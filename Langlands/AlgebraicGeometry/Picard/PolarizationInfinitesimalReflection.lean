import Langlands.AbelianScheme.FiberwiseIsogeny
import Langlands.AbelianScheme.PolarizedFiniteLevel.PullbackCoherence
import Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizationIsoTransport

/-! # Reflecting relative polarizations from a square-zero base reduction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard

variable (P : Prerequisites.{u}) {S T : Scheme.{u}}
  (b : T ⟶ S) {A : AbelianScheme S} (W : DualWitness A)
  (V : DualWitness ((baseChange b).obj A)) (lam : A ⟶ W.dual P)

/-- A relative polarization descends as a property of a supplied homomorphism
when every field-valued point of the base factors through the testing map. -/
theorem DualWitness.isPolarization_of_field_point_factorization
    (hb : ∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S),
      ∃ t : Spec (CommRingCat.of K) ⟶ T, t ≫ b = s)
    (h : V.IsPolarization P (W.pullbackMap P b V lam)) : W.IsPolarization P lam := by
  have hisog (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S) :
      IsIsogeny ((baseChange s).map lam) := by
    obtain ⟨t, rfl⟩ := hb K s
    let Vt := V.pullback P t
    let Wt := W.pullback P (t ≫ b)
    have ht : IsIsogeny (V.pullbackMap P t Vt (W.pullbackMap P b V lam)) :=
      (h.1.baseChange t).comp (isIsogeny_of_iso (V.baseChangeIso P t Vt))
    have hd : IsIsogeny (W.pullbackMap P (t ≫ b) Wt lam) := by
      rw [W.pullbackMap_comp P b t V Wt Vt]
      exact (isIsogeny_of_iso (baseChangeCompIso b t A)).comp
        (ht.comp (isIsogeny_of_iso (Wt.mapIso P Vt (baseChangeCompIso b t A))))
    have hc := hd.comp (isIsogeny_of_iso (W.baseChangeIso P (t ≫ b) Wt).symm)
    simpa only [DualWitness.pullbackMap, Category.assoc, Iso.symm_hom, Iso.hom_inv_id,
      Category.comp_id] using hc
  refine ⟨Langlands.GroupScheme.fiberwiseIsogeny S A.toGrp (W.dual P).toGrp
    A.smooth (W.dual P).smooth A.proper (W.dual P).proper (groupHom lam)
    (fun s => hisog (S.residueField s) (S.fromSpecResidueField s)), ?_⟩
  intro K _ _ s
  obtain ⟨t, rfl⟩ := hb K s
  let Vt := V.pullback P t
  let Wt := W.pullback P (t ≫ b)
  have hfield : HasFieldAmpleMumfordPresentation P.preservation P.square P.universality K
    ((baseChange t).obj ((baseChange b).obj A)) Vt.hasDual
    (Vt.parameterMap P (V.pullbackMap P t Vt (W.pullbackMap P b V lam))) := by
    rw [V.parameterMap_pullbackMap]
    exact h.2 K t
  change HasFieldAmpleMumfordPresentation P.preservation P.square P.universality K
    ((baseChange (t ≫ b)).obj A) Wt.hasDual
    (dualBaseChangeMap A W.hasDual P.universality (t ≫ b) (W.parameterMap P lam))
  rw [← W.parameterMap_pullbackMap P (t ≫ b) Wt lam, W.pullbackMap_comp P b t V Wt Vt]
  exact hasFieldAmpleMumfordPresentation_iso P.preservation P.square P.universality P.stability K
    (baseChangeCompIso b t A) Wt.hasDual Vt.hasDual _ hfield

private theorem field_point_factors_squareZero {R' R K : Type u}
    [CommRing R'] [CommRing R] [Field K] (φ : R' →+* R) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ * RingHom.ker φ = ⊥)
    (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R')) :
    ∃ t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R),
      t ≫ Spec.map (CommRingCat.ofHom φ) = s := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective s
  have ha : RingHom.ker φ ≤ RingHom.ker a.hom := by
    intro x hx
    have hxx := Ideal.mul_mem_mul hx hx
    rw [hker, Ideal.mem_bot] at hxx
    have h := congrArg a.hom hxx
    rw [map_mul, map_zero, mul_self_eq_zero] at h
    exact h
  let t := φ.liftOfSurjective hφ ⟨a.hom, ha⟩
  refine ⟨Spec.map (CommRingCat.ofHom t), ?_⟩
  rw [← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (φ.liftOfSurjective_comp hφ ⟨a.hom, ha⟩))

/-- A surjective ring map with square-zero kernel gives a surjective map of spectra. -/
theorem specMap_surjective_of_squareZero_ker {R' R : Type u} [CommRing R'] [CommRing R]
    (φ : R' →+* R) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ * RingHom.ker φ = ⊥) :
    Surjective (Spec.map (CommRingCat.ofHom φ)) := by
  let S := Spec (CommRingCat.of R')
  refine ⟨fun x => ?_⟩
  obtain ⟨t, ht⟩ := field_point_factors_squareZero φ hφ hker (S.fromSpecResidueField x)
  let y := IsLocalRing.closedPoint (S.residueField x)
  refine ⟨t y, ?_⟩
  rw [← Scheme.Hom.comp_apply, ht]
  exact Scheme.fromSpecResidueField_apply x y

/-- If a supplied dual-valued homomorphism reduces to a polarization across a
surjective map with square-zero kernel, it is itself a polarization. -/
theorem DualWitness.isPolarization_of_squareZero_reduction
    {R' R : Type u} [CommRing R'] [CommRing R] (φ : R' →+* R) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ * RingHom.ker φ = ⊥)
    {B : AbelianScheme (Spec (CommRingCat.of R'))} (W : DualWitness B)
    (V : DualWitness ((baseChange (Spec.map (CommRingCat.ofHom φ))).obj B))
    (lam : B ⟶ W.dual P)
    (h : V.IsPolarization P (W.pullbackMap P (Spec.map (CommRingCat.ofHom φ)) V lam)) :
    W.IsPolarization P lam :=
  W.isPolarization_of_field_point_factorization P (Spec.map (CommRingCat.ofHom φ)) V lam
    (fun _ _ s => field_point_factors_squareZero φ hφ hker s) h

end Langlands.AbelianScheme.PolarizedFiniteLevel
