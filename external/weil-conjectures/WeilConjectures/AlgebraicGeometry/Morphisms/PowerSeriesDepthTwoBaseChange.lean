/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.RingTheory.Depth
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import WeilConjectures.RingTheory.FlatLocalDepthFormula
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoFiniteExtensionUniqueness
import WeilConjectures.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedFiniteModel
/-!
# Descent of the finite depth-two power-series extension as a finite scheme

## References

* Stacks Project, Tag 0EYA, identification C = C0 tensor B
* Tags 0EY9 and 0EY6
* Stacks Project, Tag 0EYA, construction of the isomorphism Psi
* Stacks Project, Tag 0EY6 (2)(a), (2)(b)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private theorem depth_le_of_flat_stalk {X S : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian S]
    (f : X ⟶ S) (x : X) (hf : (f.stalkMap x).hom.Flat) :
    IsLocalRing.depth (R := S.presheaf.stalk (f x)) (S.presheaf.stalk (f x)) ≤
      IsLocalRing.depth (R := X.presheaf.stalk x) (X.presheaf.stalk x) := by
  obtain ⟨_, hlocal, _, hd⟩ :=
    IsLocalRing.depth_eq_add_of_flat_local (f.stalkMap x).hom hf
  rw [hd]
  exact le_self_add

private theorem depth_at_closed_point
    (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := B) B) :
    (2 : ℕ∞) ≤ IsLocalRing.depth
      (R := (Spec (.of B)).presheaf.stalk (IsLocalRing.closedPoint B))
      ((Spec (.of B)).presheaf.stalk (IsLocalRing.closedPoint B)) := by
  let e : B ≃+* (Spec (.of B)).presheaf.stalk (IsLocalRing.closedPoint B) :=
    (IsLocalization.atUnits B (IsLocalRing.maximalIdeal B).primeCompl
      (S := Localization.AtPrime (IsLocalRing.maximalIdeal B)) (by
        intro x hx
        change IsUnit x
        simpa only [Ideal.mem_primeCompl_iff, IsLocalRing.mem_maximalIdeal,
          mem_nonunits_iff, not_not] using hx)).toRingEquiv.trans
      (StructureSheaf.stalkIso B (IsLocalRing.closedPoint B)).toRingEquiv
  let : IsLocalHom e.toRingHom := IsLocalHom.of_surjective _ e.surjective
  obtain ⟨_, hlocal, _, hd⟩ := IsLocalRing.depth_eq_add_of_flat_local
    e.toRingHom (RingHom.Flat.of_bijective e.bijective)
  rw [hd]
  exact hdepth.trans le_self_add

/-- A finite depth-two extension on a proper power-series open comes by base change
from a finite scheme over the coefficient ring. No etaleness of that scheme is asserted. -/
theorem exists_finite_base_of_power_series_depth_two
    (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := B) B)
    (n : ℕ) (hn : 0 < n)
    (V : (Spec (.of (MvPowerSeries (Fin n) B))).Opens) (hproper : V ≠ ⊤)
    (haway : ∀ v, (Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin n)))) v ≠
      IsLocalRing.closedPoint B → v ∈ V)
    {E : Scheme.{u}} (p : E ⟶ Spec (.of (MvPowerSeries (Fin n) B)))
    [IsFinite p] [Etale (p ∣_ V)]
    (hboundary : ∀ z : E, p z ∉ V →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z)) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of B)) (a : E ⟶ Y),
      IsFinite g ∧ IsPullback a p g
        (Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin n)))) := by
  let t := Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin n) (R := B)))
  have : Module.Flat (MvPolynomial (Fin n) B) (MvPowerSeries (Fin n) B) :=
    Module.Flat.of_linearEquiv (MvPowerSeries.toAdicCompletionAlgEquiv (Fin n) B).toLinearEquiv
  have : Module.Flat B (MvPowerSeries (Fin n) B) :=
    Module.Flat.trans B (MvPolynomial (Fin n) B) (MvPowerSeries (Fin n) B)
  have : Flat t := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr this)
  let U : (Spec (.of B)).Opens :=
    ⟨{IsLocalRing.closedPoint B}ᶜ, (IsLocalRing.isClosed_singleton_closedPoint B).isOpen_compl⟩
  have hU : ∀ x, x ∈ U ↔ x ≠ IsLocalRing.closedPoint B := fun _ ↦ Iff.rfl
  let W := t ⁻¹ᵁ U
  obtain ⟨Y, g, hg, hY, e, he⟩ :=
    exists_power_series_punctured_finite_model B hdepth n hn V hproper haway p U hU
  have : IsFinite g := hg
  let r := Limits.pullback.snd g t
  have : IsLocallyNoetherian E := LocallyOfFiniteType.isLocallyNoetherian p
  have hE : ∀ z : E, p z ∉ W →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z) := by
    intro z hz
    by_cases hzV : p z ∈ V
    · have hflat : (p.stalkMap z).hom.Flat :=
        (RingHom.Flat.respectsIso.arrow_mk_iso_iff
          (morphismRestrictStalkMap p V ⟨z, hzV⟩)).mp (Flat.stalkMap (p ∣_ V) ⟨z, hzV⟩)
      have hclosed : t (p z) = IsLocalRing.closedPoint B := by
        by_contra hne
        exact hz ((hU _).mpr hne)
      have hbase := depth_at_closed_point B hdepth
      rw [← hclosed] at hbase
      exact (hbase.trans (depth_le_of_flat_stalk t (p z) (Flat.stalkMap t _))).trans
        (depth_le_of_flat_stalk p z hflat)
    · exact hboundary z hzV
  have hF : ∀ w : ↥(Limits.pullback g t), r w ∉ W →
      (2 : ℕ∞) ≤ IsLocalRing.depth
        (R := (Limits.pullback g t).presheaf.stalk w)
        ((Limits.pullback g t).presheaf.stalk w) := by
    intro w hw
    have hw' : g ((Limits.pullback.fst g t) w) ∉ U := by
      change t (r w) ∉ U at hw
      rwa [← Hom.comp_apply, ← Limits.pullback.condition, Hom.comp_apply] at hw
    have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
    exact (hY _ hw').trans
      (depth_le_of_flat_stalk (Limits.pullback.fst g t) w (Flat.stalkMap _ _))
  obtain ⟨i, hi⟩ := iso_of_finite_depth_two_extensions W r p hF hE e he
  refine ⟨Y, g, i.inv ≫ Limits.pullback.fst g t, hg, ?_⟩
  exact (IsPullback.of_hasPullback g t).of_iso i (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simpa using hi.symm) (by simp) (by simp [t])

end AlgebraicGeometry.Scheme
