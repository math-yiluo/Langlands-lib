/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.Etale
import WeilConjectures.RingTheory.FiniteFreeLocalFieldFactorization

/-!
# Finite flat rationalization of a smooth closed-fibre point

## References

* Stacks Project, Tag 0EYB, the residue extension base change
* Tag 07NE
* Stacks Project, Tag 0EYB, the first base change
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

private theorem residueFieldMap_surjective_of_surjectiveOnStalks
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) :
    Function.Surjective (f.residueFieldMap x).hom := by
  intro a
  obtain ⟨b, hb⟩ := X.residue_surjective x a
  obtain ⟨c, hc⟩ := f.stalkMap_surjective x b
  refine ⟨Y.residue (f x) c, ?_⟩
  have h := congrArg (fun g ↦ g.hom c) (residue_residueFieldMap f x)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, hc, hb] using h

/-- A finite flat local base change makes the prescribed closed-fibre point separable. -/
theorem exists_smooth_closed_point_finite_flat_lift
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {L : Scheme.{u}} (q : L ⟶ Spec (.of A)) [Smooth q]
    (x : q.fiber (IsLocalRing.closedPoint A)) (hx : IsClosed ({x} : Set _)) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : IsLocalRing A') (_ : IsNoetherianRing A'),
      ∃ (α : A →+* A'), IsLocalHom α ∧ α.Flat ∧
        IsFinite (Spec.map (CommRingCat.ofHom α)) ∧
        ∃ y : (pullback q (Spec.map (CommRingCat.ofHom α)) : Scheme.{u}),
          pullback.fst q (Spec.map (CommRingCat.ofHom α)) y =
            q.fiberι (IsLocalRing.closedPoint A) x ∧
          pullback.snd q (Spec.map (CommRingCat.ofHom α)) y =
            IsLocalRing.closedPoint A' ∧
          ((pullback.snd q (Spec.map (CommRingCat.ofHom α))).residueFieldMap y).hom.Etale
    := by
  let F := q.fiber (IsLocalRing.closedPoint A)
  let p := F.fromSpecResidueField x
  let t := p ≫ q.fiberToSpecResidueField (IsLocalRing.closedPoint A)
  have : IsClosedImmersion p := isClosed_singleton_iff_isClosedImmersion.mp hx
  have : LocallyOfFiniteType (q.fiberToSpecResidueField (IsLocalRing.closedPoint A)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : LocallyOfFiniteType t := inferInstance
  have : IsFinite t := isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  have : IsClosedImmersion ((Spec (.of A)).fromSpecResidueField
      (IsLocalRing.closedPoint A)) :=
    isClosed_singleton_iff_isClosedImmersion.mp
      (IsLocalRing.isClosed_singleton_closedPoint A)
  let r := p ≫ q.fiberι (IsLocalRing.closedPoint A) ≫ q
  have hr : r = t ≫ (Spec (.of A)).fromSpecResidueField (IsLocalRing.closedPoint A) := by
    simp only [r, t, Category.assoc, q.fiber_fac]
  have : IsFinite r := by rw [hr]; infer_instance
  obtain ⟨rho, hrho⟩ := Spec.map_surjective r
  have hfinite : rho.hom.Finite := (IsFinite.SpecMap_iff _).mp (hrho ▸ ‹IsFinite r›)
  have hker : RingHom.ker rho.hom = IsLocalRing.maximalIdeal A := by
    have hpoint : Spec.map rho (IsLocalRing.closedPoint (F.residueField x)) =
        IsLocalRing.closedPoint A := by
      rw [hrho, hr]
      simp only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    have h := congrArg PrimeSpectrum.asIdeal hpoint
    change (IsLocalRing.maximalIdeal (F.residueField x)).comap rho.hom =
      IsLocalRing.maximalIdeal A at h
    rw [RingHom.ker_eq_comap_bot]
    simpa only [IsLocalRing.maximalIdeal_eq_bot] using h
  obtain ⟨B, hB, hlocal, hAlg, hfree, hfin, halpha, beta, hbeta, hcomp⟩ :=
    IsLocalRing.exists_finite_free_local_field_factorization A (F.residueField x)
      rho.hom hfinite hker
  let := hB
  let := hlocal
  let := hAlg
  let := hfree
  let := hfin
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  refine ⟨B, inferInstance, inferInstance, inferInstance, algebraMap A B, halpha,
    RingHom.flat_algebraMap_iff.mpr inferInstance,
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hfin), ?_⟩
  have : IsLocalHom beta := IsLocalHom.of_surjective beta hbeta
  let alpha := algebraMap A B
  let g := Spec.map (CommRingCat.ofHom alpha)
  let b := Spec.map (CommRingCat.ofHom beta)
  have hb : IsClosedImmersion b := IsClosedImmersion.spec_of_surjective _ hbeta
  have hcompat : (p ≫ q.fiberι (IsLocalRing.closedPoint A)) ≫ q = b ≫ g := by
    rw [← Spec.map_comp]
    change r = Spec.map (CommRingCat.ofHom (beta.comp alpha))
    rw [hcomp]
    exact hrho.symm
  let lift := pullback.lift (p ≫ q.fiberι (IsLocalRing.closedPoint A)) b hcompat
  let c := IsLocalRing.closedPoint (F.residueField x)
  let y := lift c
  refine ⟨y, ?_, ?_, ?_⟩
  · change (lift ≫ pullback.fst q g) c = _
    rw [pullback.lift_fst]
    simp only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply, p]
    rfl
  · change (lift ≫ pullback.snd q g) c = _
    rw [pullback.lift_snd]
    exact IsLocalRing.comap_closedPoint beta
  · apply RingHom.Etale.of_bijective
    refine ⟨((pullback.snd q g).residueFieldMap y).hom.injective, ?_⟩
    have hs : Function.Surjective ((lift ≫ pullback.snd q g).residueFieldMap c).hom := by
      rw [pullback.lift_snd]
      exact residueFieldMap_surjective_of_surjectiveOnStalks b c
    rw [residueFieldMap_comp] at hs
    intro a
    obtain ⟨d, hd⟩ := hs ((lift.residueFieldMap c).hom a)
    refine ⟨d, (lift.residueFieldMap c).hom.injective ?_⟩
    exact hd

end AlgebraicGeometry.Scheme
