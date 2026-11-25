/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Noetherian

/-! Local rings of etale schemes over a trait.

## References

* Stacks Project, Tags 0AP2 (15.45.4) and 0EYI, preliminary paragraph
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The canonical local ring of an etale scheme at a point over the closed point
of a trait is a DVR with the same uniformizer. -/
theorem etale_trait_stalk (R : CommRingCat.{u})
    [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec R) [Etale f] (x : X)
    (hx : f x = IsLocalRing.closedPoint R)
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ}) :
    ∃ (_ : IsDomain (X.presheaf.stalk x))
      (_ : IsDiscreteValuationRing (X.presheaf.stalk x)),
      Function.Injective (StructureSheaf.toStalk R (f x) ≫ f.stalkMap x).hom ∧
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) =
        Ideal.span {(StructureSheaf.toStalk R (f x) ≫ f.stalkMap x).hom ϖ} := by
  let S := (Spec R).presheaf.stalk (f x)
  let A := X.presheaf.stalk x
  let u : R ⟶ S := StructureSheaf.toStalk R (f x)
  have hu : IsIso u := by
    dsimp [u, S]
    rw [hx, ← stalkClosedPointIso_inv]
    infer_instance
  let e : R ≅ S := asIso u
  have : IsRegularLocalRing R := IsRegularLocalRing.of_isIntegrallyClosed R
    (IsDiscreteValuationRing.ringKrullDim_eq_one R).le
  have : IsRegularLocalRing S := .of_ringEquiv e.commRingCatIsoToRingEquiv
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let β := f.stalkMap x
  let := β.hom.toAlgebra
  have : Module.Flat S A := Flat.stalkMap f x
  have : IsLocalHom (algebraMap S A) := inferInstanceAs (IsLocalHom β.hom)
  have hmβ := FormallyUnramified.map_maximalIdeal_stalkMap f x
  have : IsRegularLocalRing A := IsRegularLocalRing.of_flat_of_map_maximalIdeal_eq hmβ
  have : IsDomain A := inferInstance
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := S) (B := A)
  have hinjβ : Function.Injective β.hom := FaithfulSMul.algebraMap_injective S A
  have hinj : Function.Injective (u ≫ β).hom :=
    hinjβ.comp (ConcreteCategory.bijective_of_isIso u).1
  have hmu : (IsLocalRing.maximalIdeal R).map u.hom = IsLocalRing.maximalIdeal S := by
    exact IsLocalRing.map_ringEquiv_maximalIdeal e.commRingCatIsoToRingEquiv
  have hm : IsLocalRing.maximalIdeal A = Ideal.span {(u ≫ β).hom ϖ} := by
    rw [← hmβ, ← hmu, Ideal.map_map, hϖ, Ideal.map_span, Set.image_singleton]
    rfl
  have hπ : ϖ ≠ 0 :=
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ).ne_zero
  have hnfield : ¬ IsField A := by
    intro hfield
    have hbot := IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
    have hz : (u ≫ β).hom ϖ = 0 := by
      simpa only [hm, Ideal.span_singleton_eq_bot] using hbot
    exact hπ (hinj (hz.trans (map_zero (u ≫ β).hom).symm))
  have hdvr : IsDiscreteValuationRing A :=
    ((IsDiscreteValuationRing.TFAE A hnfield).out 1 5).mpr
      (by rw [hm]; infer_instance)
  exact ⟨inferInstance, hdvr, hinj, hm⟩

end AlgebraicGeometry.Scheme
