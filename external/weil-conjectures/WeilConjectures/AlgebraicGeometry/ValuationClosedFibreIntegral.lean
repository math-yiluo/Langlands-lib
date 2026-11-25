/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- The integral quotient fibre over the residue field identifies with the closed fibre.
Source: Stacks Project, More on Morphisms, Tag 0EX8.
(blueprint: new-valuation-closed-fibre-integral)

Proof: The algebra map from A/m to the ideal residue field is bijective because m is
maximal. Apply Spec to its ring equivalence and base change along f. Mathlib's
comparison between the ideal residue field and the scheme residue field gives a
second base-change isomorphism. Their composite identifies the closed fibre with
the quotient pullback. Transport integrality along its inverse.
-/
theorem closed_fibre_is_integral
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (hX₀ : IsIntegral (Limits.pullback f (Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))))) :
    IsIntegral (f.fiber (IsLocalRing.closedPoint A)) := by
  let m := IsLocalRing.maximalIdeal A
  let e := (RingEquiv.ofBijective (algebraMap (A ⧸ m) m.ResidueField)
    m.bijective_algebraMap_quotient_residueField).toCommRingCatIso
  have he : Spec.map e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)) =
      Spec.map (CommRingCat.ofHom (algebraMap A m.ResidueField)) := by
    rw [← Spec.map_comp]
    rfl
  let i := asIso (pullback.map f
    (Spec.map (CommRingCat.ofHom (algebraMap A m.ResidueField))) f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)))
    (𝟙 X) (Spec.map e.hom) (𝟙 _) (by simp) (by simpa using he.symm))
  let j := asIso (pullback.map f
    ((Spec (CommRingCat.of A)).fromSpecResidueField (IsLocalRing.closedPoint A)) f
    (Spec.map (CommRingCat.ofHom (algebraMap A m.ResidueField)))
    (𝟙 X) (Spec.map (Scheme.Spec.residueFieldIso
      (CommRingCat.of A) (IsLocalRing.closedPoint A)).inv) (𝟙 _) (by simp)
    (by simpa only [Category.comp_id, IsLocalRing.closedPoint, m] using
      (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField
        (CommRingCat.of A) (IsLocalRing.closedPoint A)).symm))
  exact IsIntegral.of_isIso (j ≪≫ i).inv

end AlgebraicGeometry.Scheme.Modules
