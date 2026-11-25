/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMap
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarSourceFactors
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientSquare

/-! # Abelian raw pullback factorization
Source: Stacks Project, Tags 03FD and 03Q8.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true in
/-- The abelian raw map factors independently of any module cohomology class.
Source: Stacks Project, Tags 03FD and 03Q8, explicit-map expansion in the proof of
lem-sbc-raw-module-abelian-hom-map-naturality.
(blueprint: lem-sbc-raw-scalar-pullback-abelian-formula).

Proof: Fix x and unfold abelianHigherDirectImageRawPullback. Its source free abelian
sheaf is RawModuleScalarComparison.freeAbelian S U, since evaluation of whiskering
by AddCommGrpCat.free is composition with that functor. Its first two maps are the
single of the composite inverse-image comparison and the inverse derived-single
comparison, which are abelianSourceFactor. Its middle map is derived inverse image
of x. Its last two maps are the shift comparison and the shift of the single
comparison followed by the single of the inverse coefficient upperStarComp. Expand
restrictedOverCoefficient to identify these last maps with abelianCoefficientFactor.
Apply Category.assoc to the first two maps. The Over triangle proofs coincide by
proof irrelevance. No module class z, scalar comparison, or inverse-image coherence
square is used. The same calculation covers degree zero, zero x, and identity f. -/
theorem rawModuleScalar_pullback_abelian_formula
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B) :
    ∀ (x : (abelianHigherDirectImageRawPresheaf (B.hom ≫ k) q
      (restrictedOverCoefficient ((moduleAbelianForget Λ W).obj G) B)).obj
        (op U)),
      abelianHigherDirectImageRawPullback f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) q _ _
        ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
          (Over.w f).symm).inv.app ((moduleAbelianForget Λ W).obj G)) U x =
      abelianSourceFactor f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) (RawModuleScalarComparison.freeAbelian S U) ≫
      (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.map x ≫
      abelianCoefficientFactor ((moduleAbelianForget Λ W).obj G)
        (q : ℤ) A B f := by
  intro x
  exact (Category.assoc _ _ _).symm

end AlgebraicGeometry.Etale
