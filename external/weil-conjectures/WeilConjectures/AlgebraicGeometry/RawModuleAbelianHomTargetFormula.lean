/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMap
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarSourcePrefix
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientSquare
import WeilConjectures.AlgebraicGeometry.RawModuleScalarPullbackAbelianFormula
import WeilConjectures.AlgebraicGeometry.RawModuleScalarHomEvaluation

/-! # Abelian expansion of the scalar raw Hom map

Source: Stacks Project, Tags 03D7 and 03Q8.
(blueprint: lem-sbc-raw-module-abelian-hom-target-formula).
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Expand the abelian raw pullback and only the source-side scalar map.
Source: Stacks Project, Tags 03FD and 03Q8, explicit pullback factor expansion.
(blueprint: lem-sbc-raw-module-abelian-hom-target-formula).

Proof: Apply rawModuleScalar_pullback_abelian_formula to the input
rawModuleAbelianHomMap evaluated on z. Expand the additive scalar map as derived forgetting
followed by right composition with scalarCoefficientFactor and left composition with
scalarSourceFactor. Apply Functor.map_comp to separate the scalar coefficient factor from
the source factor and the forgotten class. Reassociate the morphisms: the leading abelian
source comparison and the image of the source factor composed with the class are exactly
rawModuleScalarSourcePrefix; the final two morphisms are the image of the scalar coefficient
factor and abelianCoefficientFactor. This argument uses only the definitions, functoriality
and associativity. It uses neither the source coherence square nor the coefficient coherence
square, and assumes no invertibility of the scalar Hom map. Zero and identity morphisms,
empty test objects and q = 0 satisfy the same formula. -/
theorem rawModuleAbelianHomMap_target_formula
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :
    abelianHigherDirectImageRawPullback f.left (B.hom ≫ k) (A.hom ≫ k)
      (by rw [← Category.assoc, Over.w]) q _ _
      ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
        (Over.w f).symm).inv.app ((moduleAbelianForget Λ W).obj G))
      U (rawModuleAbelianHomMap Λ k G q U B z) =
    rawModuleScalarSourcePrefix Λ k G q U A B f z ≫
      ((upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.map
          (scalarCoefficientFactor Λ B.hom G (q : ℤ)) ≫
        abelianCoefficientFactor ((moduleAbelianForget Λ W).obj G)
          (q : ℤ) A B f) := by
  refine (rawModuleScalar_pullback_abelian_formula Λ k G q U A B f _).trans ?_
  rw [rawModuleScalarHom_evaluate]
  dsimp only [rawModuleScalarSourcePrefix]
  simp only [Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Etale
