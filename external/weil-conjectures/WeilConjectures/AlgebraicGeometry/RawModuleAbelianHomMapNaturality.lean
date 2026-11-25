/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMap
import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomSourceFormula
import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomTargetFormula

/-! # Naturality of the fixed raw scalar comparison

Source: Stacks Project, Tags 03FD, 03Q8 and 03D7.
(blueprint: lem-sbc-raw-module-abelian-hom-map-naturality).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true in
/-- The concrete scalar comparison commutes with the five-factor raw pullback.
Source: Stacks Project, Tags 03FD and 03Q8, with the inverse-image adjunction of 03D7.
(blueprint: lem-sbc-raw-module-abelian-hom-map-naturality).

Proof: Expand rawModuleAbelianHomMap and both raw pullbacks. The Kan-extension and
sheafification comparisons commute with their units. Under the inverse-image
adjunction their inverse therefore corresponds to the underlying module unit.
Naturality of this unit and the adjunction triangle identity show that its
composition comparison
commutes with upperStarComp. The same calculation applied to freeMap moves
the source generator comparison across the first pullback factor. The single
comparison commutes with scalar forgetting by naturality of
mapDerivedCategoryPlusSingleFunctor. Functoriality of derived forgetting moves
the class itself through the third factor. Compatibility of its commShiftIso
with the single comparison identifies the fourth factor. Finally the mate
composition equation identifies the inverse coefficient comparison with the
abelian upperStarComp inverse in the fifth factor. Associativity gives the
stated equality. No invertibility of the raw Hom map is needed in this argument;
in particular this is independent of the acyclicity argument of Tag 03FD.
The computation also applies to identity arrows, degree zero and empty objects. -/
theorem rawModuleAbelianHomMap_naturality
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale) :
    ∀ (A B : Over W) (f : A ⟶ B)
        (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)),
        rawModuleAbelianHomMap Λ k G q U A
          ((higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op z) =
          abelianHigherDirectImageRawPullback f.left (B.hom ≫ k) (A.hom ≫ k)
            (by rw [← Category.assoc, Over.w]) q
            (restrictedOverCoefficient
              ((sheafCompose _
                (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) B)
            (restrictedOverCoefficient
              ((sheafCompose _
                (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) A)
            ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
              (Over.w f).symm).inv.app
                ((sheafCompose _
                  (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G))
            U (rawModuleAbelianHomMap Λ k G q U B z) := by
  intro A B f z
  have hs := rawModuleAbelianHomMap_source_formula Λ k G q U A B f z
  have ht := rawModuleAbelianHomMap_target_formula Λ k G q U A B f z
  have hc := rawModuleScalar_coefficient_square Λ G (q : ℤ) A B f
  exact hs.trans
    ((congrArg (fun t ↦ rawModuleScalarSourcePrefix Λ k G q U A B f z ≫ t) hc).trans ht.symm)

end AlgebraicGeometry.Etale
