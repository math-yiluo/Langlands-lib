/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison

/-!
# Forgetting coefficients in higher direct images

Source: Stacks Project, Tags 03FD and 072W.
(blueprint: lem-sbc-higher-direct-image-forget-comparison)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Forgetting the module structure commutes with higher direct images of a sheaf
placed in degree zero, in every integer degree.

Source: Stacks Project, Tag 03FD (cohomology of modules agrees with abelian
cohomology), and Tag 072W (higher direct images as sheafified cohomology presheaves).
(blueprint: lemma-cohomology-modules-underlying-abelian)

Proof: Use the canonical bounded-below derived coefficient comparison
`moduleAbelianDerivedLowerStarIso` from
lemma-cohomology-modules-underlying-abelian. Its invertibility is
already proved using the all-object acyclicity argument of Tags 03FD and 072W.
Apply this isomorphism to F placed in degree zero. The exact forgetful functor
commutes with degree-q homology by `mapDerivedCategoryPlusHomologyFunctorIso`,
and with the degree-zero single functor by `mapDerivedCategoryPlusSingleFunctor`.
Compose these three isomorphisms. They hold for every integer q, so no separate
argument for degree zero or negative degrees is necessary. No flatness or
nonzero-ring hypothesis is required. -/
theorem nonempty_higherDirectImage_forget_iso
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (h : Y ⟶ X)
    (q : ℤ) (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nonempty
      ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          (higherDirectImage Λ h q F) ≅
        (DerivedCategory.Plus.homologyFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
              ((sheafCompose Y.smallEtaleTopology
                (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)))) := by
  let S := moduleAbelianForget Λ Y
  let T := moduleAbelianForget Λ X
  let GA := lowerStar AddCommGrpCat.{u + 1} h
  let GM := lowerStar (ModuleCat.{u + 1} Λ) h
  let K := (DerivedCategory.Plus.singleFunctor
    (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj F
  exact ⟨(T.mapDerivedCategoryPlusHomologyFunctorIso q).app
      (GM.rightDerivedFunctorPlus.obj K) ≪≫
    (DerivedCategory.Plus.homologyFunctor
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q).mapIso
      ((moduleAbelianDerivedLowerStarIso Λ h).app K ≪≫
        GA.rightDerivedFunctorPlus.mapIso ((S.mapDerivedCategoryPlusSingleFunctor 0).app F))⟩

end AlgebraicGeometry.Etale
