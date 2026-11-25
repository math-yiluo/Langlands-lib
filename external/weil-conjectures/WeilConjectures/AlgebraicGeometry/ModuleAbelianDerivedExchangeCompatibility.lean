/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange
import WeilConjectures.CategoryTheory.RightDerivedPlusCube

/-! # Compatibility of canonical coefficient comparisons with derived exchange

Source: Stacks Project, Tag 0736 and Remark 07A7, together with Tag 03FD.
(blueprint: lem-weil-pbc-module-abelian-derived-exchange-compatibility)
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem derivedBaseChange_module_eq
    (Λ : Type (u + 1)) [CommRing Λ] {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) :
    derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq =
      Functor.rightDerivedFunctorPlusBaseChange (baseChangeMap (ModuleCat.{u + 1} Λ) sq) := by
  rfl

private theorem derivedBaseChange_abelian_eq
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) :
    derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq =
      Functor.rightDerivedFunctorPlusBaseChange (baseChangeMap AddCommGrpCat.{u + 1} sq) := by
  rfl

/-- Forgetting the source of derived exchange, using the canonical edge comparisons. -/
noncomputable def moduleAbelianDerivedExchangeSourceIso
    (Λ : Type (u + 1)) [CommRing Λ] {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D+(moduleAbelianForget Λ Y').obj
        ((R+((f)_*[ModuleCat.{u + 1} Λ]) ⋙ D+((g)^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (R+((f)_*[AddCommGrpCat.{u + 1}]) ⋙ D+((g)^*[AddCommGrpCat.{u + 1}])).obj
        (D+(moduleAbelianForget Λ X).obj K) :=
  (moduleAbelianDerivedUpperStarIso Λ g).symm.app
      (R+((f)_*[ModuleCat.{u + 1} Λ]).obj K) ≪≫
    D+((g)^*[AddCommGrpCat.{u + 1}]).mapIso
      ((moduleAbelianDerivedLowerStarIso Λ f).app K)

/-- Forgetting the target of derived exchange, using the canonical edge comparisons. -/
noncomputable def moduleAbelianDerivedExchangeTargetIso
    (Λ : Type (u + 1)) [CommRing Λ] {X X' Y' : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D+(moduleAbelianForget Λ Y').obj
        ((D+((g')^*[ModuleCat.{u + 1} Λ]) ⋙ R+((f')_*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (D+((g')^*[AddCommGrpCat.{u + 1}]) ⋙ R+((f')_*[AddCommGrpCat.{u + 1}])).obj
        (D+(moduleAbelianForget Λ X).obj K) :=
  (moduleAbelianDerivedLowerStarIso Λ f').app (D+((g')^*[ModuleCat.{u + 1} Λ]).obj K) ≪≫
    R+((f')_*[AddCommGrpCat.{u + 1}]).mapIso
      ((moduleAbelianDerivedUpperStarIso Λ g').symm.app K)

/-- Canonical coefficient comparisons intertwine the derived exchange transformations.
The maps in this equation are fixed by their units; no isomorphisms are chosen here.

Source: Stacks Project, Tag 0736 (construction and homotopy uniqueness),
Remark 07A7 (adjunction mate), and Tag 03FD (acyclic comparison).
(blueprint: lem-weil-pbc-module-abelian-derived-exchange-compatibility)

Proof: On a bounded below module complex P, precompose both sides with the
forgotten g^* image of the unit f_*P → Rf_*P. The defining factorization of the
coefficient direct-image comparison replaces the forgotten derived unit by the
abelian unit after the termwise direct-image identification. The inverse-image
comparison is the mate of the forgotten module unit; its defining adjunction
identity identifies the inverse-image units and counits. Direct-image
composition is given by evaluation on base changes, so its coefficient
identification also respects the square's commutation isomorphism. Expand the
underived exchange as unit, square isomorphism and counit. These identities show
that its forgotten version is the abelian exchange under the edge comparisons.
The two precomposed derived transformations consequently agree by the
factorization formula for derived exchange. Uniqueness of the right derived
transformation gives equality before precomposition. Equivalently, compute on
module injective resolutions: the forgotten terms are abelian f_*-acyclic by
03FD and 072W, and the comparisons to abelian injective resolutions are unique
up to homotopy; the same underived mate therefore induces both morphisms in the
localized category. This argument works for a commutative square and for any
bounded below K, and needs neither properness nor a geometric point. -/
theorem moduleAbelianDerivedExchange_compatibility
    (Λ : Type (u + 1)) [CommRing Λ]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D+(moduleAbelianForget Λ Y').map
        ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq).app K) ≫
        (moduleAbelianDerivedExchangeTargetIso Λ g' f' K).hom =
      (moduleAbelianDerivedExchangeSourceIso Λ f g K).hom ≫
        (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app
          (D+(moduleAbelianForget Λ X).obj K) := by
  have h := Functor.rightDerivedFunctorPlusBaseChange_cube
    ((f)_*[ModuleCat.{u + 1} Λ]) ((f')_*[ModuleCat.{u + 1} Λ])
    ((f)_*[AddCommGrpCat.{u + 1}]) ((f')_*[AddCommGrpCat.{u + 1}])
    ((g')^*[ModuleCat.{u + 1} Λ]) ((g)^*[ModuleCat.{u + 1} Λ])
    ((g')^*[AddCommGrpCat.{u + 1}]) ((g)^*[AddCommGrpCat.{u + 1}])
    (moduleAbelianForget Λ X) (moduleAbelianForget Λ Y)
    (moduleAbelianForget Λ X') (moduleAbelianForget Λ Y')
    (baseChangeMap (ModuleCat.{u + 1} Λ) sq) (baseChangeMap AddCommGrpCat.{u + 1} sq)
    (moduleAbelianLowerStarIso Λ f).hom (moduleAbelianLowerStarIso Λ f').hom
    (moduleAbelianUpperStarIso Λ g) (moduleAbelianUpperStarIso Λ g')
    (moduleAbelianUnderivedExchange_compatibility Λ sq) K
  simpa only [moduleAbelianDerivedExchangeSourceIso, moduleAbelianDerivedExchangeTargetIso,
    moduleAbelianDerivedLowerStarIso, moduleAbelianDerivedLowerStarComparison,
    moduleAbelianDerivedUpperStarIso, Iso.symm_hom, Iso.trans_hom, Iso.app_hom, asIso_hom,
    derivedBaseChange_module_eq, derivedBaseChange_abelian_eq,
    Functor.mapIso_hom, Category.assoc] using h

end AlgebraicGeometry.Etale
