/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroUnitIsIso
import WeilConjectures.Algebra.Homology.DerivedOpenShriekAdjunction
import Mathlib.CategoryTheory.Monad.Adjunction

/-! # Invertibility of the transported derived open extension unit
Source: Stacks Project, Tags 00A7, 08BS and 06YB.
(blueprint: lem-pc-open-extension-derived-unit-isiso). -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
  TopologicalSpace
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

noncomputable section
universe u w

local instance standardDerivedOpenExtensionDerivedUnitIsIso (X : Scheme.{u}) (U : X.Opens) :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
  HasDerivedCategory.standard _

/-- The unit of any left adjoint to transported derived open restriction is invertible.
Source: Stacks Project, Sheaves Tag 00A7 (4), Modules on Sites Tag 03DI,
and Cohomology Tags 08BS and 08BT.
Proof: take the canonical ordinary extension-by-zero adjunction, whose unit is
invertible by the one-summand calculation on opens contained in U. Derive that
exact adjunction using derived_open_shriek_adjunction. The exact derived functors
respect composition and natural isomorphisms, so the ordinary unit gives an
isomorphism G-derived followed by restriction-derived with the identity.
Mathlib's fullyFaithfulLOfCompIsoId then makes G-derived fully faithful. Compose
it with the inverse derived over-site equivalence to obtain a fully faithful J₀
left adjoint to the prescribed R. Its unit is invertible. The left-adjoint
uniqueness isomorphism from J₀ to any J identifies the two units, so invertibility
passes to the unit of the supplied adjunction. Empty and total opens are already
covered by the ordinary unit theorem; the derived construction uses precisely the
specified localization universes and the standard localization on U.toScheme.
(blueprint: lem-pc-open-extension-derived-unit-isiso). -/
theorem openExtension_derived_unit_isIso (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    let E := (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory ⋙ E
    ∀ (J : schemeDerivedCategory U.toScheme ⥤ schemeDerivedCategory X)
      (adj : J ⊣ R) (A : schemeDerivedCategory U.toScheme), IsIso (adj.unit.app A) := by
  dsimp
  intro J adj A
  let G := SheafOfModules.extensionByZeroPresheaf.{u}
    (moduleRings X.toRingedSpace) U ⋙
      PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X.toRingedSpace).obj)
  let F := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let a : G ⊣ F := Classical.choice
    (open_restriction_adjunction_exact X.toRingedSpace U).2.2.2.2
  have : G.Additive := a.left_adjoint_additive
  have : PreservesFiniteLimits G :=
    (open_restriction_adjunction_exact X.toRingedSpace U).2.2.1
  have : PreservesFiniteColimits G :=
    (open_restriction_adjunction_exact X.toRingedSpace U).2.2.2.1
  have (M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :
      IsIso (a.unit.app M) := moduleExtensionByZero_unit_isIso X.toRingedSpace U M
  have : IsIso a.unit := NatIso.isIso_of_isIso_app a.unit
  let b : G.mapDerivedCategory ⊣ F.mapDerivedCategory :=
    Classical.choice (derived_open_shriek_adjunction X.toRingedSpace U)
  let e : G.mapDerivedCategory ⋙ F.mapDerivedCategory ≅ 𝟭 _ :=
    (Functor.mapDerivedCategoryCompIso G F) ≪≫
      Functor.mapDerivedCategoryNatIso (asIso a.unit).symm ≪≫
        Functor.mapDerivedCategoryIdIso _
  have hG := b.fullyFaithfulLOfCompIsoId e
  have := hG.full
  have := hG.faithful
  let eU : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ≌
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) := Scheme.Modules.overEquiv U
  let E := eU.mapDerivedCategory
  let J₀ := E.inverse ⋙ G.mapDerivedCategory
  let b₀ : J₀ ⊣ F.mapDerivedCategory ⋙ E.functor := E.symm.toAdjunction.comp b
  have : J₀.Full := inferInstance
  have : J₀.Faithful := inferInstance
  have : IsIso (b₀.unit.app A) := inferInstance
  have h := b₀.unit_leftAdjointUniq_hom_app adj A
  exact h ▸ (inferInstance : IsIso
    (b₀.unit.app A ≫ (F.mapDerivedCategory ⋙ E.functor).map
      ((b₀.leftAdjointUniq adj).hom.app A)))

end
end AlgebraicGeometry
