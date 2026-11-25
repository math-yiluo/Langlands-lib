/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # The canonical homology comparison for associated sheaves over a field

## References

* Stacks Project, Tag 01XK
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v
open CategoryTheory
namespace AlgebraicGeometry.Scheme

-- The scalar and sheaf homology structures require several comparison instances.
/-- Associated sheaves followed by derived homology and field sections compute
module-complex homology naturally.

Construction: Global sections on the spectrum of a field are an exact equivalence.
Commute them with homology and apply the tilde/sections unit isomorphism termwise.
The derived localization homology comparison supplies the first factor. -/
noncomputable def residueTildeHomologyComparison (k : CommRingCat.{v}) (hk : IsField k)
    [HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} (moduleRings (Spec k).toRingedSpace))] (i : ℤ) :
    let B := SheafOfModules.{v} (moduleRings (Spec k).toRingedSpace)
    let L : ModuleCat.{v} k ⥤ B := tilde.functor k
    letI : L.Additive := ⟨by intros; exact tilde.map_add _ _⟩
    L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙
        DerivedCategory.homologyFunctor B i ⋙ moduleSpecΓFunctor (R := k) ≅
      HomologicalComplex.homologyFunctor (ModuleCat.{v} k) (.up ℤ) i := by
  dsimp only
  let B := SheafOfModules.{v} (moduleRings (Spec k).toRingedSpace)
  let L : ModuleCat.{v} k ⥤ B := tilde.functor k
  have : L.Additive := ⟨by intros; exact tilde.map_add _ _⟩
  let Γ : B ⥤ ModuleCat.{v} k := moduleSpecΓFunctor (R := k)
  have : Γ.IsEquivalence := isEquivalence_moduleSpecΓFunctor hk
  have : Γ.Additive := Functor.additive_of_preserves_binary_products _
  have : Γ.PreservesHomology := inferInstance
  let θ : L.mapHomologicalComplex (.up ℤ) ⋙ Γ.mapHomologicalComplex (.up ℤ) ≅
      𝟭 (CochainComplex (ModuleCat.{v} k) ℤ) :=
    Functor.mapHomologicalComplexCompIso
      (tilde.toTildeΓNatIso (R := k)).symm (.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso (ModuleCat.{v} k) (.up ℤ)
  exact Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (L.mapHomologicalComplex (.up ℤ))
        (DerivedCategory.homologyFunctorFactors B i)) Γ ≪≫
    Functor.isoWhiskerLeft (L.mapHomologicalComplex (.up ℤ))
      (Γ.mapHomologicalComplexHomologyIso (.up ℤ) i).symm ≪≫
    Functor.isoWhiskerRight θ
      (HomologicalComplex.homologyFunctor (ModuleCat.{v} k) (.up ℤ) i)

attribute [irreducible] residueTildeHomologyComparison

end AlgebraicGeometry.Scheme
