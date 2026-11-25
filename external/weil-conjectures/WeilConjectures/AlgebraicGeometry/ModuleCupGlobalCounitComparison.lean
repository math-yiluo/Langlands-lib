/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Global ringed-space pullback comparisons

The ringed-space map throughout is `toGlobalSectionsPoint X`, with target
`globalSectionsPoint X`, not a morphism of schemes. Modules on this point are
identified with Γ(X,O_X)-modules by evaluation. No condition on X is imposed.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable (X : Scheme.{u})
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

local instance globalCounitCommRing :
    CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing (X.presheaf.obj (op ⊤)))
/-- The global ringed-space counit comparison square. P is the ordinary
pullback of the preceding global tensor theorem (the statement holds for any
adjunction to Γ); α is its left-derived comparison. The derived adjunction here
is induced from the ordinary adjunction and the canonical right-derived unit,
so an unrelated adjunction with the same functors cannot be substituted.
The derived-functor instances under postcomposition express absoluteness; for
p they follow from K-flat and K-injective resolutions, respectively.
Source: Stacks, Tag 0FP1, Lemma 20.28.6.
(blueprint: lem-sc-module-cup-global-counit-comparison)
Proof: resolve K by a K-injective I and resolve Γ(I) by a K-flat Q. Choose a
K-flat P0 resolving Γ(K) and a map P0 → Q so the square with Γ(K) → Γ(I)
commutes in the homotopy category, using common refinements of roofs. Apply
ordinary pullback to that square and then the ordinary evaluation counit.
Naturality of evaluation gives a commutative outer rectangle from p*P0 to I.
The left edge computes Lp*(Γ(K) → RΓ(K)), the bottom edge is the induced
derived counit, and the upper/right path is the comparison Lp* → p* followed
by ordinary evaluation. Localizing the outer rectangle proves the equation.
In Lean, the induced derived counit is constructed as a right-derived descent;
its factorization equation is exactly this square, so the existing
Adjunction.derivedε_fac_app proves it for arbitrary complexes. -/
theorem globalRingedSpace_derivedCounit_comparison
    (P : ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [P.Additive]
    (L : DerivedCategory
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (α : DerivedCategory.Qh ⋙ L ⟶
      P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (adj : P ⊣ RingedSpace.globalSectionsFunctor X.toRingedSpace)
    [L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    [Functor.IsLeftDerivedFunctor
      (L ⋙ (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor)
        ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor)
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    [Functor.IsRightDerivedFunctor
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor ⋙ L)
        (Functor.whiskerRight
            (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorUnit L ≫
          (Functor.associator _ _ _).hom)
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    L.map ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorUnit.app K) ≫
        (((adj.mapHomotopyCategory (ComplexShape.up ℤ)).derived
          (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
          (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) α
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorUnit).counit.app
            (DerivedCategory.Qh.obj K)) =
      α.app (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).counit.app K) := by
  exact (adj.mapHomotopyCategory (ComplexShape.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) α
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorUnit K

end
end AlgebraicGeometry.Scheme.Modules
