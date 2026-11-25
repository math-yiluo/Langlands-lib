/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.AlgebraicGeometry.SixFunctors.MixedDerivedMateUnit

/-! # Normalization of the canonical derived open exchange

## References

* Stacks Project, Tags 0F7B and 0D6E
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] upperStar lowerStar openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactorsh
  Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  Functor.mapDerivedCategoryNatIso

private lemma derived_square_symm
    {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]
    [Abelian C] [Abelian D] [Abelian E] [Abelian V]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory V]
    (T : C ⥤ D) (L' : D ⥤ V) (L : C ⥤ E) (O : E ⥤ V)
    [T.Additive] [L'.Additive] [L.Additive] [O.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    (e : T ⋙ L' ≅ L ⋙ O) :
    (Functor.mapDerivedCategorySquareIso e.symm).hom =
      (Functor.mapDerivedCategorySquareIso e).inv := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.symm_hom, Iso.trans_hom,
    Iso.trans_inv, Functor.mapDerivedCategoryNatIso_symm, Iso.symm_inv, Category.assoc]

/-- The canonical open/proper exchange carries a right-derived unit to the homotopy
image of the ordinary mate followed by the target unit. Identify inverse derived base
change with the exact-derived inverse square by formal symmetry, then apply the mixed
mate normalization theorem. The source derived adjunctions are precisely the mixed
adjunctions used there. -/
theorem openExchangeDerivedUnit
    (A : Type (u + 1)) [CommRing A]
    {U V W Z : Scheme.{u}} (b : U ⟶ V) (q : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion b] [IsOpenImmersion i] (sq : IsPullback q b i p)
    (L : HomotopyCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) :
    let K := ModuleCat.{u + 1} A;
    let I := openImmersionLowerShriek K i;
    let O := openImmersionLowerShriek K b;
    let R := lowerStar K q;
    let P := lowerStar K p;
    let bc := @asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap K sq);
    let χ := (mateEquiv (upperStarLowerStarAdjunction K q)
      (upperStarLowerStarAdjunction K p) (TwoSquare.mk _ _ _ _ bc.inv));
    let Γ := openImmersionLowerShriekLowerStarExchange K sq;
    I.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app L) ≫
        Γ.app (DerivedCategory.Qh.obj L) ≫
        P.rightDerivedFunctor.map (O.mapDerivedCategoryFactorsh.hom.app L) =
      I.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj L) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ I)) (.up ℤ)).hom.app L ≫
            (χ.mapHomotopyCategory (.up ℤ)).app L ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (O ⋙ P)) (.up ℤ)).inv.app L) ≫
          P.rightDerivedFunctorUnit.app ((O.mapHomotopyCategory (.up ℤ)).obj L) := by
  intro K I O R P bc χ Γ
  have hbc : (Functor.mapDerivedCategorySquareIso bc.symm).hom =
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso K
        sq).inv := by
    exact derived_square_symm _ _ _ _ bc
  have hn := mixedDerivedMateUnit I (upperStar K p) (upperStar K q) O R P
    (upperStarLowerStarAdjunction K q) (upperStarLowerStarAdjunction K p) bc.symm
    (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso K sq).inv hbc L
  simpa only [Γ, χ, Iso.symm_hom, openImmersionLowerShriekLowerStarExchange,
    mapDerivedUpperStarLowerStarAdjunction] using hn

end AlgebraicGeometry.Etale
