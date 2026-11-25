/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.NativeBaseChange.NativeBaseChangeForgetComparison
import WeilConjectures.CategoryTheory.Endofunctor.FixedPairDerivedForgetComparison

/-!
# Natural proper base change in the native derived Weil categories

The source is the full bounded constructible subcategory of the ordinary derived
category of native Weil modules. The target is the ambient native equivariant
derived category. All operations are the recorded actual equivariant operations.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Natural proper base change for the native ordinary derived Weil categories.
-/
theorem nativeWeil_proper_natural_baseChange
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)]
    {Z' Z T' T : Scheme.{u}}
    [Z'.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
    [T'.Over (Spec (CommRingCat.of k₀))] [T.Over (Spec (CommRingCat.of k₀))]
    (v : Z' ⟶ Z) (p' : Z' ⟶ T') (p : Z ⟶ T) (u : T' ⟶ T)
    [v.IsOver (Spec (CommRingCat.of k₀))] [p'.IsOver (Spec (CommRingCat.of k₀))]
    [p.IsOver (Spec (CommRingCat.of k₀))] [u.IsOver (Spec (CommRingCat.of k₀))]
    (_sq : ChosenCartesianSquare v p' p u) [IsProper p]
    [QuasiCompact (T ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (T ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (T' ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (T' ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (T' ↘ Spec (CommRingCat.of k₀))] :
    Nonempty
      (((WeilComplex.objectProperty k₀ l Z).ι ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor ⋙
          (ProEtaleWeilSheaf.upperStar k₀ l u).mapDerivedCategory) ≅
        ((WeilComplex.objectProperty k₀ l Z).ι ⋙
          (ProEtaleWeilSheaf.upperStar k₀ l v).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l p').rightDerivedFunctor)) := by
  let F := CategoryTheory.Endofunctor.IsoAlgebra.forget
    (WeilSheaf.frobeniusPullback k₀ l T')
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hF⟩ :=
    CategoryTheory.Endofunctor.IsoAlgebra.fixedPair_forget_properties
      (WeilSheaf.frobeniusPullback k₀ l T')
  let : F.mapDerivedCategory.ReflectsIsomorphisms := hF
  have component_iso (K : WeilComplex k₀ l Z) :
      IsIso ((NativeBaseChange.mate k₀ l _sq.toCommSq).app K.obj) := by
    have hbounded := Functor.bounded_mapDerivedCategory_obj
      (CategoryTheory.Endofunctor.IsoAlgebra.forget
        (WeilSheaf.frobeniusPullback k₀ l Z)) K.property.1
    have hc (n : ℤ) : ProEtale.IsAdicConstructibleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ n).obj
          ((NativeBaseChange.forget k₀ l Z).obj K.obj)) := by
      exact (ProEtale.adicConstructibleSheaf l _).prop_of_iso
        (((CategoryTheory.Endofunctor.IsoAlgebra.forget
          (WeilSheaf.frobeniusPullback k₀ l Z)).mapDerivedCategoryHomologyFunctorIso n).app
            K.obj) (K.property.2 n)
    have := NativeBaseChange.geometric_proper_baseChange_isIso k₀ l _sq
      ((NativeBaseChange.forget k₀ l Z).obj K.obj) hbounded hc
    have : IsIso ((NativeBaseChange.forget k₀ l T').map
        ((NativeBaseChange.mate k₀ l _sq.toCommSq).app K.obj)) := by
      rw [NativeBaseChange.forget_mate]
      infer_instance
    exact isIso_of_reflects_iso _ (NativeBaseChange.forget k₀ l T')
  let β := Functor.whiskerLeft (WeilComplex.objectProperty k₀ l Z).ι
    (NativeBaseChange.mate k₀ l _sq.toCommSq)
  have : ∀ K, IsIso (β.app K) := fun K ↦ component_iso K
  have : IsIso β := NatIso.isIso_of_isIso_app β
  exact ⟨asIso β⟩

end AlgebraicGeometry
