/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.WeilSheaf.FiniteLeray
import WeilConjectures.WeilSheaf.LowerStarId
import WeilConjectures.WeilSheaf.UpperStarId
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraLeftAdjunction

/-! # Basic comparisons for native derived Weil sheaves

The functors act on the ordinary derived categories of all pro-etale Weil sheaves.
The constructible subcategory is exactly `WeilComplex.objectProperty`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

private noncomputable def nativeOpenAdjunction
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    {U S : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
    [S.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ S) [j.IsOver (Spec (CommRingCat.of k₀))] [IsOpenImmersion j] :
    ProEtaleWeilSheaf.extensionByZero k₀ l j ⊣ ProEtaleWeilSheaf.upperStar k₀ l j := by
  apply Endofunctor.IsoAlgebra.mapOfNatIsoLeftAdjunction
    (ProEtale.adicOpenImmersionLowerShriekAdjunction l _)
    (ProEtale.adicUpperStarLowerStarAdjunction l _)
    _ _ _ (ProEtale.mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv l j _)
    (ProEtale.adicOpenImmersionLowerShriekToLowerStar l _)
    (ProEtale.adicOpenImmersionLowerShriekToLowerStar_geometricFiberMapCompFrobeniusIso l j _)
  intro K
  exact ProEtale.adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar
    _ K

/-- Direct-image composition and identities, and exact open extension with its bounded
constructibility and composition comparisons, in the native equivariant derived categories.
-/
theorem nativeWeilBasicComparisons (k₀ : Type u) [Field k₀] [Finite k₀]
    (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] :
    (∀ (S T H : Scheme.{u})
      [S.Over (Spec (CommRingCat.of k₀))] [T.Over (Spec (CommRingCat.of k₀))]
      [H.Over (Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (H ↘ Spec (CommRingCat.of k₀))]
      (f : S ⟶ T) (g : T ⟶ H)
      [f.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))],
      Nonempty ((ProEtaleWeilSheaf.lowerStar k₀ l (f ≫ g)).rightDerivedFunctor ≅
        (ProEtaleWeilSheaf.lowerStar k₀ l f).rightDerivedFunctor ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor)) ∧
    (∀ (S : Scheme.{u}) [S.Over (Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k₀))],
      Nonempty ((ProEtaleWeilSheaf.lowerStar k₀ l (𝟙 S)).rightDerivedFunctor ≅
        𝟭 (_root_.DerivedCategory (ProEtaleWeilSheaf k₀ l S)))) ∧
    (∀ (U S : Scheme.{u})
      [U.Over (Spec (CommRingCat.of k₀))] [S.Over (Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k₀))]
      (j : U ⟶ S) [j.IsOver (Spec (CommRingCat.of k₀))]
      [IsOpenImmersion j] [QuasiCompact j],
      PreservesFiniteLimits (ProEtaleWeilSheaf.extensionByZero k₀ l j) ∧
      PreservesFiniteColimits (ProEtaleWeilSheaf.extensionByZero k₀ l j) ∧
      ∀ (K : _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l U)),
        WeilComplex.objectProperty k₀ l U K →
          WeilComplex.objectProperty k₀ l S
            ((ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory.obj K)) ∧
    (∀ (U S T : Scheme.{u})
      [U.Over (Spec (CommRingCat.of k₀))] [S.Over (Spec (CommRingCat.of k₀))]
      [T.Over (Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
      (j : U ⟶ S) (i : S ⟶ T)
      [j.IsOver (Spec (CommRingCat.of k₀))] [i.IsOver (Spec (CommRingCat.of k₀))]
      [IsOpenImmersion j] [QuasiCompact j] [IsOpenImmersion i] [QuasiCompact i],
      Nonempty ((ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory ⋙
        (ProEtaleWeilSheaf.extensionByZero k₀ l i).mapDerivedCategory ≅
          (ProEtaleWeilSheaf.extensionByZero k₀ l (j ≫ i)).mapDerivedCategory)) ∧
    (∀ (S : Scheme.{u}) [S.Over (Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k₀))],
      Nonempty ((ProEtaleWeilSheaf.extensionByZero k₀ l (𝟙 S)).mapDerivedCategory ≅
        𝟭 (_root_.DerivedCategory (ProEtaleWeilSheaf k₀ l S)))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro S T H _ _ _ _ _ _ f g _ _
    exact ⟨ProEtaleWeilSheaf.rightDerivedLowerStarCompIso k₀ l f g⟩
  · intro S _ _
    exact ⟨Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarIdIso k₀ l S) ≪≫
      (𝟭 (ProEtaleWeilSheaf k₀ l S)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
      Functor.mapDerivedCategoryIdIso _⟩
  · intro U S _ _ _ _ j _ _ _
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro K hK
    refine ⟨(ProEtaleWeilSheaf.extensionByZero k₀ l j).bounded_mapDerivedCategory_obj hK.1,
      fun n ↦ ?_⟩
    exact (WeilSheaf.objectProperty k₀ l S).prop_of_iso
      (((ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategoryHomologyFunctorIso
        n).app K)
      (WeilSheaf.isAdicConstructibleSheaf_extensionByZero j _ (hK.2 n))
  · intro U S T _ _ _ _ _ _ j i _ _ _ _ _ _
    let adj := (nativeOpenAdjunction k₀ l j).comp (nativeOpenAdjunction k₀ l i)
    let adj' := (nativeOpenAdjunction k₀ l (j ≫ i)).ofNatIsoRight
      (ProEtaleWeilSheaf.upperStarCompIso k₀ l j i)
    exact ⟨Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso (Adjunction.leftAdjointUniq adj adj')⟩
  · intro S _ _
    let adj := (nativeOpenAdjunction k₀ l (𝟙 S)).ofNatIsoRight
      (ProEtaleWeilSheaf.upperStarIdIso k₀ l S)
    exact ⟨Functor.mapDerivedCategoryNatIso (Adjunction.leftAdjointUniq adj Adjunction.id) ≪≫
      Functor.mapDerivedCategoryIdIso _⟩

end AlgebraicGeometry
