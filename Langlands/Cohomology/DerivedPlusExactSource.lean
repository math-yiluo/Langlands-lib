import Langlands.Cohomology.DerivedPlus
import Langlands.Cohomology.ExactDerivedHomology

/-! # Right-derived comparisons along an exact source functor -/

noncomputable section

universe uC vC wC uD vD wD uE vE wE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Cohomology.DerivedPlusExactSource

open CategoryTheory CategoryTheory.Limits

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  (T : C ⥤ D) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]

/-- An exact functor of abelian categories acts on bounded-below derived objects. -/
def mapDerivedPlus : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D :=
  DerivedCategory.TStructure.t.plus.lift (DerivedCategory.Plus.ι ⋙ T.mapDerivedCategory) (fun A => by
    obtain ⟨n, hA⟩ := A.property
    refine ⟨n, ?_⟩
    change A.obj.IsGE n at hA
    change (T.mapDerivedCategory.obj A.obj).IsGE n
    rw [DerivedCategory.isGE_iff] at hA ⊢
    intro q hq
    exact (T.map_isZero (hA q hq)).of_iso ((exactDerivedHomologyIso T q).app A.obj))

/-- On every complex representative, exact derived image identifies with termwise image. -/
def mapDerivedPlusFactors :
    DerivedCategory.Plus.Q ⋙ mapDerivedPlus T ≅ T.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q :=
  NatIso.ofComponents (fun A => DerivedCategory.Plus.ι.preimageIso
    (T.mapDerivedCategoryFactors.app A.obj)) (fun {_ _} a => by
      apply (DerivedCategory.Plus.ι (C := D)).map_injective
      simp only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      exact T.mapDerivedCategoryFactors.hom.naturality a.hom)

/-- Exact derived image sends a single-object complex to the single-object complex of the image. -/
def mapDerivedPlusSingleIso (n : ℤ) :
    DerivedCategory.Plus.singleFunctor C n ⋙ mapDerivedPlus T ≅
      T ⋙ DerivedCategory.Plus.singleFunctor D n :=
  NatIso.ofComponents (fun A => DerivedCategory.Plus.ι.preimageIso
    ((T.mapDerivedCategorySingleFunctor n).app A)) (fun {_ _} a => by
      apply (DerivedCategory.Plus.ι (C := D)).map_injective
      simp only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      exact (T.mapDerivedCategorySingleFunctor n).hom.naturality a)

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]
  [EnoughInjectives C] [EnoughInjectives D]
  (F : C ⥤ E) [F.Additive] (G : D ⥤ E) [G.Additive] (τ : F ⟶ T ⋙ G)

private def mapComplexCompositeIso :
    T.mapCochainComplexPlus ⋙ G.mapCochainComplexPlus ≅ (T ⋙ G).mapCochainComplexPlus :=
  NatIso.ofComponents (fun A => (CochainComplex.Plus.ι E).preimageIso
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ G)) (.up ℤ)).app A.obj))
    (fun {_ _} a => by
      apply (CochainComplex.Plus.ι E).map_injective
      simp only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      exact (Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ G)) (.up ℤ)).hom.naturality a.hom)

/-- The termwise comparison followed by the right-derived unit on the image complex. -/
def comparisonUnit :
    F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶
      DerivedCategory.Plus.Q ⋙ (mapDerivedPlus T ⋙ G.rightDerivedFunctorPlus) :=
  Functor.whiskerRight (τ.mapCochainComplexPlus ≫ (mapComplexCompositeIso T G).inv) _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ G.rightDerivedFunctorPlusUnit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (mapDerivedPlusFactors T).inv _ ≫
    (Functor.associator _ _ _).hom

/-- A comparison with an exact source change induces a map on bounded-below right-derived
functors, by the defining universal property of right derivation. -/
def rightDerivedComparison : F.rightDerivedFunctorPlus ⟶ mapDerivedPlus T ⋙ G.rightDerivedFunctorPlus :=
  F.rightDerivedFunctorPlus.rightDerivedDesc F.rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso C) _ (comparisonUnit T F G τ)

/-- On complex representatives the derived comparison agrees with the termwise map after the
right-derived units. -/
@[reassoc]
theorem rightDerivedComparison_fac (A : CochainComplex.Plus C) :
    F.rightDerivedFunctorPlusUnit.app A ≫ (rightDerivedComparison T F G τ).app (DerivedCategory.Plus.Q.obj A) =
      (comparisonUnit T F G τ).app A :=
  F.rightDerivedFunctorPlus.rightDerived_fac_app F.rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso C) _ (comparisonUnit T F G τ) A

/-- The comparison evaluated on degree-zero coefficient objects. -/
def derivedComplexComparison : DerivedPlus.derivedComplex F ⟶ T ⋙ DerivedPlus.derivedComplex G :=
  Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor C 0) (rightDerivedComparison T F G τ) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (mapDerivedPlusSingleIso T 0).hom _ ≫
    (Functor.associator _ _ _).hom

end Langlands.Cohomology.DerivedPlusExactSource
