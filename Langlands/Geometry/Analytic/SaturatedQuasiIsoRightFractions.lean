import Langlands.Geometry.Analytic.CompatibleQuasiIsoOreRefinement
import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-! # Actual right fractions of saturated strong atlas maps -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : SaturatedAtlasPresentation.{u, v, w} K}

/-- The actual Ore source is still an object of the saturated strong-map category. -/
def quasiIsoOreSource (f : A ⟶ C) (s : B ⟶ C) (hs : s.IsQuasiIso) :
    SaturatedAtlasPresentation.{u, v, w} K where
  presentation := (compatibleFunctor.map f).quasiIsoOreSource (compatibleFunctor.map s)
    hs A.hasAllLocalDomains C.hasAllLocalDomains
  hasAllLocalDomains := (compatibleFunctor.map f).quasiIsoOreSource_hasAllLocalDomains
    (compatibleFunctor.map s) hs A.hasAllLocalDomains C.hasAllLocalDomains

/-- The retained original restrictions define the denominator of the new right fraction. -/
def quasiIsoOreInclusion (f : A ⟶ C) (s : B ⟶ C) (hs : s.IsQuasiIso) :
    quasiIsoOreSource f s hs ⟶ A :=
  ((compatibleFunctor.map f).quasiIsoOreInclusion (compatibleFunctor.map s)
    hs A.hasAllLocalDomains C.hasAllLocalDomains).toStrongHom

theorem isQuasiIso_quasiIsoOreInclusion (f : A ⟶ C) (s : B ⟶ C)
    (hs : s.IsQuasiIso) : (quasiIsoOreInclusion f s hs).IsQuasiIso :=
  (compatibleFunctor.map f).isQuasiIso_quasiIsoOreInclusion (compatibleFunctor.map s)
    hs A.hasAllLocalDomains C.hasAllLocalDomains

/-- The actual bounded forward/reverse composite defines the numerator. -/
def quasiIsoOreLift (f : A ⟶ C) (s : B ⟶ C) (hs : s.IsQuasiIso) :
    quasiIsoOreSource f s hs ⟶ B :=
  ((compatibleFunctor.map f).quasiIsoOreLift (compatibleFunctor.map s)
    hs A.hasAllLocalDomains C.hasAllLocalDomains).toStrongHom

@[simp]
theorem quasiIsoOreInclusion_baseMap (f : A ⟶ C) (s : B ⟶ C) (hs : s.IsQuasiIso) :
    (quasiIsoOreInclusion f s hs).baseMap = ContinuousMap.id A.presentation.space := rfl

@[simp]
theorem quasiIsoOreLift_baseMap (f : A ⟶ C) (s : B ⟶ C) (hs : s.IsQuasiIso) :
    (quasiIsoOreLift f s hs).baseMap = hs.inverseBaseMap.comp f.baseMap := rfl

/-- The square commutes for saturated composition as complete strong morphisms. -/
theorem quasiIsoOre_square (f : A ⟶ C) (s : B ⟶ C) (hs : s.IsQuasiIso) :
    quasiIsoOreLift f s hs ≫ s = quasiIsoOreInclusion f s hs ≫ f := by
  exact congrArg AffinoidAtlasPresentation.CompatibleStrongHom.toStrongHom
    ((compatibleFunctor.map f).quasiIsoOre_square (compatibleFunctor.map s)
      hs A.hasAllLocalDomains C.hasAllLocalDomains)

/-- A quasi-isomorphism numerator is retained when the original numerator is one. -/
theorem isQuasiIso_quasiIsoOreLift (f : A ⟶ C) (hf : f.IsQuasiIso)
    (s : B ⟶ C) (hs : s.IsQuasiIso) : (quasiIsoOreLift f s hs).IsQuasiIso :=
  (compatibleFunctor.map f).isQuasiIso_quasiIsoOreLift hf (compatibleFunctor.map s)
    hs A.hasAllLocalDomains C.hasAllLocalDomains

/-- The constructed actual right fraction resolves any cospan with a
full quasi-isomorphism denominator. No source or square is supplied as input. -/
def quasiIsoOreRightFraction (f : A ⟶ C) (s : B ⟶ C) (hs : s.IsQuasiIso) :
    (quasiIsomorphisms (K := K)).RightFraction A B :=
  ⟨quasiIsoOreInclusion f s hs, isQuasiIso_quasiIsoOreInclusion f s hs,
    quasiIsoOreLift f s hs⟩

theorem quasiIsoOreRightFraction_fac (f : A ⟶ C) (s : B ⟶ C) (hs : s.IsQuasiIso) :
    (quasiIsoOreRightFraction f s hs).s ≫ f =
      (quasiIsoOreRightFraction f s hs).f ≫ s :=
  (quasiIsoOre_square f s hs).symm

/-- Geometric source refinement gives Ore existence; full bounded-test
cancellation gives the second right-fraction axiom with the identity refinement. -/
instance : (quasiIsomorphisms (K := K) :
    MorphismProperty (SaturatedAtlasPresentation.{u, v, w} K)).HasRightCalculusOfFractions where
  exists_rightFraction _ _ φ :=
    ⟨quasiIsoOreRightFraction φ.f φ.s φ.hs, quasiIsoOreRightFraction_fac φ.f φ.s φ.hs⟩
  ext X Y _ f₁ f₂ s hs h := by
    have heq : f₁ = f₂ := hs.cancel_saturatedComp X.hasAllLocalDomains Y.hasAllLocalDomains h
    refine ⟨X, 𝟙 X, ?_, ?_⟩
    · exact AffinoidAtlasPresentation.StrongHom.isQuasiIso_id X.presentation
    · simpa only [Category.id_comp] using heq

end Langlands.Analytic.SaturatedAtlasPresentation
