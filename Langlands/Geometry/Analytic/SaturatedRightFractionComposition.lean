import Langlands.Geometry.Analytic.SaturatedLocalizedFractions

/-! # Constructed Ore composition of actual saturated right fractions -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C D : SaturatedAtlasPresentation.{u, v, w} K}

/-- Compose actual right fractions using the constructed retained-chart Ore
source for the first numerator and the second denominator. -/
def rightFractionComp
    (φ : (quasiIsomorphisms (K := K)).RightFraction A B)
    (ψ : (quasiIsomorphisms (K := K)).RightFraction B C) :
    (quasiIsomorphisms (K := K)).RightFraction A C :=
  ⟨quasiIsoOreInclusion φ.f ψ.s ψ.hs ≫ φ.s,
    (quasiIsomorphisms (K := K)).comp_mem _ _
      (isQuasiIso_quasiIsoOreInclusion φ.f ψ.s ψ.hs) φ.hs,
    quasiIsoOreLift φ.f ψ.s ψ.hs ≫ ψ.f⟩

@[simp]
theorem rightFractionComp_s_baseMap
    (φ : (quasiIsomorphisms (K := K)).RightFraction A B)
    (ψ : (quasiIsomorphisms (K := K)).RightFraction B C) :
    (rightFractionComp φ ψ).s.baseMap = φ.s.baseMap := by
  ext x
  rfl

@[simp]
theorem rightFractionComp_f_baseMap
    (φ : (quasiIsomorphisms (K := K)).RightFraction A B)
    (ψ : (quasiIsomorphisms (K := K)).RightFraction B C) :
    (rightFractionComp φ ψ).f.baseMap =
      ψ.f.baseMap.comp (ψ.hs.inverseBaseMap.comp φ.f.baseMap) := rfl

/-- Cancelling the denominator of the actual fraction gives its numerator. -/
@[reassoc (attr := simp)]
theorem localizationFunctor_map_s_comp_localizedRightFraction
    (φ : (quasiIsomorphisms (K := K)).RightFraction A B) :
    localizationFunctor.map φ.s ≫ localizedRightFraction φ = localizationFunctor.map φ.f :=
  φ.map_s_comp_map localizationFunctor (Localization.inverts _ (quasiIsomorphisms (K := K)))

/-- The constructed Ore composite interprets as the composite localized arrow. -/
@[simp]
theorem localizedRightFraction_comp
    (φ : (quasiIsomorphisms (K := K)).RightFraction A B)
    (ψ : (quasiIsomorphisms (K := K)).RightFraction B C) :
    localizedRightFraction (rightFractionComp φ ψ) =
      localizedRightFraction φ ≫ localizedRightFraction ψ := by
  apply (cancel_epi (localizationFunctor.map (rightFractionComp φ ψ).s)).1
  rw [localizationFunctor_map_s_comp_localizedRightFraction]
  let a := quasiIsoOreInclusion φ.f ψ.s ψ.hs
  let b := quasiIsoOreLift φ.f ψ.s ψ.hs
  change localizationFunctor.map (b ≫ ψ.f) =
    localizationFunctor.map (a ≫ φ.s) ≫
      (localizedRightFraction φ ≫ localizedRightFraction ψ)
  calc
    localizationFunctor.map (b ≫ ψ.f) =
        localizationFunctor.map b ≫ localizationFunctor.map ψ.f :=
      localizationFunctor.map_comp b ψ.f
    _ = localizationFunctor.map b ≫
        (localizationFunctor.map ψ.s ≫ localizedRightFraction ψ) := by
      rw [localizationFunctor_map_s_comp_localizedRightFraction]
    _ = localizationFunctor.map (b ≫ ψ.s) ≫ localizedRightFraction ψ := by
      rw [Functor.map_comp, Category.assoc]
    _ = localizationFunctor.map (a ≫ φ.f) ≫ localizedRightFraction ψ := by
      rw [quasiIsoOre_square φ.f ψ.s ψ.hs]
    _ = localizationFunctor.map a ≫
        (localizationFunctor.map φ.f ≫ localizedRightFraction ψ) := by
      rw [Functor.map_comp, Category.assoc]
    _ = localizationFunctor.map a ≫
        ((localizationFunctor.map φ.s ≫ localizedRightFraction φ) ≫
          localizedRightFraction ψ) := by
      rw [localizationFunctor_map_s_comp_localizedRightFraction]
    _ = localizationFunctor.map (a ≫ φ.s) ≫
        (localizedRightFraction φ ≫ localizedRightFraction ψ) := by
      rw [Functor.map_comp]
      simp only [Category.assoc]

/-- The trivial denominator interprets as the original mapped arrow. -/
@[simp]
theorem localizedRightFraction_ofHom (f : A ⟶ B) :
    localizedRightFraction (MorphismProperty.RightFraction.ofHom (quasiIsomorphisms (K := K)) f) =
      localizationFunctor.map f :=
  MorphismProperty.RightFraction.map_ofHom _ f localizationFunctor
    (Localization.inverts _ (quasiIsomorphisms (K := K)))

/-- Common refinement of each factor is preserved by the constructed Ore composition. -/
theorem fractionCommonRefinement_comp
    {φ φ' : (quasiIsomorphisms (K := K)).RightFraction A B}
    {ψ ψ' : (quasiIsomorphisms (K := K)).RightFraction B C}
    (hφ : FractionCommonRefinement φ φ') (hψ : FractionCommonRefinement ψ ψ') :
    FractionCommonRefinement (rightFractionComp φ ψ) (rightFractionComp φ' ψ') := by
  apply (localizedRightFraction_eq_iff _ _).1
  rw [localizedRightFraction_comp, localizedRightFraction_comp,
    (localizedRightFraction_eq_iff φ φ').2 hφ,
    (localizedRightFraction_eq_iff ψ ψ').2 hψ]

/-- Actual Ore composition descends to the common-refinement hom quotients. -/
def rightFractionQuotientComp :
    Quotient (rightFractionSetoid A B) → Quotient (rightFractionSetoid B C) →
      Quotient (rightFractionSetoid A C) :=
  Quotient.map₂ rightFractionComp (fun {_ _} hφ {_ _} hψ =>
    fractionCommonRefinement_comp hφ hψ)

@[simp]
theorem rightFractionQuotientComp_mk
    (φ : (quasiIsomorphisms (K := K)).RightFraction A B)
    (ψ : (quasiIsomorphisms (K := K)).RightFraction B C) :
    rightFractionQuotientComp (Quotient.mk _ φ) (Quotient.mk _ ψ) =
      Quotient.mk _ (rightFractionComp φ ψ) := rfl

/-- The computed hom equivalences preserve the descended Ore composition. -/
@[simp]
theorem rightFractionHomEquiv_comp
    (x : Quotient (rightFractionSetoid A B)) (y : Quotient (rightFractionSetoid B C)) :
    rightFractionHomEquiv (rightFractionQuotientComp x y) =
      rightFractionHomEquiv x ≫ rightFractionHomEquiv y := by
  refine Quotient.inductionOn₂ x y ?_
  intro φ ψ
  exact localizedRightFraction_comp φ ψ

/-- The identity class has the literal identity as denominator and numerator. -/
def rightFractionQuotientId (A : SaturatedAtlasPresentation.{u, v, w} K) :
    Quotient (rightFractionSetoid A A) :=
  Quotient.mk _ (MorphismProperty.RightFraction.ofHom (quasiIsomorphisms (K := K)) (𝟙 A))

@[simp]
theorem rightFractionHomEquiv_id (A : SaturatedAtlasPresentation.{u, v, w} K) :
    rightFractionHomEquiv (rightFractionQuotientId A) = 𝟙 (localizationFunctor.obj A) := by
  change localizedRightFraction
    (MorphismProperty.RightFraction.ofHom (quasiIsomorphisms (K := K)) (𝟙 A)) = _
  rw [localizedRightFraction_ofHom]
  exact localizationFunctor.map_id A

@[simp]
theorem rightFractionQuotientId_comp (x : Quotient (rightFractionSetoid A B)) :
    rightFractionQuotientComp (rightFractionQuotientId A) x = x := by
  apply rightFractionHomEquiv.injective
  simp only [rightFractionHomEquiv_comp, rightFractionHomEquiv_id, Category.id_comp]

@[simp]
theorem rightFractionQuotientComp_id (x : Quotient (rightFractionSetoid A B)) :
    rightFractionQuotientComp x (rightFractionQuotientId B) = x := by
  apply rightFractionHomEquiv.injective
  simp only [rightFractionHomEquiv_comp, rightFractionHomEquiv_id, Category.comp_id]

/-- Associativity holds on common-refinement classes of actual Ore composites. -/
theorem rightFractionQuotientComp_assoc
    (x : Quotient (rightFractionSetoid A B)) (y : Quotient (rightFractionSetoid B C))
    (z : Quotient (rightFractionSetoid C D)) :
    rightFractionQuotientComp (rightFractionQuotientComp x y) z =
      rightFractionQuotientComp x (rightFractionQuotientComp y z) := by
  apply rightFractionHomEquiv.injective
  simp only [rightFractionHomEquiv_comp, Category.assoc]

/-- Actual iterated composites have a full common refinement, even though their
constructed retained-chart sources need not be definitionally equal. -/
theorem rightFractionComp_assoc_commonRefinement
    (φ : (quasiIsomorphisms (K := K)).RightFraction A B)
    (ψ : (quasiIsomorphisms (K := K)).RightFraction B C)
    (χ : (quasiIsomorphisms (K := K)).RightFraction C D) :
    FractionCommonRefinement (rightFractionComp (rightFractionComp φ ψ) χ)
      (rightFractionComp φ (rightFractionComp ψ χ)) := by
  apply (localizedRightFraction_eq_iff _ _).1
  simp only [localizedRightFraction_comp, Category.assoc]

/-- The underlying continuous map of a constructed composite is the composite
of the two numerator-after-inverse-denominator continuous maps. -/
theorem localizedSpaceFunctor_map_rightFractionComp
    (φ : (quasiIsomorphisms (K := K)).RightFraction A B)
    (ψ : (quasiIsomorphisms (K := K)).RightFraction B C) :
    localizedSpaceFunctor.map (localizedRightFraction (rightFractionComp φ ψ)) =
      TopCat.ofHom ((ψ.f.baseMap.comp ψ.hs.inverseBaseMap).comp
        (φ.f.baseMap.comp φ.hs.inverseBaseMap)) := by
  rw [localizedRightFraction_comp, Functor.map_comp,
    localizedSpaceFunctor_map_rightFraction, localizedSpaceFunctor_map_rightFraction]
  rfl

end Langlands.Analytic.SaturatedAtlasPresentation
