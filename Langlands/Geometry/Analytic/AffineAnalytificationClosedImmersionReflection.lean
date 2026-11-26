import Langlands.Geometry.Analytic.SchemeAnalytificationQuasiFiniteProperness
import Langlands.Geometry.Analytic.AnalyticClosedImmersionTopology
import Langlands.Geometry.Analytic.AnalyticClosedImmersionMonomorphism
import Langlands.Geometry.Analytic.AffineAnalytificationMonomorphismComparison
import Langlands.Geometry.Analytic.AffineAnalytificationUniverseReduction

/-! # Analytic closed immersions of affine analytifications come from surjections -/

noncomputable section

universe u v

namespace Langlands.Analytic.AffineAnalytification

namespace ClosedImmersionReflection

open CategoryTheory _root_.AlgebraicGeometry Topology SaturatedAtlasPresentation
open Langlands.Analytic.AffineSchemeAnalytification Langlands.Analytic.SchemeAnalytification

section Coordinates

variable {K : Type u} [CommRing K]

/-- The top affine open of an affine spectrum. -/
abbrev topChart (A : Type u) [CommRing A] : (Spec (CommRingCat.of A)).affineOpens :=
  ⟨⊤, isAffineOpen_top _⟩

instance topChart_isAffine (A : Type u) [CommRing A] : IsAffine (topChart A : Scheme.{u}) :=
  (topChart A).property

variable (A : Type u) [CommRing A] [Algebra K A]

/-- The global-section isomorphism of an affine spectrum, as a map of `K`-algebras. -/
def gammaAlgHom : A →ₐ[K] CoordinateRing (Spec.algebraMap K A) where
  toRingHom := (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  commutes' k := by
    have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap K A))
    exact congrArg (fun g => g.hom k) h

/-- The coordinates of the top chart of `Spec A`. -/
def topCoordinateMap :
    A →ₐ[K] CoordinateRing (structureMap (Spec.algebraMap K A) (topChart A)) :=
  (coordinateMap ((topChart A : (Spec (CommRingCat.of A)).Opens).ι) rfl).comp (gammaAlgHom A)

theorem topCoordinateMap_bijective : Function.Bijective (topCoordinateMap (K := K) A) := by
  have h₁ : Function.Bijective (gammaAlgHom (K := K) A) :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm.bijective
  have : IsIso (Scheme.Hom.appTop ((topChart A : (Spec (CommRingCat.of A)).Opens).ι)) :=
    Scheme.Hom.isIso_app _ _ (by simp)
  have h₂ : Function.Bijective
      (coordinateMap (fY := Spec.algebraMap K A)
        ((topChart A : (Spec (CommRingCat.of A)).Opens).ι) rfl) :=
    ConcreteCategory.bijective_of_isIso
      (Scheme.Hom.appTop ((topChart A : (Spec (CommRingCat.of A)).Opens).ι))
  exact h₂.comp h₁

/-- The coordinates of the top chart, as an isomorphism of `K`-algebras. -/
def topCoordinateEquiv :
    A ≃ₐ[K] CoordinateRing (structureMap (Spec.algebraMap K A) (topChart A)) :=
  AlgEquiv.ofBijective (topCoordinateMap A) (topCoordinateMap_bijective A)

variable {A} {B : Type u} [CommRing B] [Algebra K B] (f : A →ₐ[K] B)

theorem specMap_comp_algebraMap :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.algebraMap K A = Spec.algebraMap K B := by
  rw [Spec.algebraMap, Spec.algebraMap, ← Spec.map_comp]
  congr 1
  ext k
  exact f.commutes k

/-- The top coordinates are natural in the algebra. -/
theorem openCoordinateMap_comp_topCoordinateMap
    (h : ((topChart B : (Spec (CommRingCat.of B)).affineOpens) : (Spec (CommRingCat.of B)).Opens) ≤
      Spec.map (CommRingCat.ofHom f.toRingHom) ⁻¹ᵁ
        ((topChart A : (Spec (CommRingCat.of A)).affineOpens) : (Spec (CommRingCat.of A)).Opens)) :
    (openCoordinateMap (Spec.map (CommRingCat.ofHom f.toRingHom)) (specMap_comp_algebraMap f)
        h).comp (topCoordinateMap A) = (topCoordinateMap B).comp f := by
  ext a
  let q := Spec.map (CommRingCat.ofHom f.toRingHom)
  change (q.resLE _ _ h).appTop
      (((topChart A : (Spec (CommRingCat.of A)).Opens).ι).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) =
    ((topChart B : (Spec (CommRingCat.of B)).Opens).ι).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (f a))
  have e1 := congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))
    (congrArg Scheme.Hom.appTop (Scheme.Hom.resLE_comp_ι q h))
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at e1
  have hn := congrArg (fun g => g.hom a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f.toRingHom))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hn
  change _ = _ at e1
  rw [e1]
  change _ = ((topChart B : (Spec (CommRingCat.of B)).Opens).ι).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (f.toRingHom a))
  rw [hn]

end Coordinates

section Analytic

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The structure morphism of the spectrum of a finite type algebra is locally of
finite type. -/
theorem locallyOfFiniteType_specAlgebraMap (A : Type u) [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] : LocallyOfFiniteType (Spec.algebraMap K A) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)

variable {A : Type u} [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
  (P : FinitePolynomialPresentation K A)

attribute [local instance] locallyOfFiniteType_specAlgebraMap

/-- The analytic isomorphism from the top chart of `Spec A` to the supplied
polynomial-locus model. -/
def topChartIso :
    AffineAnalytification.localized K (chartPresentation K (Spec.algebraMap K A) (topChart A)) ≅
      AffineAnalytification.localized K P :=
  letI := UniverseReduction.isIso_localizedHom_of_algEquiv P
    (chartPresentation K (Spec.algebraMap K A) (topChart A)) (topCoordinateEquiv A)
  asIso (localizedHom K P (chartPresentation K (Spec.algebraMap K A) (topChart A))
    (topCoordinateEquiv A).toAlgHom)

set_option backward.isDefEq.respectTransparency false in
/-- The glued scheme analytification of `Spec A` and the supplied polynomial-locus
model are homeomorphic through the top chart coordinates. -/
def comparisonHomeomorph :
    SchemeAnalytification.Space K (Spec.algebraMap K A) ≃ₜ AffineAnalytification.Space K P :=
  (affineTopChartHomeomorph K (Spec.algebraMap K A)).symm.trans
    (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso (topChartIso K P)))

set_option backward.isDefEq.respectTransparency false in
theorem comparisonHomeomorph_ι (y : LocalSpace K (Spec.algebraMap K A) (topChart A)) :
    comparisonHomeomorph K P (ι K (Spec.algebraMap K A) (topChart A) y) =
      baseMap K P (chartPresentation K (Spec.algebraMap K A) (topChart A))
        (topCoordinateMap A) y := by
  let e := affineTopChartHomeomorph K (Spec.algebraMap K A)
  change (localizedSpaceFunctor.map (localizedHom K P
    (chartPresentation K (Spec.algebraMap K A) (topChart A))
    (topCoordinateEquiv A).toAlgHom)).hom (e.symm (e y)) = _
  rw [Homeomorph.symm_apply_apply, localizedSpaceFunctor_map_localizedHom]
  rfl

variable {B : Type u} [CommRing B] [Algebra K B] [Algebra.FiniteType K B]
  (Q : FinitePolynomialPresentation K B) (f : A →ₐ[K] B)

set_option backward.isDefEq.respectTransparency false in
/-- The glued scheme analytification of `Spec B → Spec A` is the polynomial-locus
map under the comparison homeomorphisms. -/
theorem comparisonHomeomorph_analytification
    (x : SchemeAnalytification.Space K (Spec.algebraMap K B)) :
    comparisonHomeomorph K P
        (MorphismExistence.analytification K (Spec.algebraMap K B) (Spec.algebraMap K A)
          (Spec.map (CommRingCat.ofHom f.toRingHom)) (specMap_comp_algebraMap f) x) =
      baseMap K P Q f (comparisonHomeomorph K Q x) := by
  let eB := affineTopChartHomeomorph K (Spec.algebraMap K B)
  obtain ⟨y, rfl⟩ := eB.surjective x
  change comparisonHomeomorph K P
      (MorphismExistence.analytification K (Spec.algebraMap K B) (Spec.algebraMap K A)
        (Spec.map (CommRingCat.ofHom f.toRingHom)) (specMap_comp_algebraMap f)
        (ι K (Spec.algebraMap K B) (topChart B) y)) =
    baseMap K P Q f (comparisonHomeomorph K Q (ι K (Spec.algebraMap K B) (topChart B) y))
  have h : ((topChart B : (Spec (CommRingCat.of B)).affineOpens) :
      (Spec (CommRingCat.of B)).Opens) ≤ Spec.map (CommRingCat.ofHom f.toRingHom) ⁻¹ᵁ
        ((topChart A : (Spec (CommRingCat.of A)).affineOpens) :
          (Spec (CommRingCat.of A)).Opens) := by
    change (⊤ : (Spec (CommRingCat.of B)).Opens) ≤ _ ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of A)).Opens)
    simp
  rw [MorphismExistence.isAnalytificationMap_analytification K (Spec.algebraMap K B)
      (Spec.algebraMap K A) _ (specMap_comp_algebraMap f) (topChart B) (topChart A) h y,
    comparisonHomeomorph_ι, comparisonHomeomorph_ι]
  change baseMap K P _ (topCoordinateMap A) (baseMap K _ _ (openCoordinateMap _
      (specMap_comp_algebraMap f) h) y) = _
  rw [MorphismComparison.baseMap_baseMap K P _ _ (topCoordinateMap A)
      (openCoordinateMap _ (specMap_comp_algebraMap f) h)
      ((openCoordinateMap _ (specMap_comp_algebraMap f) h).comp (topCoordinateMap A))
      (fun _ => rfl),
    MorphismComparison.baseMap_baseMap K P Q _ f (topCoordinateMap B)
      ((topCoordinateMap B).comp f) (fun _ => rfl),
    openCoordinateMap_comp_topCoordinateMap f h]

set_option backward.isDefEq.respectTransparency false in
/-- If the analytified map is a closed embedding and `Spec B → Spec A` is a
monomorphism, then `A → B` is surjective. -/
theorem surjective_of_isClosedEmbedding_of_mono
    (hc : IsClosedEmbedding (baseMap K P Q f))
    [Mono (Spec.map (CommRingCat.ofHom f.toRingHom))] : Function.Surjective f := by
  let q := Spec.map (CommRingCat.ofHom f.toRingHom)
  let F := MorphismExistence.analytification K (Spec.algebraMap K B) (Spec.algebraMap K A) q
    (specMap_comp_algebraMap f)
  have hF : (F : SchemeAnalytification.Space K (Spec.algebraMap K B) →
      SchemeAnalytification.Space K (Spec.algebraMap K A)) =
      (comparisonHomeomorph K P).symm ∘ baseMap K P Q f ∘ comparisonHomeomorph K Q := by
    funext x
    change F x = (comparisonHomeomorph K P).symm (baseMap K P Q f (comparisonHomeomorph K Q x))
    rw [← comparisonHomeomorph_analytification K P Q f x]
    exact ((comparisonHomeomorph K P).symm_apply_apply (F x)).symm
  have hp : IsProperMap F := by
    rw [hF]
    exact (comparisonHomeomorph K P).symm.isProperMap.comp
      (hc.isProperMap.comp (comparisonHomeomorph K Q).isProperMap)
  have hft : (CommRingCat.Hom.hom (CommRingCat.ofHom f.toRingHom)).FiniteType := by
    change f.toRingHom.FiniteType
    have hB : (algebraMap K B).FiniteType := RingHom.finiteType_algebraMap.mpr inferInstance
    rw [← f.comp_algebraMap] at hB
    exact RingHom.FiniteType.of_comp_finiteType hB
  have : LocallyOfFiniteType q := HasRingHomProperty.Spec_iff.mpr hft
  have hfin : IsFinite q :=
    isFinite_of_isProperMap_analytification K (Spec.algebraMap K B) (Spec.algebraMap K A) q
      (specMap_comp_algebraMap f) hp
  have : Epi (CommRingCat.ofHom f.toRingHom) := epi_of_mono_specMap _
  exact RingHom.surjective_of_epi_of_finite (CommRingCat.ofHom f.toRingHom)
    ((IsFinite.SpecMap_iff _).mp hfin)

end Analytic

end ClosedImmersionReflection

open ClosedImmersionReflection CategoryTheory SaturatedAtlasPresentation _root_.AlgebraicGeometry

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- An analytic closed immersion of affine analytifications, with algebras in the
universe of the field, is induced by a surjective algebra map. -/
theorem surjective_of_closedImmersion_localizedHom_of_univ {A B : Type u} [CommRing A]
    [Algebra K A] [CommRing B] [Algebra K B] (P : FinitePolynomialPresentation K A)
    (Q : FinitePolynomialPresentation K B) (f : A →ₐ[K] B)
    (hc : closedImmersion (localizedHom K P Q f)) : Function.Surjective f := by
  have : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective P.map P.surjective
  have : Algebra.FiniteType K B := Algebra.FiniteType.of_surjective Q.map Q.surjective
  have : Mono (localizedHom K P Q f) := hc.mono
  have : Epi (CommRingCat.ofHom f.toRingHom) := epi_of_mono_localizedHom P Q f
  have : Mono (Spec.map (CommRingCat.ofHom f.toRingHom)) := mono_specMap_of_epi _
  have he := hc.isClosedEmbedding
  rw [localizedSpaceFunctor_map_localizedHom] at he
  exact surjective_of_isClosedEmbedding_of_mono K P Q f he

/-- An analytic closed immersion of affine analytifications is induced by a
surjective algebra map. -/
theorem surjective_of_closedImmersion_localizedHom {A B : Type v} [CommRing A]
    [Algebra K A] [CommRing B] [Algebra K B] (P : FinitePolynomialPresentation K A)
    (Q : FinitePolynomialPresentation K B) (f : A →ₐ[K] B)
    (hc : closedImmersion (localizedHom K P Q f)) : Function.Surjective f :=
  (UniverseReduction.surjective_iff_model P Q f).mpr
    (surjective_of_closedImmersion_localizedHom_of_univ _ _ _
      ((UniverseReduction.closedImmersion_iff_model P Q f).mp hc))

end Langlands.Analytic.AffineAnalytification
