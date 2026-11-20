import Langlands.Geometry.Analytic.AffineAnalytificationAffinoidLocalized

/-! # Naturality of localized affinoid tests -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffineAnalytification

open CategoryTheory Set AffinoidAtlasPresentation PresentedAffinoidAlgebra
open SaturatedAtlasPresentation ChartFamilyComparison

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
  (R : PresentedAffinoidAlgebra K)

private theorem affinoidStrongAlgHom_comp_saturatedHom
    {B : Type w} [CommRing B] [Algebra K B]
    (Q : FinitePolynomialPresentation K B) (f : A →ₐ[K] B)
    (F : SmallAffinoidSpectrum.saturated.{u, u} R ⟶ saturated K Q) :
    affinoidStrongAlgHom K P R (F ≫ saturatedHom K P Q f) =
      (affinoidStrongAlgHom K Q R F).comp f := by
  unfold affinoidStrongAlgHom
  rw [toAlgebraFamily_comp_saturatedHom, AlgHom.comp_assoc]

private theorem saturatedAffinoidHom_comp {B : Type w} [CommRing B] [Algebra K B]
    (Q : FinitePolynomialPresentation K B) (f : A →ₐ[K] B) (φ : B →ₐ[K] R) :
    saturatedAffinoidHom K Q R φ ≫ saturatedHom K P Q f =
      saturatedAffinoidHom K P R (φ.comp f) := by
  apply affinoidStrongAlgHom_injective K P R
  rw [affinoidStrongAlgHom_comp_saturatedHom, affinoidStrongAlgHom_saturatedAffinoidHom,
    affinoidStrongAlgHom_saturatedAffinoidHom]

/-- Postcomposition by a morphism of affine analytifications is
precomposition with its algebra map. -/
theorem localizedAffinoidHom_comp {B : Type w} [CommRing B] [Algebra K B]
    (Q : FinitePolynomialPresentation K B) (f : A →ₐ[K] B) (φ : B →ₐ[K] R) :
    localizedAffinoidHom K Q R φ ≫ localizedHom K P Q f =
      localizedAffinoidHom K P R (φ.comp f) := by
  change localizationFunctor.map (saturatedAffinoidHom K Q R φ) ≫
    localizationFunctor.map (saturatedHom K P Q f) =
      localizationFunctor.map (saturatedAffinoidHom K P R (φ.comp f))
  rw [← Functor.map_comp, saturatedAffinoidHom_comp]

omit [CompleteSpace K] in
private theorem comp_cast_coordinate {R' S T U : PresentedAffinoidAlgebra K}
    (p : BoundedAlgHom K S T) (q : BoundedAlgHom K R' S)
    (r : BoundedAlgHom K R' T) (c : BoundedAlgHom K U R')
    (a : A →ₐ[K] U) (h : r = p.comp q) :
    (r.comp c).toAlgHom.comp a = p.toAlgHom.comp ((q.comp c).toAlgHom.comp a) := by
  subst r
  rfl

private theorem toAlgebraFamily_precomp
    {U V : SaturatedAtlasPresentation.{u, u, u} K}
    (g : U ⟶ V) (F : V ⟶ saturated K P)
    (i : U.presentation.atlas.Index) (j : V.presentation.atlas.Index)
    (hij : g.baseMap '' range (U.presentation.atlas.chart i) ⊆
      range (V.presentation.atlas.chart j)) :
    (toAlgebraFamily P (g ≫ F)).map i =
      (g.pullback i j hij).toAlgHom.comp ((toAlgebraFamily P F).map j) := by
  obtain ⟨k, hk⟩ := original_target_exists P F j
  have hF := original_admissible P F j k hk
  have hcomp := g.comp_admissible F i j (originalIndex P k) hij hF
  have htarget : (g ≫ F).baseMap '' range (U.presentation.atlas.chart i) ⊆
      range ((presentation K P).atlas.chart k) :=
    hcomp.trans (originalRange P k).subset
  have hp : (g ≫ F).pullback i (originalIndex P k) hcomp =
      (g.pullback i j hij).comp (F.pullback j (originalIndex P k) hF) :=
    g.saturatedComp_pullback F U.hasAllLocalDomains V.hasAllLocalDomains
      i j (originalIndex P k) hij hF hcomp
  calc
    (toAlgebraFamily P (g ≫ F)).map i = chartAlgHom P (g ≫ F) i k htarget :=
      toAlgebraFamily_map_eq P (g ≫ F) i k htarget
    _ = (g.pullback i j hij).toAlgHom.comp (chartAlgHom P F j k hk) :=
      comp_cast_coordinate K (g.pullback i j hij) (F.pullback j (originalIndex P k) hF)
        ((g ≫ F).pullback i (originalIndex P k) hcomp)
        (algebraCast (originalAlgebra P k).symm) (coordinateMap P k) hp
    _ = (g.pullback i j hij).toAlgHom.comp ((toAlgebraFamily P F).map j) :=
      congrArg (g.pullback i j hij).toAlgHom.comp (toAlgebraFamily_map_eq P F j k hk).symm

omit [CompleteSpace K] in
private theorem comp_coordinate_of_square {R' S T U : PresentedAffinoidAlgebra K}
    (c : BoundedAlgHom K U S) (p : BoundedAlgHom K T U)
    (g : BoundedAlgHom K R' S) (d : BoundedAlgHom K T R')
    (a : A →ₐ[K] T) (h : c.comp p = g.comp d) :
    c.toAlgHom.comp (p.toAlgHom.comp a) = g.toAlgHom.comp (d.toAlgHom.comp a) :=
  congrArg (fun q : BoundedAlgHom K T S => q.toAlgHom.comp a) h

private theorem affinoidStrongAlgHom_precomp
    {S : PresentedAffinoidAlgebra K} (g : BoundedAlgHom K R S)
    (F : SmallAffinoidSpectrum.saturated.{u, u} R ⟶ saturated K P) :
    affinoidStrongAlgHom K P S (SmallAffinoidSpectrum.map.{u, u} g ≫ F) =
      g.toAlgHom.comp (affinoidStrongAlgHom K P R F) := by
  let E := SmallAffinoidSpectrum.map.{u, u} g
  let i := SmallAffinoidSpectrum.topIndex S
  let j := SmallAffinoidSpectrum.topIndex R
  let eS := SmallAffinoidSpectrum.top_algebra S
  let eR := SmallAffinoidSpectrum.top_algebra R
  have hE : E.baseMap '' range ((SmallAffinoidSpectrum.saturated.{u, u} S).presentation.atlas.chart i) ⊆
      range ((SmallAffinoidSpectrum.saturated.{u, u} R).presentation.atlas.chart j) :=
    (SmallAffinoidSpectrum.range_topIndex R).symm ▸ subset_univ _
  have hCast : (algebraCast eS).comp (E.pullback i j hE) = g.comp (algebraCast eR) :=
    algebraCast_square eS eR (SmallAffinoidSpectrum.map_pullbackAtTop_heq g)
  unfold affinoidStrongAlgHom
  calc
    (algebraCast eS).toAlgHom.comp ((toAlgebraFamily P (E ≫ F)).map i) =
        (algebraCast eS).toAlgHom.comp
          ((E.pullback i j hE).toAlgHom.comp ((toAlgebraFamily P F).map j)) :=
      congrArg (algebraCast eS).toAlgHom.comp (toAlgebraFamily_precomp K P E F i j hE)
    _ = g.toAlgHom.comp ((algebraCast eR).toAlgHom.comp ((toAlgebraFamily P F).map j)) :=
      comp_coordinate_of_square K (algebraCast eS) (E.pullback i j hE) g
        (algebraCast eR) ((toAlgebraFamily P F).map j) hCast

private theorem saturatedAffinoidHom_precomp
    {S : PresentedAffinoidAlgebra K} (g : BoundedAlgHom K R S) (φ : A →ₐ[K] R) :
    SmallAffinoidSpectrum.map.{u, u} g ≫ saturatedAffinoidHom K P R φ =
      saturatedAffinoidHom K P S (g.toAlgHom.comp φ) := by
  apply affinoidStrongAlgHom_injective K P S
  rw [affinoidStrongAlgHom_precomp, affinoidStrongAlgHom_saturatedAffinoidHom,
    affinoidStrongAlgHom_saturatedAffinoidHom]

/-- Precomposing with the affinoid map of a bounded algebra map
postcomposes the coordinate-algebra map with that bounded map. -/
theorem localizedAffinoidHom_precomp
    {S : PresentedAffinoidAlgebra K} (g : BoundedAlgHom K R S) (φ : A →ₐ[K] R) :
    localizationFunctor.map (SmallAffinoidSpectrum.map.{u, u} g) ≫
      localizedAffinoidHom K P R φ = localizedAffinoidHom K P S (g.toAlgHom.comp φ) := by
  change localizationFunctor.map (SmallAffinoidSpectrum.map.{u, u} g) ≫
      localizationFunctor.map (saturatedAffinoidHom K P R φ) =
    localizationFunctor.map (saturatedAffinoidHom K P S (g.toAlgHom.comp φ))
  rw [← Functor.map_comp, saturatedAffinoidHom_precomp]

/-- The two composition laws for the localized affinoid Hom comparison. -/
def LocalizedAffinoidHomNaturalityStatement : Prop :=
  (∀ {A : Type v} [CommRing A] [Algebra K A] {B : Type w} [CommRing B] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (R : PresentedAffinoidAlgebra K) (f : A →ₐ[K] B) (φ : B →ₐ[K] R),
    localizedAffinoidHom K Q R φ ≫ localizedHom K P Q f =
      localizedAffinoidHom K P R (φ.comp f)) ∧
  (∀ {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
    {R S : PresentedAffinoidAlgebra K} (g : BoundedAlgHom K R S) (φ : A →ₐ[K] R),
    localizationFunctor.map (SmallAffinoidSpectrum.map.{u, u} g) ≫
      localizedAffinoidHom K P R φ = localizedAffinoidHom K P S (g.toAlgHom.comp φ))

/-- The localized affinoid Hom comparison is natural in both arguments. -/
theorem localizedAffinoidHomNaturality : LocalizedAffinoidHomNaturalityStatement.{u, v, w} K := by
  constructor
  · intro A _ _ B _ _ P Q R f φ
    exact localizedAffinoidHom_comp K P R Q f φ
  · intro A _ _ P R S g φ
    exact localizedAffinoidHom_precomp K P R g φ

end Langlands.Analytic.AffineAnalytification
