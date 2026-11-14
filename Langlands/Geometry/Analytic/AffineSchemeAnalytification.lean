import Langlands.Geometry.Analytic.AffineAnalytificationAtlas
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Polynomial-locus analytification of genuine affine schemes -/

noncomputable section

universe u

namespace Langlands.Analytic.AffineSchemeAnalytification

open CategoryTheory _root_.AlgebraicGeometry

section Algebraic

variable {K : Type u} [CommRing K] {X : Scheme.{u}}

/-- The actual global-section ring, with its scheme structure morphism retained
in the type so that its induced scalar action is unambiguous. -/
def CoordinateRing (_f : X ⟶ Spec (CommRingCat.of K)) : Type u := Γ(X, ⊤)

instance coordinateRingCommRing (f : X ⟶ Spec (CommRingCat.of K)) :
    CommRing (CoordinateRing f) := inferInstanceAs (CommRing Γ(X, ⊤))

/-- Scalars act through global sections of the given scheme morphism. -/
instance coordinateRingAlgebra (f : X ⟶ Spec (CommRingCat.of K)) :
    Algebra K (CoordinateRing f) :=
  (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom).toAlgebra

@[simp] theorem coordinateRing_algebraMap (f : X ⟶ Spec (CommRingCat.of K)) (k : K) :
    algebraMap K (CoordinateRing f) k =
      f.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv k) := rfl

/-- Affine finite-type schemes have genuinely finitely generated global-section
algebras with this induced scalar action. -/
instance coordinateRingFiniteType (f : X ⟶ Spec (CommRingCat.of K))
    [IsAffine X] [LocallyOfFiniteType f] : Algebra.FiniteType K (CoordinateRing f) := by
  apply RingHom.finiteType_algebraMap.mp
  change (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).FiniteType
  exact (HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f inferInstance).comp
    (RingHom.FiniteType.of_surjective _
      ((Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective))

/-- The canonical affine scheme isomorphism to the spectrum of its actual
coordinate ring. -/
def coordinateIso (f : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] :
    X ≅ Spec (CommRingCat.of (CoordinateRing f)) := X.isoSpec

/-- The canonical affine isomorphism respects the specified base-field map. -/
theorem coordinateIso_hom_over (f : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] :
    (coordinateIso f).hom ≫ Spec.algebraMap K (CoordinateRing f) = f := by
  change X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop) = f
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
  have h : (Spec (CommRingCat.of K)).toSpecΓ ≫
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv = 𝟙 _ := by
    change (Spec (CommRingCat.of K)).isoSpec.hom ≫ _ = _
    rw [Scheme.isoSpec_Spec_hom, ← Spec.map_comp]
    simp
  simp only [Category.assoc, h, Category.comp_id]

/-- Choose a finite polynomial presentation of the actual global sections. -/
def presentation (f : X ⟶ Spec (CommRingCat.of K))
    [IsAffine X] [LocallyOfFiniteType f] : FinitePolynomialPresentation K (CoordinateRing f) :=
  FinitePolynomialPresentation.ofFiniteType K (CoordinateRing f)

/-- An algebraic presentation of the specified affine scheme over its base.
Only genuine algebraic data is stored; analytic outputs are constructed. -/
structure Presentation (f : X ⟶ Spec (CommRingCat.of K))
    (A : Type u) [CommRing A] [Algebra K A] where
  polynomialPresentation : FinitePolynomialPresentation K A
  schemeIso : X ≅ Spec (CommRingCat.of A)
  over_base : schemeIso.hom ≫ Spec.algebraMap K A = f

namespace Presentation

variable {A : Type u} [CommRing A] [Algebra K A]

/-- The supplied polynomial presentation presents the genuine scheme `Spec A`. -/
def forSpec (P : FinitePolynomialPresentation K A) :
    Presentation (Spec.algebraMap K A) A where
  polynomialPresentation := P
  schemeIso := Iso.refl _
  over_base := Category.id_comp _

/-- Choose a polynomial presentation for the genuine affine scheme `Spec A`. -/
def forSpecFiniteType [Algebra.FiniteType K A] :
    Presentation (Spec.algebraMap K A) A :=
  forSpec (FinitePolynomialPresentation.ofFiniteType K A)

/-- Use an explicit presentation of the actual global-section algebra. -/
def forAffine (f : X ⟶ Spec (CommRingCat.of K)) [IsAffine X]
    (P : FinitePolynomialPresentation K (CoordinateRing f)) :
    Presentation f (CoordinateRing f) where
  polynomialPresentation := P
  schemeIso := coordinateIso f
  over_base := coordinateIso_hom_over f

/-- The actual affine finite-type scheme supplies all the required algebraic data. -/
def forAffineFiniteType (f : X ⟶ Spec (CommRingCat.of K))
    [IsAffine X] [LocallyOfFiniteType f] : Presentation f (CoordinateRing f) :=
  forAffine f (presentation f)

end Presentation

end Algebraic

section Normed

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of K)}
  {A : Type u} [CommRing A] [Algebra K A]

namespace Presentation

variable (C : Presentation f A)

/-- The actual quotient algebra of a bounded polynomial locus of the scheme. -/
abbrev boundedAlgebra (r : PositivePolyradius (Fin C.polynomialPresentation.arity)) :
    PresentedAffinoidAlgebra K := PolynomialLocus.chart C.polynomialPresentation r

/-- The visible polynomial map into a bounded chart algebra. -/
abbrev boundedPolynomialMap (r : PositivePolyradius (Fin C.polynomialPresentation.arity)) :
    MvPolynomial (Fin C.polynomialPresentation.arity) K →ₐ[K] C.boundedAlgebra r :=
  PolynomialLocus.polynomialMap C.polynomialPresentation r

/-- The visible coordinate-algebra map into the full bounded chart quotient. -/
abbrev boundedAlgebraMap (r : PositivePolyradius (Fin C.polynomialPresentation.arity)) :
    A →ₐ[K] C.boundedAlgebra r :=
  PolynomialLocus.algebraMap C.polynomialPresentation r

/-- The actual chart map kills every defining polynomial relation. -/
theorem boundedPolynomialMap_relation
    (r : PositivePolyradius (Fin C.polynomialPresentation.arity))
    {p : MvPolynomial (Fin C.polynomialPresentation.arity) K}
    (hp : C.polynomialPresentation.map p = 0) :
    C.boundedPolynomialMap r p = 0 :=
  PolynomialLocus.polynomialMap_relation C.polynomialPresentation r hp

@[simp] theorem boundedAlgebraMap_map
    (r : PositivePolyradius (Fin C.polynomialPresentation.arity))
    (p : MvPolynomial (Fin C.polynomialPresentation.arity) K) :
    C.boundedAlgebraMap r (C.polynomialPresentation.map p) = C.boundedPolynomialMap r p :=
  PolynomialLocus.algebraMap_map C.polynomialPresentation r p

theorem boundedAlgebraMap_comp
    (r : PositivePolyradius (Fin C.polynomialPresentation.arity)) :
    (C.boundedAlgebraMap r).comp C.polynomialPresentation.map = C.boundedPolynomialMap r :=
  PolynomialLocus.algebraMap_comp C.polynomialPresentation r

/-- The full bounded restriction between nested scheme charts. -/
abbrev boundedRestriction (r s : PositivePolyradius (Fin C.polynomialPresentation.arity))
    (hsr : ∀ i, s i ≤ r i) : BoundedAlgHom K (C.boundedAlgebra r) (C.boundedAlgebra s) :=
  PolynomialLocus.restriction C.polynomialPresentation r s hsr

@[simp] theorem boundedRestriction_polynomialMap
    (r s : PositivePolyradius (Fin C.polynomialPresentation.arity))
    (hsr : ∀ i, s i ≤ r i) (p : MvPolynomial (Fin C.polynomialPresentation.arity) K) :
    C.boundedRestriction r s hsr (C.boundedPolynomialMap r p) = C.boundedPolynomialMap s p :=
  PolynomialLocus.restriction_polynomial C.polynomialPresentation r s hsr p

@[simp] theorem boundedRestriction_algebraMap
    (r s : PositivePolyradius (Fin C.polynomialPresentation.arity))
    (hsr : ∀ i, s i ≤ r i) (a : A) :
    C.boundedRestriction r s hsr (C.boundedAlgebraMap r a) = C.boundedAlgebraMap s a :=
  PolynomialLocus.restriction_algebraMap C.polynomialPresentation r s hsr a

theorem boundedRestriction_self
    (r : PositivePolyradius (Fin C.polynomialPresentation.arity)) :
    C.boundedRestriction r r (fun _ => le_rfl) = BoundedAlgHom.id K (C.boundedAlgebra r) :=
  PolynomialLocus.restriction_self C.polynomialPresentation r

theorem boundedRestriction_trans
    (r s t : PositivePolyradius (Fin C.polynomialPresentation.arity))
    (hsr : ∀ i, s i ≤ r i) (hts : ∀ i, t i ≤ s i) :
    C.boundedRestriction r t (fun i => (hts i).trans (hsr i)) =
      (C.boundedRestriction s t hts).comp (C.boundedRestriction r s hsr) :=
  PolynomialLocus.restriction_trans C.polynomialPresentation r s hsr t hts

end Presentation

end Normed

section Cofinal

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of K)}
  {A : Type u} [CommRing A] [Algebra K A]

namespace Presentation

variable (C : Presentation f A)

/-- The actual scheme chart algebra at the `m`-th cofinal radius. -/
abbrev chartAlgebra (m : ℕ) : PresentedAffinoidAlgebra K :=
  AffineAnalytification.algebra K C.polynomialPresentation m

/-- The polynomial map into the `m`-th cofinal chart. -/
abbrev chartPolynomialMap (m : ℕ) :
    MvPolynomial (Fin C.polynomialPresentation.arity) K →ₐ[K] C.chartAlgebra m :=
  C.boundedPolynomialMap (AnalyticAffineSpace.polyradius K C.polynomialPresentation.arity m)

/-- The full coordinate-algebra map into the `m`-th cofinal chart. -/
abbrev chartAlgebraMap (m : ℕ) : A →ₐ[K] C.chartAlgebra m :=
  C.boundedAlgebraMap (AnalyticAffineSpace.polyradius K C.polynomialPresentation.arity m)

/-- The actual bounded restriction between two cofinal charts. -/
abbrev chartRestriction {m k : ℕ} (h : m ≤ k) :
    BoundedAlgHom K (C.chartAlgebra k) (C.chartAlgebra m) :=
  AffineAnalytification.restriction K C.polynomialPresentation h

omit [CompleteSpace K] in
@[simp] theorem chartRestriction_algebraMap {m k : ℕ} (h : m ≤ k) (a : A) :
    C.chartRestriction h (C.chartAlgebraMap k a) = C.chartAlgebraMap m a :=
  PolynomialLocus.restriction_algebraMap C.polynomialPresentation _ _ _ a

/-- The cofinal scheme charts with their proved actual affinoid-domain restrictions. -/
abbrev chartSystem : AffinoidChartSystem.{u, 0} K :=
  AffineAnalytification.chartSystem K C.polynomialPresentation

/-- The topological space obtained by gluing the cofinal scheme charts. -/
abbrev Space : Type u := AffineAnalytification.Space K C.polynomialPresentation

/-- The spectrum map of a cofinal scheme chart into the constructed space. -/
abbrev chart (m : ℕ) : BanachSpectrum (C.chartAlgebra m) → C.Space :=
  AffineAnalytification.chart K C.polynomialPresentation m

theorem exists_chart (z : C.Space) : ∃ m s, C.chart m s = z :=
  AffineAnalytification.exists_chart K C.polynomialPresentation z

/-- The computed affinoid atlas, selecting one original index per distinct range. -/
abbrev atlas : IndexedAffinoidAtlas.{u, u, 0} K C.Space :=
  AffineAnalytification.atlas K C.polynomialPresentation

/-- The genuine affine scheme with its constructed polynomial-locus atlas. -/
def analyticPresentation : AffinoidAtlasPresentation.{u, u, 0} K :=
  AffineAnalytification.presentation K C.polynomialPresentation

/-- The actual full-domain saturation of the scheme's constructed atlas. -/
def saturated : SaturatedAtlasPresentation.{u, u, u} K :=
  AffineAnalytification.saturated K C.polynomialPresentation

/-- The constructed scheme analytification in the existing localized category. -/
def localized : SaturatedAtlasPresentation.LocalizedCategory.{u, u, u} (K := K) :=
  AffineAnalytification.localized K C.polynomialPresentation

@[simp] theorem analyticPresentation_space :
    C.analyticPresentation.space = TopCat.of C.Space := rfl

@[simp] theorem saturated_space :
    C.saturated.presentation.space = TopCat.of C.Space := rfl

@[simp] theorem localized_space :
    SaturatedAtlasPresentation.localizedSpaceFunctor.obj C.localized = TopCat.of C.Space := rfl

end Presentation

/-- Analytification of the genuine scheme `Spec A`, using the specified actual
polynomial presentation and the identity scheme isomorphism. -/
def spec (P : FinitePolynomialPresentation K A) :
    SaturatedAtlasPresentation.LocalizedCategory.{u, u, u} (K := K) :=
  (Presentation.forSpec P).localized

/-- Analytification of `Spec A`, choosing a polynomial presentation from finite type. -/
def specFiniteType [Algebra.FiniteType K A] :
    SaturatedAtlasPresentation.LocalizedCategory.{u, u, u} (K := K) :=
  (Presentation.forSpecFiniteType (K := K) (A := A)).localized

/-- Analytification of a genuine affine scheme using a specified presentation of
its actual global sections and its canonical affine scheme isomorphism over `K`. -/
def affine (f : X ⟶ Spec (CommRingCat.of K)) [IsAffine X]
    (P : FinitePolynomialPresentation K (CoordinateRing f)) :
    SaturatedAtlasPresentation.LocalizedCategory.{u, u, u} (K := K) :=
  (Presentation.forAffine f P).localized

/-- The constructed analytification of any genuine affine finite-type scheme over `K`. -/
def affineFiniteType (f : X ⟶ Spec (CommRingCat.of K))
    [IsAffine X] [LocallyOfFiniteType f] :
    SaturatedAtlasPresentation.LocalizedCategory.{u, u, u} (K := K) :=
  (Presentation.forAffineFiniteType f).localized

end Cofinal

end Langlands.Analytic.AffineSchemeAnalytification
