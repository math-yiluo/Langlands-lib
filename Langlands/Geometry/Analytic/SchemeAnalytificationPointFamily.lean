import Langlands.Geometry.Analytic.SchemeAnalytificationAffineTests
import Langlands.Geometry.Analytic.SchemeAnalytificationEtaleSite
import Langlands.Geometry.Analytic.SchemeAnalytificationPullbacks

/-! # The point family of a localized scheme analytification -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Analytic.SchemeAnalytification

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open SaturatedAtlasPresentation AffineAnalytification AffineSchemeAnalytification Localized
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology (ringTest ringTestMap)
open SpaceAnalytification (PointFamily pointHom IsAnalytification chartRingPoint chartRingPoint_left
  isEtale_chartRingPoint)

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (X : (separatedLocallyFiniteTypeOver K).FullSubcategory)

local notation "Xspace" => Functor.obj (schemeToSpace (Spec (CommRingCat.of K)))
  (ObjectProperty.FullSubcategory.obj X)
local notation "Xan" => Functor.obj (localizedAnalytification K) X

private abbrev affineTestArrow {A : Type u} [CommRing A] [Algebra K A]
    (P : FinitePolynomialPresentation K A) (x : RingPoints K Xspace A) : affineTestObject K P ⟶ X :=
  ObjectProperty.homMk (schemeRingPointsEquiv K X.obj A x)

/-- An affine point of the represented algebraic space gives its actual localized
analytic map, using the polynomial-locus comparison on the source test. -/
def schemePointFamily : PointFamily K Xspace Xan :=
  fun _ _ _ P x => (affineTestIso K P).hom ≫ (localizedAnalytification K).map (affineTestArrow K X P x)

private theorem schemePointFamily_naturality {A B : Type u} [CommRing A] [Algebra K A] [CommRing B]
    [Algebra K B] (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (φ : A →ₐ[K] B) (x : RingPoints K Xspace A) :
    schemePointFamily K X B Q (RingPoints.changeRing φ x) =
      localizedHom K P Q φ ≫ schemePointFamily K X A P x := by
  let g : affineTestObject K Q ⟶ affineTestObject K P := ObjectProperty.homMk (ringTestMap K φ)
  have h : affineTestArrow K X Q (RingPoints.changeRing φ x) = g ≫ affineTestArrow K X P x :=
    (separatedLocallyFiniteTypeOver K).ι.map_injective (schemeRingPointsEquiv_changeRing φ x)
  simp only [schemePointFamily, h, Functor.map_comp, ← Category.assoc]
  rw [affineTestIso_naturality K P Q φ]

private theorem schemePointFamily_etale (hSmall : StrongEtaleSmallIndexComparisonStatement.{u})
    {A : Type u} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
    (x : RingPoints K Xspace A) (hx : AlgebraicSpace.IsEtale (pointHom K x)) :
    etale (schemePointFamily K X A P x) := by
  let g := affineTestArrow K X P x
  have ht : AlgebraicSpace.IsEtale ((schemeYoneda _).map g.hom) := hx
  let : Etale g.hom.left := MorphismProperty.of_relative_map
    (P := (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget _))) ht
  let : LocallyOfFiniteType (affineTestObject K P).obj.hom := (affineTestObject K P).property.1
  let : IsSeparated (affineTestObject K P).obj.hom := (affineTestObject K P).property.2
  let : LocallyOfFiniteType X.obj.hom := X.property.1
  let : IsSeparated X.obj.hom := X.property.2
  exact etale_comp (etale_of_isIso (affineTestIso K P).hom)
    (Localized.etale_map K _ X.obj.hom hSmall g.hom.left (Over.w g.hom))

private theorem schemePointFamily_jointlySurjective (y : localizedSpaceFunctor.obj Xan) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra K A) (P : FinitePolynomialPresentation K A)
      (x : RingPoints K Xspace A), AlgebraicSpace.IsEtale (pointHom K x) ∧
        y ∈ Set.range (localizedSpaceFunctor.map (schemePointFamily K X A P x)) := by
  let Y := X.obj.left
  let f := X.obj.hom
  let : LocallyOfFiniteType f := X.property.1
  let : IsSeparated f := X.property.2
  let z : Space K f := y
  obtain ⟨U₀, ha, hz, _⟩ := exists_isAffineOpen_mem_and_subset (x := center K f z) (U := ⊤) trivial
  let U : Y.affineOpens := ⟨U₀, ha⟩
  let : IsAffine (U : Scheme.{u}) := ha
  let A := CoordinateRing (structureMap f U)
  let P := chartPresentation K f U
  let x : RingPoints K Xspace A := chartRingPoint K f U
  let g := affineTestArrow K X P x
  have he : AlgebraicSpace.IsEtale (pointHom K x) := isEtale_chartRingPoint K f U
  let T := affineTestObject K P
  let : LocallyOfFiniteType T.obj.hom := T.property.1
  let : IsSeparated T.obj.hom := T.property.2
  obtain ⟨w, hw⟩ : z ∈ Set.range (MorphismExistence.analytification K T.obj.hom f g.hom.left (Over.w g.hom)) := by
    rw [range_analytification K T.obj.hom f g.hom.left (Over.w g.hom)]
    let p : U₀ := ⟨center K f z, hz⟩
    let e := coordinateIso (structureMap f U)
    refine ⟨e.hom p, ?_⟩
    have hg : g.hom.left = e.inv ≫ U₀.ι := chartRingPoint_left K f U
    calc
      g.hom.left (e.hom p) = (e.inv ≫ U₀.ι) (e.hom p) :=
        congrArg (fun k : T.obj.left ⟶ Y => k (e.hom p)) hg
      _ = center K f z :=
        congrArg (fun k : (U₀ : Scheme.{u}) ⟶ Y => k p) (Iso.hom_inv_id_assoc e U₀.ι)
  have hw' : localizedSpaceFunctor.map ((localizedAnalytification K).map g) w = y := by
    change (localizedSpaceFunctor.map (Localized.map K T.obj.hom f g.hom.left (Over.w g.hom))).hom w = z
    rw [Localized.underlying_map]
    exact hw
  let w₀ : localizedSpaceFunctor.obj ((localizedAnalytification K).obj (affineTestObject K P)) := w
  let a := localizedSpaceFunctor.mapIso (affineTestIso K P)
  have hₐ : a.hom (a.inv w₀) = w₀ := by
    rw [← TopCat.comp_app, Iso.inv_hom_id, TopCat.id_app]
  refine ⟨A, inferInstance, inferInstance, P, x, he, a.inv w₀, ?_⟩
  rw [schemePointFamily, Functor.map_comp, TopCat.comp_app]
  change localizedSpaceFunctor.map ((localizedAnalytification K).map g) (a.hom (a.inv w₀)) = y
  rw [hₐ]
  exact hw'

private theorem schemePointFamily_isPullback {A B C : Type u}
    [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] [CommRing C] [Algebra K C]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (R : FinitePolynomialPresentation K C) (f : A →ₐ[K] C) (g : B →ₐ[K] C)
    (x : RingPoints K Xspace A) (y : RingPoints K Xspace B)
    (h : IsPullback ((schemeYoneda _).map (ringTestMap K f)) ((schemeYoneda _).map (ringTestMap K g))
      (pointHom K x) (pointHom K y)) :
    IsPullback (localizedHom K P R f) (localizedHom K Q R g) (schemePointFamily K X A P x)
      (schemePointFamily K X B Q y) := by
  let p : affineTestObject K R ⟶ affineTestObject K P := ObjectProperty.homMk (ringTestMap K f)
  let q : affineTestObject K R ⟶ affineTestObject K Q := ObjectProperty.homMk (ringTestMap K g)
  let a := affineTestArrow K X P x
  let b := affineTestArrow K X Q y
  have h₀ : IsPullback p.hom q.hom a.hom b.hom := isPullback_of_map h
  have h₁ := localizedAnalytification_map_isPullback K (p := p) (q := q) (f := a) (g := b)
    (h₀.map (Over.forget _))
  exact h₁.of_iso' (affineTestIso K R) (affineTestIso K P) (affineTestIso K Q) (Iso.refl Xan)
    (affineTestIso_naturality K P R f).symm (affineTestIso_naturality K Q R g).symm
    (Category.comp_id _).symm (Category.comp_id _).symm

/-- The glued localized scheme analytification satisfies the affine-test definition of
analytification of the represented algebraic space. The small-index affine comparison
is used for preservation of étale test maps. -/
theorem isAnalytification_schemePointFamily (hSmall : StrongEtaleSmallIndexComparisonStatement.{u}) :
    IsAnalytification K Xspace Xan (schemePointFamily K X) where
  naturality := schemePointFamily_naturality K X
  etale_map := schemePointFamily_etale K X hSmall
  jointly_surjective := schemePointFamily_jointlySurjective K X
  isPullback := schemePointFamily_isPullback K X

end Langlands.Analytic.SchemeAnalytification
