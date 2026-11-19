import Langlands.Geometry.Analytic.SpaceAnalytificationSchemeStatement
import Langlands.Geometry.Analytic.EtaleOpenMap.Proof
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation
import Langlands.Geometry.Analytic.LocalizedPullbackPoints
import Langlands.Geometry.Analytic.AffineAnalytificationImmersionProof
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-! # The canonical comparison with the glued scheme analytification -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open CategoryTheory SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology (ringTest ringTestMap)
open Langlands.Analytic.AffineSchemeAnalytification Langlands.Analytic.SchemeAnalytification

section Algebraic

variable (K : Type u) [CommRing K] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of K))

/-- The test point given by the inclusion of an affine open. -/
def chartRingPoint (U : X.affineOpens) :
    RingPoints K ((schemeToSpace _).obj (Over.mk f))
      (CoordinateRing (structureMap f U)) :=
  (schemeRingPointsEquiv K (Over.mk f) _).symm
    (Over.homMk ((coordinateIso (structureMap f U)).inv ≫ (U : X.Opens).ι) (by
      change ((coordinateIso (structureMap f U)).inv ≫ (U : X.Opens).ι) ≫ f = _
      rw [Category.assoc]
      change (coordinateIso (structureMap f U)).inv ≫ structureMap f U =
        Spec.algebraMap K (CoordinateRing (structureMap f U))
      calc
        _ = (coordinateIso (structureMap f U)).inv ≫
            ((coordinateIso (structureMap f U)).hom ≫
              Spec.algebraMap K (CoordinateRing (structureMap f U))) :=
          congrArg ((coordinateIso (structureMap f U)).inv ≫ ·)
            (coordinateIso_hom_over (structureMap f U)).symm
        _ = _ := Iso.inv_hom_id_assoc _ _))

@[simp]
theorem chartRingPoint_left (U : X.affineOpens) :
    (schemeRingPointsEquiv K (Over.mk f) _ (chartRingPoint K f U)).left =
      (coordinateIso (structureMap f U)).inv ≫ (U : X.Opens).ι :=
  rfl

/-- The chart point is the unique point with its specified underlying inclusion. -/
theorem eq_chartRingPoint (U : X.affineOpens)
    (x : RingPoints K ((schemeToSpace _).obj (Over.mk f))
      (CoordinateRing (structureMap f U)))
    (hx : (schemeRingPointsEquiv K (Over.mk f) _ x).left =
      (coordinateIso (structureMap f U)).inv ≫ (U : X.Opens).ι) :
    x = chartRingPoint K f U := by
  apply (schemeRingPointsEquiv K (Over.mk f) _).injective
  exact Over.OverMorphism.ext hx

/-- Restriction of the chart point is the point of the smaller affine open. -/
theorem changeRing_chartRingPoint {U V : X.affineOpens} (h : (V : X.Opens) ≤ U) :
    RingPoints.changeRing (restriction f h) (chartRingPoint K f U) =
      chartRingPoint K f V := by
  apply (schemeRingPointsEquiv K (Over.mk f) _).injective
  apply Over.OverMorphism.ext
  change Spec.map (X.homOfLE h).appTop ≫
      ((U : Scheme).isoSpec.inv ≫ (U : X.Opens).ι) = _
  rw [Scheme.isoSpec_inv_naturality_assoc, Scheme.homOfLE_ι]
  rfl

/-- The coordinate algebra homomorphism of a point of an affine chart. -/
def chartPointAlgHom (U : X.affineOpens)
    {A : Type u} [CommRing A] [Algebra K A]
    (q : Over.mk (Spec.algebraMap K A) ⟶ Over.mk (structureMap f U)) :
    CoordinateRing (structureMap f U) →ₐ[K] A := by
  refine Spec.homEquivAlgHom ⟨q.left ≫ (coordinateIso (structureMap f U)).hom, ?_⟩
  rw [Category.assoc, coordinateIso_hom_over]
  exact Over.w q

/-- Taking the spectrum recovers the affine-chart point and its coordinates. -/
theorem spec_chartPointAlgHom (U : X.affineOpens)
    {A : Type u} [CommRing A] [Algebra K A]
    (q : Over.mk (Spec.algebraMap K A) ⟶ Over.mk (structureMap f U)) :
    Spec.map (CommRingCat.ofHom (chartPointAlgHom K f U q).toRingHom) =
      q.left ≫ (coordinateIso (structureMap f U)).hom :=
  Spec.map_preimage _

/-- Pulling the chart point back by its coordinate algebra map recovers the point. -/
theorem changeRing_chartPointAlgHom (U : X.affineOpens)
    {A : Type u} [CommRing A] [Algebra K A]
    (q : Over.mk (Spec.algebraMap K A) ⟶ Over.mk (structureMap f U)) :
    schemeRingPointsEquiv K (Over.mk f) A
      (RingPoints.changeRing (chartPointAlgHom K f U q) (chartRingPoint K f U)) =
      Langlands.AlgebraicGeometry.PointTopology.openPointMap K (Over.mk f) A U.val q := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ ((coordinateIso (structureMap f U)).inv ≫ (U : X.Opens).ι) =
    q.left ≫ (U : X.Opens).ι
  rw [← Category.assoc, spec_chartPointAlgHom, Category.assoc, Category.assoc,
    Iso.hom_inv_id_assoc]

/-- Near any prime of an affine test algebra, its point of the scheme factors
through an affine chart after one principal localization. -/
theorem exists_localized_chart_factorization
    {A : Type u} [CommRing A] [Algebra K A]
    (x : RingPoints K ((schemeToSpace _).obj (Over.mk f)) A)
    (t : PrimeSpectrum A) :
    ∃ (U : X.affineOpens) (a : A)
      (φ : CoordinateRing (structureMap f U) →ₐ[K] Localization.Away a),
      t ∈ PrimeSpectrum.basicOpen a ∧
        RingPoints.changeRing φ (chartRingPoint K f U) =
          RingPoints.changeRing (IsScalarTower.toAlgHom K A (Localization.Away a)) x := by
  let q : ringTest K A ⟶ Over.mk f := schemeRingPointsEquiv K (Over.mk f) A x
  obtain ⟨U, hU, htU, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := q.left t) (U := ⊤) (by trivial)
  let W : X.affineOpens := ⟨U, hU⟩
  obtain ⟨_, ⟨a, rfl⟩, hta, haU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      htU (U.2.preimage q.left.continuous)
  let C := Localization.Away a
  let χ : A →ₐ[K] C := IsScalarTower.toAlgHom K A C
  have hrange : Set.range ((ringTestMap K χ).left ≫ q.left) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨b, rfl⟩
    apply haU
    exact (PrimeSpectrum.localization_away_comap_range C a).le ⟨b, rfl⟩
  let l := IsOpenImmersion.lift U.ι ((ringTestMap K χ).left ≫ q.left) hrange
  have hl : l ≫ U.ι = (ringTestMap K χ).left ≫ q.left :=
    IsOpenImmersion.lift_fac _ _ _
  let q' : Over.mk (Spec.algebraMap K C) ⟶ Over.mk (structureMap f W) :=
    Over.homMk l (by
      have hq : q.left ≫ f = Spec.algebraMap K A := Over.w q
      change l ≫ (U.ι ≫ f) = _
      rw [← Category.assoc, hl, Category.assoc, hq]
      exact Over.w (ringTestMap K χ))
  refine ⟨W, a, chartPointAlgHom K f W q', hta, ?_⟩
  apply (schemeRingPointsEquiv K (Over.mk f) C).injective
  rw [changeRing_chartPointAlgHom]
  apply Over.OverMorphism.ext
  exact hl

/-- The affine intersection of two charts of a separated scheme over an affine base. -/
abbrev chartIntersection [IsSeparated f] (U V : X.affineOpens) : X.affineOpens :=
  ⟨(U : X.Opens) ⊓ (V : X.Opens), by
    have h : IsAffineHom (CategoryTheory.Limits.pullback.diagonal f) := inferInstance
    exact (isAffineHom_diagonal_iff (f := f)).mp h ⊤ (isAffineOpen_top _)
      _ (by simp) _ (by simp) U.2 V.2⟩

end Algebraic

section Normed

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
  {Y : LocalizedCategory.{u, u, u} (K := K)}
  (p : PointFamily K ((schemeToSpace _).obj (Over.mk f)) Y)
  (hp : IsAnalytification K ((schemeToSpace _).obj (Over.mk f)) Y p)

omit [IsUltrametricDist K] [CompleteSpace K] [LocallyOfFiniteType f] in
/-- The Yoneda morphism of the chart point is the represented chart inclusion. -/
theorem pointHom_chartRingPoint (U : X.affineOpens) :
    pointHom K (chartRingPoint K f U) = (schemeYoneda _).map
      (schemeRingPointsEquiv K (Over.mk f) _ (chartRingPoint K f U)) := by
  apply uliftYonedaEquiv.injective
  rfl

omit [IsUltrametricDist K] [CompleteSpace K] [LocallyOfFiniteType f] in
/-- The test point of an affine open is étale. -/
theorem isEtale_chartRingPoint (U : X.affineOpens) :
    AlgebraicSpace.IsEtale (pointHom K (chartRingPoint K f U)) := by
  rw [pointHom_chartRingPoint]
  apply isEtale_map
  change Etale ((coordinateIso (structureMap f U)).inv ≫ (U : X.Opens).ι)
  infer_instance

/-- The map attached to an affine chart, on underlying topological spaces. -/
def chartComparison (U : X.affineOpens) :
    C(LocalSpace K f U, localizedSpaceFunctor.obj Y) :=
  (localizedSpaceFunctor.map (p _ (chartPresentation K f U) (chartRingPoint K f U))).hom

include hp in
/-- Naturality makes the chart maps compatible with the gluing relation. -/
theorem chartComparison_localMap {U V : X.affineOpens} (h : (V : X.Opens) ≤ U)
    (y : LocalSpace K f V) :
    chartComparison K f p U (localMap K f h y) = chartComparison K f p V y := by
  have hn := hp.naturality (chartPresentation K f U) (chartPresentation K f V)
    (restriction f h) (chartRingPoint K f U)
  rw [changeRing_chartRingPoint] at hn
  have ht := congrArg (fun q : AffineAnalytification.localized K
    (chartPresentation K f V) ⟶ Y => localizedSpaceFunctor.map q) hn
  rw [Functor.map_comp,
    AffineAnalytification.localizedSpaceFunctor_map_localizedHom] at ht
  exact (congrArg (fun q : TopCat.of (LocalSpace K f V) ⟶
    localizedSpaceFunctor.obj Y => q.hom y) ht).symm

/-- The canonical continuous map from the glued scheme space to an analytification. -/
def schemeComparison : C(Space K f, localizedSpaceFunctor.obj Y) :=
  desc K f (chartComparison K f p) (fun h y => chartComparison_localMap K f p hp h y)

@[simp]
theorem schemeComparison_ι (U : X.affineOpens) (y : LocalSpace K f U) :
    schemeComparison K f p hp (ι K f U y) = chartComparison K f p U y :=
  rfl

include hp in
/-- The comparison map from each affine chart is open. -/
theorem isOpenMap_chartComparison (U : X.affineOpens) :
    IsOpenMap (chartComparison K f p U) :=
  etaleOpenMap K _ (hp.etale_map (chartPresentation K f U)
    (chartRingPoint K f U) (isEtale_chartRingPoint K f U))

/-- The image of a set under the comparison is the union of its chart images. -/
theorem schemeComparison_image (s : Set (Space K f)) :
    schemeComparison K f p hp '' s =
      ⋃ U : X.affineOpens, chartComparison K f p U '' (ι K f U ⁻¹' s) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨U, w, rfl⟩ := exists_ι K f z
    exact Set.mem_iUnion.mpr ⟨U, w, hz, rfl⟩
  · intro hy
    obtain ⟨U, w, hw, rfl⟩ := Set.mem_iUnion.mp hy
    exact ⟨ι K f U w, hw, rfl⟩

/-- Étale openness on charts makes the descended comparison an open map. -/
theorem isOpenMap_schemeComparison : IsOpenMap (schemeComparison K f p hp) := by
  intro s hs
  rw [schemeComparison_image]
  exact isOpen_iUnion fun U =>
    isOpenMap_chartComparison K f p hp U _ ((isOpen_iff K f s).mp hs U)

omit [IsUltrametricDist K] [CompleteSpace K] [LocallyOfFiniteType f] in
/-- The represented affine intersection is the pullback of its two chart points. -/
theorem chartIntersection_isPullback [IsSeparated f] (U V : X.affineOpens) :
    CategoryTheory.IsPullback
      ((schemeYoneda _).map (ringTestMap K (restriction f
        (show (chartIntersection K f U V : X.Opens) ≤ U from inf_le_left))))
      ((schemeYoneda _).map (ringTestMap K (restriction f
        (show (chartIntersection K f U V : X.Opens) ≤ V from inf_le_right))))
      (pointHom K (chartRingPoint K f U)) (pointHom K (chartRingPoint K f V)) := by
  have : IsAffine (((U : X.Opens) ⊓ (V : X.Opens) : X.Opens) : Scheme) :=
    (chartIntersection K f U V).2
  rw [pointHom_chartRingPoint, pointHom_chartRingPoint]
  apply CategoryTheory.IsPullback.map
  apply CategoryTheory.IsPullback.of_map_of_faithful (F := Over.forget _)
  change CategoryTheory.IsPullback
    (Spec.map (X.homOfLE
      (show (chartIntersection K f U V : X.Opens) ≤ U from inf_le_left)).appTop)
    (Spec.map (X.homOfLE
      (show (chartIntersection K f U V : X.Opens) ≤ V from inf_le_right)).appTop)
    ((coordinateIso (structureMap f U)).inv ≫ (U : X.Opens).ι)
    ((coordinateIso (structureMap f V)).inv ≫ (V : X.Opens).ι)
  refine (isPullback_opens_inf (U : X.Opens) (V : X.Opens)).of_iso
    (coordinateIso (structureMap f (chartIntersection K f U V)))
    (coordinateIso (structureMap f U)) (coordinateIso (structureMap f V))
    (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Scheme.isoSpec_hom_naturality _).symm
  · exact (Scheme.isoSpec_hom_naturality _).symm
  · simp only [Iso.refl_hom, Category.comp_id]
    exact (Iso.hom_inv_id_assoc (coordinateIso (structureMap f U)) (U : X.Opens).ι).symm
  · simp only [Iso.refl_hom, Category.comp_id]
    exact (Iso.hom_inv_id_assoc (coordinateIso (structureMap f V)) (V : X.Opens).ι).symm

include hp in
/-- Equal analytic chart images are identified by the scheme gluing relation. -/
theorem ι_eq_of_chartComparison_eq [IsSeparated f]
    (U V : X.affineOpens) (x : LocalSpace K f U) (y : LocalSpace K f V)
    (hxy : chartComparison K f p U x = chartComparison K f p V y) :
    ι K f U x = ι K f V y := by
  let W := chartIntersection K f U V
  have h := hp.isPullback (chartPresentation K f U) (chartPresentation K f V)
    (chartPresentation K f W)
    (restriction f (show (W : X.Opens) ≤ U from inf_le_left))
    (restriction f (show (W : X.Opens) ≤ V from inf_le_right))
    (chartRingPoint K f U) (chartRingPoint K f V) (chartIntersection_isPullback K f U V)
  obtain ⟨z, hz₁, hz₂⟩ := exists_point_of_isPullback _ _ _ _ h x y hxy
  change LocalSpace K f W at z
  rw [AffineAnalytification.localizedSpaceFunctor_map_localizedHom] at hz₁ hz₂
  change localMap K f (show (W : X.Opens) ≤ U from inf_le_left) z = x at hz₁
  change localMap K f (show (W : X.Opens) ≤ V from inf_le_right) z = y at hz₂
  rw [← hz₁, ← hz₂]
  exact (ι_localMap K f (U := U) (V := W) inf_le_left z).trans
    (ι_localMap K f (U := V) (V := W) inf_le_right z).symm

/-- The comparison is injective for a separated scheme. -/
theorem injective_schemeComparison [IsSeparated f] :
    Function.Injective (schemeComparison K f p hp) := by
  intro x y hxy
  obtain ⟨U, x, rfl⟩ := exists_ι K f x
  obtain ⟨V, y, rfl⟩ := exists_ι K f y
  exact ι_eq_of_chartComparison_eq K f p hp U V x y hxy

include hp in
omit [LocallyOfFiniteType f] in
/-- Naturality on the underlying points of arbitrary affine test algebras. -/
theorem pointFamily_naturality_apply
    {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (φ : A →ₐ[K] B) (x : RingPoints K ((schemeToSpace _).obj (Over.mk f)) A)
    (z : AffineAnalytification.Space K Q) :
    localizedSpaceFunctor.map (p B Q (RingPoints.changeRing φ x)) z =
      localizedSpaceFunctor.map (p A P x) (AffineAnalytification.baseMap K P Q φ z) := by
  rw [hp.naturality P Q φ x, Functor.map_comp,
    AffineAnalytification.localizedSpaceFunctor_map_localizedHom]
  rfl

/-- Every point in an analytification is the image of a point in an affine chart. -/
theorem surjective_schemeComparison :
    Function.Surjective (schemeComparison K f p hp) := by
  intro y
  obtain ⟨A, _, _, P, x, _, z, rfl⟩ := hp.jointly_surjective y
  obtain ⟨U, a, φ, ha, hφ⟩ := exists_localized_chart_factorization K f x
    (AffineAnalytification.center K P z)
  let : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective P.map P.surjective
  let C := Localization.Away a
  let Q := FinitePolynomialPresentation.ofFiniteType K C
  let χ : A →ₐ[K] C := IsScalarTower.toAlgHom K A C
  have hz : z ∈ Set.range (AffineAnalytification.baseMap K P Q χ) := by
    rw [AffineAnalytification.ImmersionComparison.range_baseMap_away K P Q a]
    exact (AffineAnalytification.center_mem_basicOpen K P z a).mp ha
  obtain ⟨w, hw⟩ := hz
  refine ⟨ι K f U (AffineAnalytification.baseMap K (chartPresentation K f U) Q φ w), ?_⟩
  rw [schemeComparison_ι]
  change localizedSpaceFunctor.map (p _ (chartPresentation K f U) (chartRingPoint K f U))
    (AffineAnalytification.baseMap K (chartPresentation K f U) Q φ w) = _
  rw [← pointFamily_naturality_apply K f p hp (chartPresentation K f U) Q φ
    (chartRingPoint K f U) w, hφ,
    pointFamily_naturality_apply K f p hp P Q χ x w, hw]

omit [IsUltrametricDist K] [CompleteSpace K] [LocallyOfFiniteType f] in
/-- The chart-coordinate map agrees with the algebraic point used for rational points. -/
theorem chartPointAlgHom_eq_affineAlgPoint (U : X.affineOpens)
    (q : Over.mk (Spec.algebraMap K K) ⟶ Over.mk (structureMap f U)) :
    chartPointAlgHom K f U q =
      (affineAlgPoint K f U q).toAlgHom := by
  apply AlgHom.coe_ringHom_injective
  suffices h : CommRingCat.ofHom (chartPointAlgHom K f U q).toRingHom =
      CommRingCat.ofHom (affineAlgPoint K f U q).toAlgHom.toRingHom by
    exact congrArg (fun g => g.hom) h
  apply Spec.map_injective
  rw [spec_chartPointAlgHom]
  have he : CommRingCat.ofHom (affineAlgPoint K f U q).toAlgHom.toRingHom =
      CommRingCat.ofHom
        (Langlands.AlgebraicGeometry.PointTopology.affineSchemePointEquiv K
          (Over.mk (structureMap f U)) K q).toAlgHom.toRingHom := rfl
  rw [he]
  exact (Langlands.AlgebraicGeometry.PointTopology.affineSchemePointEquiv_spec K
    (X := Over.mk (structureMap f U)) K q).symm

omit [LocallyOfFiniteType f] in
/-- The seminorm of an algebraic rational point evaluates by the ground-field norm. -/
theorem comparison_pointSeminorm_analyticPoint
    {A : Type u} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
    (φ : Langlands.AlgebraicGeometry.PointTopology.AlgPoint K A K) (a : A) :
    AffineAnalytification.pointSeminorm K P (AffineAnalytification.analyticPoint K P φ) a =
      ‖φ a‖ := by
  rw [AffineAnalytification.analyticPoint, AffineAnalytification.pointSeminorm_chart,
    AffineAnalytification.chartSeminorm_apply, AffineAnalytification.spectrumPoint_apply,
    AffineAnalytification.character_algebraMap]

/-- Algebra maps carry analytic rational points to the corresponding composite points. -/
theorem comparison_baseMap_analyticPoint
    {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (φ : A →ₐ[K] B) (q : Langlands.AlgebraicGeometry.PointTopology.AlgPoint K B K) :
    AffineAnalytification.baseMap K P Q φ (AffineAnalytification.analyticPoint K Q q) =
      AffineAnalytification.analyticPoint K P
        (Langlands.AlgebraicGeometry.PointTopology.AlgPoint.precomp φ q) := by
  apply AffineAnalytification.SeminormComparison.pointSeminorm_injective K P
  ext a
  rw [AffineAnalytification.pointSeminorm_baseMap,
    comparison_pointSeminorm_analyticPoint, comparison_pointSeminorm_analyticPoint]
  rfl

/-- The canonical comparison sends a scheme rational point to its point in the
supplied analytification, for every presentation of the ground field. -/
theorem schemeComparison_analyticRationalPoint
    (P₀ : FinitePolynomialPresentation K K)
    (x : RingPoints K ((schemeToSpace _).obj (Over.mk f)) K) :
    schemeComparison K f p hp
      (analyticRationalPoint K f (schemeRingPointsEquiv K (Over.mk f) K x)) =
        rationalPoint p P₀ x := by
  let q₀ := schemeRingPointsEquiv K (Over.mk f) K x
  let U := pointAffine K f q₀
  let q := pointLift K f q₀
  let φ := chartPointAlgHom K f U q
  have hx : RingPoints.changeRing φ (chartRingPoint K f U) = x := by
    apply (schemeRingPointsEquiv K (Over.mk f) K).injective
    exact (changeRing_chartPointAlgHom K f U q).trans (openPointMap_pointLift K f q₀)
  have he : Langlands.AlgebraicGeometry.PointTopology.AlgPoint.precomp φ
      (Langlands.AlgebraicGeometry.PointTopology.AlgPoint.ofAlgHom (AlgHom.id K K)) =
        affineAlgPoint K f U q := by
    ext a
    change chartPointAlgHom K f U q a = (affineAlgPoint K f U q).toAlgHom a
    exact AlgHom.congr_fun (chartPointAlgHom_eq_affineAlgPoint K f U q) a
  have hn := pointFamily_naturality_apply K f p hp (chartPresentation K f U) P₀ φ
    (chartRingPoint K f U)
    (AffineAnalytification.analyticPoint K P₀
      (Langlands.AlgebraicGeometry.PointTopology.AlgPoint.ofAlgHom (AlgHom.id K K)))
  rw [hx, comparison_baseMap_analyticPoint, he] at hn
  exact hn.symm

/-- The continuous, open bijection identifies the glued scheme space with the
underlying space of any analytification of its represented algebraic space. -/
def schemeComparisonHomeomorph [IsSeparated f] :
    Space K f ≃ₜ localizedSpaceFunctor.obj Y :=
  (Equiv.ofBijective (schemeComparison K f p hp)
    ⟨injective_schemeComparison K f p hp, surjective_schemeComparison K f p hp⟩
    ).toHomeomorphOfContinuousOpen (schemeComparison K f p hp).continuous
      (isOpenMap_schemeComparison K f p hp)

end Normed

/-- The separated-scheme comparison, including the chart and rational-point
identities, in every universe. -/
theorem spaceAnalytificationScheme : SpaceAnalytificationSchemeStatement.{u} := by
  intro K _ _ _ X f _ _ Y p hp
  let e := schemeComparisonHomeomorph K f p hp
  refine ⟨e.symm, ?_, ?_⟩
  · intro U x hx y
    have hx' := eq_chartRingPoint K f U x hx
    subst x
    change e.symm (e (ι K f U y)) = _
    exact e.symm_apply_apply _
  · intro P₀ x
    apply e.injective
    rw [e.apply_symm_apply]
    exact (schemeComparison_analyticRationalPoint K f p hp P₀ x).symm

end Langlands.Analytic.SpaceAnalytification
