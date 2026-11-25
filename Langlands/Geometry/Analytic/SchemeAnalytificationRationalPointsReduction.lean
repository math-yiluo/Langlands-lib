import Langlands.Geometry.Analytic.SchemeAnalytificationRationalPointsStatement
import Langlands.Geometry.Analytic.AffineAnalytificationRationalPointNaturalityStatement
import Langlands.Geometry.Analytic.AnalytificationCenter
import Mathlib.Topology.LocalAtTarget

noncomputable section

universe u

namespace Langlands.Analytic.SchemeAnalytification

open CategoryTheory _root_.AlgebraicGeometry Topology
open Langlands.Analytic.AffineSchemeAnalytification Langlands.AlgebraicGeometry.PointTopology

namespace RationalPointsComparison

section Algebraic

variable {K : Type u} [CommRing K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K))

/-- Inclusion between affine open subschemes, as a relative morphism. -/
def openInclusion {U V : X.affineOpens} (h : (V : X.Opens) ≤ U) :
    openOver K (Over.mk f) V.val ⟶ openOver K (Over.mk f) U.val :=
  Over.homMk (X.homOfLE h) (by
    change X.homOfLE h ≫ ((U : X.Opens).ι ≫ f) = (V : X.Opens).ι ≫ f
    rw [← Category.assoc, Scheme.homOfLE_ι])

/-- Relative open inclusions commute with the map to the original point space. -/
theorem openPointMap_inclusion {U V : X.affineOpens} (h : (V : X.Opens) ≤ U)
    (q : RingPoint K (openOver K (Over.mk f) V.val) K) :
    openPointMap K (Over.mk f) K U.val (q ≫ openInclusion f h) =
      openPointMap K (Over.mk f) K V.val q := by
  apply RingPoint.ext
  change (q.left ≫ X.homOfLE h) ≫ (U : X.Opens).ι = q.left ≫ (V : X.Opens).ι
  erw [Category.assoc, Scheme.homOfLE_ι]

end Algebraic

section Field

variable {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K))

/-- Two affine factorizations of the same field point have a common affine refinement. -/
theorem exists_common_affine_lift (U V : X.affineOpens)
    (q : RingPoint K (openOver K (Over.mk f) U.val) K)
    (r : RingPoint K (openOver K (Over.mk f) V.val) K)
    (h : openPointMap K (Over.mk f) K U.val q =
      openPointMap K (Over.mk f) K V.val r) :
    ∃ (W : X.affineOpens) (hU : (W : X.Opens) ≤ U) (hV : (W : X.Opens) ≤ V)
      (s : RingPoint K (openOver K (Over.mk f) W.val) K),
      s ≫ openInclusion f hU = q ∧ s ≫ openInclusion f hV = r := by
  let p := openPointMap K (Over.mk f) K U.val q
  have hpU : p.left (IsLocalRing.closedPoint K) ∈ (U : X.Opens) :=
    (q.left (IsLocalRing.closedPoint K)).property
  have hpV : p.left (IsLocalRing.closedPoint K) ∈ (V : X.Opens) := by
    change (openPointMap K (Over.mk f) K U.val q).left _ ∈ _
    rw [h]
    exact (r.left (IsLocalRing.closedPoint K)).property
  obtain ⟨W, hW, hpW, hWU⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := p.left (IsLocalRing.closedPoint K)) (U := U.val ⊓ V.val) ⟨hpU, hpV⟩
  let s := openPointLift K (Over.mk f) K W p
    ((range_subset_open_iff_closedPoint K (Over.mk f) K W p).mpr hpW)
  refine ⟨⟨W, hW⟩, le_trans hWU inf_le_left, le_trans hWU inf_le_right, s, ?_, ?_⟩
  · apply openPointMap_injective K (Over.mk f) K U.val
    exact (openPointMap_inclusion f (U := U) (V := ⟨W, hW⟩)
      (le_trans hWU inf_le_left) s).trans (openPointMap_lift K (Over.mk f) K W p _)
  · apply openPointMap_injective K (Over.mk f) K V.val
    exact (openPointMap_inclusion f (U := V) (V := ⟨W, hW⟩)
      (le_trans hWU inf_le_right) s).trans ((openPointMap_lift K (Over.mk f) K W p _).trans h)

end Field

section Normed

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]

omit [IsUltrametricDist K] [CompleteSpace K] [LocallyOfFiniteType f] in
/-- On algebra points, inclusion of affine opens is restriction of global sections. -/
theorem affineAlgPoint_inclusion {U V : X.affineOpens} (h : (V : X.Opens) ≤ U)
    (q : RingPoint K (openOver K (Over.mk f) V.val) K) :
    affineAlgPoint K f U (q ≫ openInclusion f h) =
      AlgPoint.precomp (restriction f h) (affineAlgPoint K f V q) := by
  let : IsAffine (openOver K (Over.mk f) U.val).left := U.property
  let : IsAffine (openOver K (Over.mk f) V.val).left := V.property
  unfold affineAlgPoint
  erw [affineSchemePointEquiv_natural]
  ext a
  rfl

/-- The affine algebra-point comparison is a homeomorphism for the evaluation topology. -/
def affineAlgPointHomeomorph (U : X.affineOpens) :
    letI : IsAffine (openOver K (Over.mk f) U.val).left := U.property
    RingPoint K (openOver K (Over.mk f) U.val) K ≃ₜ
      AlgPoint K (CoordinateRing (structureMap f U)) K :=
  letI : IsAffine (openOver K (Over.mk f) U.val).left := U.property
  (affineSchemePointHomeomorph K (openOver K (Over.mk f) U.val) K).trans
    (AlgPoint.congr (coordinateAlgEquiv (structureMap f U)).symm)

omit [IsUltrametricDist K] [CompleteSpace K] [LocallyOfFiniteType f] in
@[simp] theorem affineAlgPointHomeomorph_apply (U : X.affineOpens)
    (q : RingPoint K (openOver K (Over.mk f) U.val) K) :
    affineAlgPointHomeomorph K f U q = affineAlgPoint K f U q := rfl

/-- Evaluation of the seminorm associated with an algebraic rational point. -/
theorem pointSeminorm_analyticPoint {A : Type u} [CommRing A] [Algebra K A]
    (P : FinitePolynomialPresentation K A) (φ : AlgPoint K A K) (a : A) :
    AffineAnalytification.pointSeminorm K P (AffineAnalytification.analyticPoint K P φ) a =
      ‖φ a‖ := by
  rw [AffineAnalytification.analyticPoint, AffineAnalytification.pointSeminorm_chart,
    AffineAnalytification.chartSeminorm_apply, AffineAnalytification.spectrumPoint_apply,
    AffineAnalytification.character_algebraMap]

/-- The center in an affine spectrum is the image of the closed point of `Spec K`.
This is the direct rational-center argument. -/
theorem localCenterPoint_localAnalyticPoint (U : X.affineOpens)
    (q : RingPoint K (openOver K (Over.mk f) U.val) K) :
    localCenterPoint K f U (localAnalyticPoint K f U q) =
      (q.left ≫ (U : X.Opens).toScheme.isoSpec.hom) (IsLocalRing.closedPoint K) := by
  let : IsAffine (openOver K (Over.mk f) U.val).left := U.property
  dsimp only [RingPoint] at q
  have hs := affineSchemePointEquiv_spec K K q
  have he : CommRingCat.ofHom (affineAlgPoint K f U q).toAlgHom.toRingHom =
      CommRingCat.ofHom (affineSchemePointEquiv K
        (openOver K (Over.mk f) U.val) K q).toAlgHom.toRingHom := rfl
  change localCenterPoint K f U (localAnalyticPoint K f U q) =
    (q.left ≫ (openOver K (Over.mk f) U.val).left.isoSpec.hom) (IsLocalRing.closedPoint K)
  erw [← hs, ← he]
  apply PrimeSpectrum.ext
  ext a
  change a ∈ (AffineAnalytification.center K (chartPresentation K f U)
      (AffineAnalytification.analyticPoint K (chartPresentation K f U)
        (affineAlgPoint K f U q))).asIdeal ↔ _
  erw [AffineAnalytification.center_asIdeal, AffineAnalytification.mem_kernel,
    pointSeminorm_analyticPoint, norm_eq_zero]
  change _ ↔ (affineAlgPoint K f U q) a ∈ (IsLocalRing.closedPoint K).asIdeal
  simp [IsLocalRing.closedPoint]
  rfl

/-- The local center is the underlying scheme point of the rational point. -/
theorem localCenter_localAnalyticPoint (U : X.affineOpens)
    (q : RingPoint K (openOver K (Over.mk f) U.val) K) :
    localCenter K f U (localAnalyticPoint K f U q) =
      (openPointMap K (Over.mk f) K U.val q).left (IsLocalRing.closedPoint K) := by
  dsimp only [RingPoint] at q
  erw [localCenter_apply, localCenterPoint_localAnalyticPoint, affineOpenMap]
  have he : (q.left ≫ (U : X.Opens).toScheme.isoSpec.hom) ≫
      ((U : X.Opens).toScheme.isoSpec.inv ≫ (U : X.Opens).ι) =
      q.left ≫ (U : X.Opens).ι := by
    erw [Category.assoc, Iso.hom_inv_id_assoc]
  exact congrArg (fun g : Spec (CommRingCat.of K) ⟶ X =>
    g (IsLocalRing.closedPoint K)) he

/-- The center of the chosen-chart rational point is its underlying scheme point. -/
theorem center_analyticRationalPoint (p : RingPoint K (Over.mk f) K) :
    center K f (analyticRationalPoint K f p) = p.left (IsLocalRing.closedPoint K) := by
  rw [analyticRationalPoint_def, center_ι, localCenter_localAnalyticPoint,
    openPointMap_pointLift]

variable (hnat : AffineAnalytification.AffineAnalytificationRationalPointNaturalityStatement.{u,u,u})
include hnat

/-- Affine analytic points commute with the restriction maps between affine opens. -/
theorem localAnalyticPoint_inclusion {U V : X.affineOpens} (h : (V : X.Opens) ≤ U)
    (q : RingPoint K (openOver K (Over.mk f) V.val) K) :
    localMap K f h (localAnalyticPoint K f V q) =
      localAnalyticPoint K f U (q ≫ openInclusion f h) := by
  unfold localAnalyticPoint localMap
  rw [hnat, affineAlgPoint_inclusion]

/-- Two affine factorizations compute the same point of the glued analytification. -/
theorem iota_localAnalyticPoint_eq (U V : X.affineOpens)
    (q : RingPoint K (openOver K (Over.mk f) U.val) K)
    (r : RingPoint K (openOver K (Over.mk f) V.val) K)
    (h : openPointMap K (Over.mk f) K U.val q =
      openPointMap K (Over.mk f) K V.val r) :
    ι K f U (localAnalyticPoint K f U q) = ι K f V (localAnalyticPoint K f V r) := by
  obtain ⟨W, hU, hV, s, hsU, hsV⟩ := exists_common_affine_lift f U V q r h
  rw [← hsU, ← hsV, ← localAnalyticPoint_inclusion K f hnat hU,
    ← localAnalyticPoint_inclusion K f hnat hV, ι_localMap, ι_localMap]

/-- The chosen-chart construction agrees with computation in every affine open. -/
theorem chart_independence (U : X.affineOpens)
    (q : RingPoint K (openOver K (Over.mk f) U.val) K) :
    analyticRationalPoint K f (openPointMap K (Over.mk f) K U.val q) =
      ι K f U (localAnalyticPoint K f U q) := by
  unfold analyticRationalPoint
  apply iota_localAnalyticPoint_eq K f hnat
  exact openPointMap_pointLift K f _

/-- The rational image in the glued space is the union of all affine rational images. -/
theorem range_analyticRationalPoint :
    Set.range (analyticRationalPoint K f) =
      ⋃ U : X.affineOpens,
        ι K f U '' Set.range (AffineAnalytification.analyticPoint K (chartPresentation K f U)) := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact Set.mem_iUnion.mpr ⟨pointAffine K f p,
      localAnalyticPoint K f (pointAffine K f p) (pointLift K f p),
      ⟨affineAlgPoint K f (pointAffine K f p) (pointLift K f p), rfl⟩, rfl⟩
  · intro hz
    obtain ⟨U, y, ⟨φ, rfl⟩, rfl⟩ := Set.mem_iUnion.mp hz
    obtain ⟨q, hq⟩ := (affineAlgPointHomeomorph K f U).surjective φ
    refine ⟨openPointMap K (Over.mk f) K U.val q, ?_⟩
    rw [chart_independence K f hnat]
    change ι K f U (AffineAnalytification.analyticPoint K (chartPresentation K f U)
      (affineAlgPointHomeomorph K f U q)) = _
    rw [hq]

variable (haff : ∀ (A : Type u) [CommRing A] [Algebra K A]
  (P : FinitePolynomialPresentation K A), IsEmbedding (AffineAnalytification.analyticPoint K P))
include haff

omit hnat in
/-- The local rational point map is an embedding by the affine comparison. -/
theorem isEmbedding_localAnalyticPoint (U : X.affineOpens) :
    letI : IsAffine (openOver K (Over.mk f) U.val).left := U.property
    IsEmbedding (localAnalyticPoint K f U) := by
  let : IsAffine (openOver K (Over.mk f) U.val).left := U.property
  exact (haff _ (chartPresentation K f U)).comp
    (affineAlgPointHomeomorph K f U).isEmbedding

/-- Continuity follows from the final topology on actual scheme points. -/
theorem continuous_analyticRationalPoint :
    Continuous[schemePointTopology K (Over.mk f) K, inferInstance] (analyticRationalPoint K f) := by
  rw [schemePointTopology, continuous_iSup_dom]
  intro U
  rw [continuous_coinduced_dom]
  have heq : analyticRationalPoint K f ∘ openPointMap K (Over.mk f) K U.val =
      ι K f U ∘ localAnalyticPoint K f U := funext (chart_independence K f hnat U)
  rw [heq]
  exact (ι K f U).continuous.comp (isEmbedding_localAnalyticPoint K f haff U).continuous

/-- The rational point map is an embedding once the analytic affine charts are open
embeddings. -/
theorem isEmbedding_analyticRationalPoint
    (hiota : ∀ U : X.affineOpens, IsOpenEmbedding (ι K f U)) :
    @IsEmbedding _ _ (schemePointTopology K (Over.mk f) K) _ (analyticRationalPoint K f) := by
  let : TopologicalSpace (RingPoint K (Over.mk f) K) := schemePointTopology K (Over.mk f) K
  let Uan : X.affineOpens → TopologicalSpace.Opens (Space K f) :=
    fun U => ⟨Set.range (ι K f U), (hiota U).isOpen_range⟩
  let V : X.affineOpens → Type u := fun U => RingPoint K (openOver K (Over.mk f) U.val) K
  let (U : X.affineOpens) : IsAffine (openOver K (Over.mk f) U.val).left := U.property
  refine isEmbedding_of_iSup_eq_top_of_preimage_subset_range
    (analyticRationalPoint K f) (continuous_analyticRationalPoint K f hnat haff)
    Uan ?_ V (fun U => openPointMap K (Over.mk f) K U.val)
      (fun U => schemePointTopology_continuous_chart K (Over.mk f) K U) ?_ ?_
  · rintro _ ⟨p, rfl⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨pointAffine K f p, analyticRationalPoint_mem_range K f p⟩
  · intro U p hp
    obtain ⟨y, hy⟩ := hp
    have hpc : p.left (IsLocalRing.closedPoint K) ∈ (U : X.Opens) := by
      rw [← center_analyticRationalPoint K f p, ← hy]
      exact center_ι_mem K f U y
    have hpU := (range_subset_open_iff_closedPoint K (Over.mk f) K U.val p).mpr hpc
    exact ⟨openPointLift K (Over.mk f) K U.val p hpU,
      openPointMap_lift K (Over.mk f) K U.val p hpU⟩
  · intro U
    have heq : analyticRationalPoint K f ∘ openPointMap K (Over.mk f) K U.val =
        ι K f U ∘ localAnalyticPoint K f U := funext (chart_independence K f hnat U)
    rw [heq]
    exact (hiota U).isEmbedding.comp (isEmbedding_localAnalyticPoint K f haff U)

end Normed

end RationalPointsComparison

end Langlands.Analytic.SchemeAnalytification
