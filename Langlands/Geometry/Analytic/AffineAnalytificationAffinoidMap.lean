import Langlands.Geometry.Analytic.AffineAnalytificationMap
import Langlands.Geometry.Analytic.AffinoidSpectrumAtlas

/-! # Maps from affinoid spectra to a polynomial-locus analytification -/

noncomputable section

universe u v

namespace Langlands.Analytic.AffineAnalytification

open Set Topology PresentedAffinoidAlgebra AnalyticAffineSpace AffinoidAtlasPresentation

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
  (R : PresentedAffinoidAlgebra K) (φ : A →ₐ[K] R)

/-! ## The generator values and their radius level -/

/-- The image under `φ` of the `t`-th generator of the presentation `P`. -/
def affinoidValue (t : Fin P.arity) : R :=
  φ (P.map (MvPolynomial.X t))

theorem exists_affinoidValue_le : ∃ l, ∀ t, ‖affinoidValue K P R φ t‖ ≤ radius K l := by
  obtain ⟨l, hl⟩ := exists_radius_gt K (∑ t, ‖affinoidValue K P R φ t‖)
  refine ⟨l, fun t => ?_⟩
  exact (Finset.single_le_sum (fun s _ => norm_nonneg (affinoidValue K P R φ s))
    (Finset.mem_univ t)).trans hl.le

open scoped Classical in
/-- The least radius index bounding the norms of all generator values. -/
def affinoidLevel : ℕ :=
  Nat.find (exists_affinoidValue_le K P R φ)

open scoped Classical in
theorem norm_affinoidValue_le (t : Fin P.arity) :
    ‖affinoidValue K P R φ t‖ ≤ radius K (affinoidLevel K P R φ) :=
  Nat.find_spec (exists_affinoidValue_le K P R φ) t

/-- The generator values have weighted monomials bounded by one. -/
theorem affinoidValue_hasBoundedMonomials :
    GeneralizedTateAlgebra.HasBoundedMonomials (polyradius K P.arity (affinoidLevel K P R φ))
      R (affinoidValue K P R φ) :=
  ⟨1, one_pos, fun d => by
    rw [one_mul]
    exact GeneralizedTateAlgebra.monomialValue_norm_le_weight _ _ (norm_one_le K _) _
      (norm_affinoidValue_le K P R φ) d⟩

/-! ## The bounded chart map -/

variable [CompleteSpace K]

/-- Weighted Tate evaluation at the generator values. -/
def affinoidTateMap :
    BoundedAlgHom K (GeneralizedTateAlgebra (polyradius K P.arity (affinoidLevel K P R φ)) K) R :=
  GeneralizedTateAlgebra.evaluateHom (polyradius K P.arity (affinoidLevel K P R φ)) K R
    (affinoidValue K P R φ) (affinoidValue_hasBoundedMonomials K P R φ)

theorem affinoidTateMap_X (t : Fin P.arity) :
    affinoidTateMap K P R φ
        (GeneralizedTateAlgebra.X (polyradius K P.arity (affinoidLevel K P R φ)) K t) =
      affinoidValue K P R φ t :=
  GeneralizedTateAlgebra.evaluate_X (polyradius K P.arity (affinoidLevel K P R φ)) K R
    (affinoidValue K P R φ) t

/-- On polynomials, Tate evaluation is `φ` applied to the presented element. -/
theorem affinoidTateMap_polynomialMap (p : MvPolynomial (Fin P.arity) K) :
    affinoidTateMap K P R φ
        (GeneralizedTateAlgebra.polynomialMap (polyradius K P.arity (affinoidLevel K P R φ)) K p) =
      φ (P.map p) := by
  have h : (affinoidTateMap K P R φ).toAlgHom.comp
      (GeneralizedTateAlgebra.polynomialMap (polyradius K P.arity (affinoidLevel K P R φ)) K) =
        φ.comp P.map := by
    apply MvPolynomial.algHom_ext
    intro t
    change affinoidTateMap K P R φ (MvPolynomial.aeval _ (MvPolynomial.X t)) =
      φ (P.map (MvPolynomial.X t))
    rw [MvPolynomial.aeval_X]
    exact affinoidTateMap_X K P R φ t
  exact AlgHom.congr_fun h p

/-- The bounded map from the chart algebra at the radius level to `R`, descended
through the closed relation ideal. -/
def affinoidChartMap : BoundedAlgHom K (algebra K P (affinoidLevel K P R φ)) R :=
  PresentedAffinoidAlgebra.descendRelations K P.arity
    (polyradius K P.arity (affinoidLevel K P R φ))
    (PolynomialLocus.relations P (polyradius K P.arity (affinoidLevel K P R φ))) R
    (affinoidTateMap K P R φ)
    (by
      rintro _ ⟨p, hp, rfl⟩
      have h0 : P.map p = 0 := RingHom.mem_ker.1 hp
      rw [affinoidTateMap_polynomialMap, h0, map_zero])

@[simp]
theorem affinoidChartMap_coordinate (t : Fin P.arity) :
    affinoidChartMap K P R φ (coordinate K (algebra K P (affinoidLevel K P R φ)) t) =
      affinoidValue K P R φ t :=
  affinoidTateMap_X K P R φ t

/-- The chart map is compatible with the coordinate-algebra map and `φ`. -/
@[simp]
theorem affinoidChartMap_algebraMap (a : A) :
    affinoidChartMap K P R φ
        (PolynomialLocus.algebraMap P (polyradius K P.arity (affinoidLevel K P R φ)) a) =
      φ a := by
  obtain ⟨p, rfl⟩ := P.surjective a
  rw [PolynomialLocus.algebraMap_map]
  change affinoidTateMap K P R φ
    (GeneralizedTateAlgebra.polynomialMap (polyradius K P.arity (affinoidLevel K P R φ)) K p) = _
  rw [affinoidTateMap_polynomialMap]

/-! ## The continuous map and the atlas morphisms -/

/-- The continuous map from the spectrum of `R` to the analytification: pull a
point back to the chart at the radius level. -/
def affinoidBaseMap : C(BanachSpectrum R, Space K P) :=
  ⟨fun x => chart K P (affinoidLevel K P R φ)
      (BanachSpectrum.comap (affinoidChartMap K P R φ).toBoundedRingHom x),
    (continuous_chart K P (affinoidLevel K P R φ)).comp
      (BanachSpectrum.comapContinuous (affinoidChartMap K P R φ).toBoundedRingHom).continuous⟩

@[simp]
theorem affinoidBaseMap_apply (x : BanachSpectrum R) :
    affinoidBaseMap K P R φ x = chart K P (affinoidLevel K P R φ)
      (BanachSpectrum.comap (affinoidChartMap K P R φ).toBoundedRingHom x) :=
  rfl

/-- The selected chart of `P` receiving the spectrum of `R`. -/
def affinoidIndex : (presentation K P).atlas.Index :=
  representative K P (affinoidLevel K P R φ)

/-- The bounded pullback on the selected chart: transport to the radius level,
followed by the chart map. -/
def affinoidPullback :
    BoundedAlgHom K ((presentation K P).atlas.algebra (affinoidIndex K P R φ)) R :=
  (affinoidChartMap K P R φ).comp
    (representativeEquiv K P (affinoidLevel K P R φ)).toBoundedAlgHom

theorem affinoidPullback_algebraMap (a : A) :
    affinoidPullback K P R φ
        (PolynomialLocus.algebraMap P (polyradius K P.arity (affinoidIndex K P R φ).val) a) =
      φ a := by
  change affinoidChartMap K P R φ (representativeEquiv K P (affinoidLevel K P R φ)
    (PolynomialLocus.algebraMap P _ a)) = _
  rw [representativeEquiv, equalRangeEquiv_algebraMap, affinoidChartMap_algebraMap]

/-- The chosen-chart morphism from the singleton atlas of `R` to the constructed
atlas of `P`. -/
def affinoidAtlasHom :
    Hom (PresentedAffinoidSpace.atlasPresentation (Opposite.op R)) (presentation K P) where
  baseMap := affinoidBaseMap K P R φ
  indexMap _ := affinoidIndex K P R φ
  index_mono _ _ _ := Subset.rfl
  pullback _ := affinoidPullback K P R φ
  chart_comm _ x := by
    change chart K P (representative K P (affinoidLevel K P R φ)).val
        (BanachSpectrum.comap
          (representativeEquiv K P (affinoidLevel K P R φ)).toBoundedAlgHom.toBoundedRingHom
          (BanachSpectrum.comap (affinoidChartMap K P R φ).toBoundedRingHom x)) = _
    rw [chart_comap_representativeEquiv]
    rfl
  restriction_comm _ _ _ := by
    rw [(presentation K P).atlas.restriction_id]
    exact (BoundedAlgHom.id_comp (affinoidPullback K P R φ)).trans
      (BoundedAlgHom.comp_id (affinoidPullback K P R φ)).symm

/-- The all-admissible-pair strong map induced by `φ`, built from the chosen-chart
morphism through the directed charts of `P`. -/
def affinoidStrongHom :
    StrongHom (PresentedAffinoidSpace.atlasPresentation (Opposite.op R)) (presentation K P) :=
  StrongHom.ofDirected (affinoidAtlasHom K P R φ) (atlas_hasDirectedCharts K P)

@[simp]
theorem affinoidStrongHom_baseMap :
    (affinoidStrongHom K P R φ).baseMap = affinoidBaseMap K P R φ :=
  rfl

/-- The singleton atlas of an affinoid spectrum has directed charts. -/
theorem _root_.Langlands.Analytic.PresentedAffinoidSpace.atlasPresentation_hasDirectedCharts
    {k : Type u} [NormedField k] [IsUltrametricDist k] [CompleteSpace k]
    (B : PresentedAffinoidSpace k) : B.atlasPresentation.atlas.HasDirectedCharts :=
  fun _ _ => ⟨PUnit.unit, Subset.rfl, Subset.rfl⟩

/-! ## The algebra map of a strong map -/

variable {K P R}

/-- A target chart containing the image of the single chart of `R`. -/
def strongHomTarget
    (F : StrongHom (PresentedAffinoidSpace.atlasPresentation (Opposite.op R))
      (presentation K P)) : (presentation K P).atlas.Index :=
  (F.target_exists PUnit.unit).choose

theorem strongHomTarget_spec
    (F : StrongHom (PresentedAffinoidSpace.atlasPresentation (Opposite.op R))
      (presentation K P)) :
    F.baseMap '' range ((PresentedAffinoidSpace.atlasPresentation (Opposite.op R)).atlas.chart
        PUnit.unit) ⊆ range ((presentation K P).atlas.chart (strongHomTarget F)) :=
  (F.target_exists PUnit.unit).choose_spec

/-- The `K`-algebra map `A → R` of a strong map: the coordinate-algebra map of the
chosen target chart followed by its bounded pullback. -/
def strongHomAlgHom
    (F : StrongHom (PresentedAffinoidSpace.atlasPresentation (Opposite.op R))
      (presentation K P)) : A →ₐ[K] R :=
  (F.pullback PUnit.unit (strongHomTarget F) (strongHomTarget_spec F)).toAlgHom.comp
    (PolynomialLocus.algebraMap P (polyradius K P.arity (strongHomTarget F).val))

theorem strongHomAlgHom_apply
    (F : StrongHom (PresentedAffinoidSpace.atlasPresentation (Opposite.op R))
      (presentation K P)) (a : A) :
    strongHomAlgHom F a =
      F.pullback PUnit.unit (strongHomTarget F) (strongHomTarget_spec F)
        (PolynomialLocus.algebraMap P (polyradius K P.arity (strongHomTarget F).val) a) :=
  rfl

end Langlands.Analytic.AffineAnalytification
