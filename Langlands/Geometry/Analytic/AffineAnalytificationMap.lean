import Langlands.Geometry.Analytic.AffineAnalytificationAtlas
import Langlands.Geometry.Analytic.DirectedAtlasMaps

/-! # Maps of polynomial-locus analytifications induced by algebra maps -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffineAnalytification

open Set Topology PresentedAffinoidAlgebra AnalyticAffineSpace

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  {A : Type v} [CommRing A] [Algebra K A] {B : Type w} [CommRing B] [Algebra K B]
  (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
  (f : A →ₐ[K] B)

/-! ## Polynomial lifts of the generator images -/

/-- A chosen polynomial in the variables of `Q` presenting the image under `f`
of the `t`-th generator of `P`. -/
def generatorLift (t : Fin P.arity) : MvPolynomial (Fin Q.arity) K :=
  (Q.surjective (f (P.map (MvPolynomial.X t)))).choose

omit [IsUltrametricDist K] in
theorem map_generatorLift (t : Fin P.arity) :
    Q.map (generatorLift K P Q f t) = f (P.map (MvPolynomial.X t)) :=
  (Q.surjective (f (P.map (MvPolynomial.X t)))).choose_spec

omit [IsUltrametricDist K] in
/-- Substituting the lifts into a polynomial of `P` presents its image under `f`. -/
theorem map_aeval_generatorLift (p : MvPolynomial (Fin P.arity) K) :
    Q.map (MvPolynomial.aeval (generatorLift K P Q f) p) = f (P.map p) := by
  have h : Q.map.comp (MvPolynomial.aeval (generatorLift K P Q f)) = f.comp P.map := by
    apply MvPolynomial.algHom_ext
    intro t
    rw [AlgHom.comp_apply, AlgHom.comp_apply, MvPolynomial.aeval_X]
    exact map_generatorLift K P Q f t
  exact AlgHom.congr_fun h p

/-- The image of the `t`-th lifted generator in the `k`-th bounded chart of `Q`. -/
def generatorValue (k : ℕ) (t : Fin P.arity) : algebra K Q k :=
  PolynomialLocus.polynomialMap Q (polyradius K Q.arity k) (generatorLift K P Q f t)

/-! ## The radius levels of the target charts -/

theorem exists_generatorValue_le (k : ℕ) :
    ∃ l, ∀ t, ‖generatorValue K P Q f k t‖ ≤ radius K l := by
  obtain ⟨l, hl⟩ := exists_radius_gt K (∑ t, ‖generatorValue K P Q f k t‖)
  refine ⟨l, fun t => ?_⟩
  exact (Finset.single_le_sum (fun s _ => norm_nonneg (generatorValue K P Q f k s))
    (Finset.mem_univ t)).trans hl.le

open scoped Classical in
/-- The least radius index bounding the quotient norms of all lifted generator
values in the `k`-th chart of `Q`. -/
def minimalLevel (k : ℕ) : ℕ :=
  Nat.find (exists_generatorValue_le K P Q f k)

open scoped Classical in
theorem norm_generatorValue_le_minimalLevel (k : ℕ) (t : Fin P.arity) :
    ‖generatorValue K P Q f k t‖ ≤ radius K (minimalLevel K P Q f k) :=
  Nat.find_spec (exists_generatorValue_le K P Q f k) t

/-- The monotone radius index of the chart of `P` receiving the `k`-th chart of `Q`. -/
def level (k : ℕ) : ℕ :=
  (Finset.range (k + 1)).sup (minimalLevel K P Q f)

theorem minimalLevel_le_level (k : ℕ) : minimalLevel K P Q f k ≤ level K P Q f k :=
  Finset.le_sup (Finset.self_mem_range_succ k)

theorem level_mono {k k' : ℕ} (h : k ≤ k') : level K P Q f k ≤ level K P Q f k' :=
  Finset.sup_mono (Finset.range_subset_range.2 (Nat.succ_le_succ h))

theorem norm_generatorValue_le (k : ℕ) (t : Fin P.arity) :
    ‖generatorValue K P Q f k t‖ ≤ radius K (level K P Q f k) :=
  (norm_generatorValue_le_minimalLevel K P Q f k t).trans
    ((radius_le_radius_iff K).2 (minimalLevel_le_level K P Q f k))

/-- The lifted generator values have weighted monomials bounded by one. -/
theorem generatorValue_hasBoundedMonomials (k : ℕ) :
    GeneralizedTateAlgebra.HasBoundedMonomials (polyradius K P.arity (level K P Q f k))
      (algebra K Q k) (generatorValue K P Q f k) :=
  ⟨1, one_pos, fun d => by
    rw [one_mul]
    exact GeneralizedTateAlgebra.monomialValue_norm_le_weight _ _ (norm_one_le K _) _
      (norm_generatorValue_le K P Q f k) d⟩

/-! ## The bounded chart maps -/

variable [CompleteSpace K]

/-- Weighted Tate evaluation at the lifted generator values. -/
def tateMap (k : ℕ) :
    BoundedAlgHom K (GeneralizedTateAlgebra (polyradius K P.arity (level K P Q f k)) K)
      (algebra K Q k) :=
  GeneralizedTateAlgebra.evaluateHom (polyradius K P.arity (level K P Q f k)) K
    (algebra K Q k) (generatorValue K P Q f k) (generatorValue_hasBoundedMonomials K P Q f k)

theorem tateMap_X (k : ℕ) (t : Fin P.arity) :
    tateMap K P Q f k (GeneralizedTateAlgebra.X (polyradius K P.arity (level K P Q f k)) K t) =
      generatorValue K P Q f k t :=
  GeneralizedTateAlgebra.evaluate_X (polyradius K P.arity (level K P Q f k)) K
    (algebra K Q k) (generatorValue K P Q f k) t

/-- On polynomials, Tate evaluation is substitution of the lifts. -/
theorem tateMap_polynomialMap (k : ℕ) (p : MvPolynomial (Fin P.arity) K) :
    tateMap K P Q f k
        (GeneralizedTateAlgebra.polynomialMap (polyradius K P.arity (level K P Q f k)) K p) =
      PolynomialLocus.polynomialMap Q (polyradius K Q.arity k)
        (MvPolynomial.aeval (generatorLift K P Q f) p) := by
  have h : (tateMap K P Q f k).toAlgHom.comp
      (GeneralizedTateAlgebra.polynomialMap (polyradius K P.arity (level K P Q f k)) K) =
        (PolynomialLocus.polynomialMap Q (polyradius K Q.arity k)).comp
          (MvPolynomial.aeval (generatorLift K P Q f)) := by
    apply MvPolynomial.algHom_ext
    intro t
    change tateMap K P Q f k (MvPolynomial.aeval _ (MvPolynomial.X t)) =
      PolynomialLocus.polynomialMap Q _ (MvPolynomial.aeval _ (MvPolynomial.X t))
    rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    exact tateMap_X K P Q f k t
  exact AlgHom.congr_fun h p

omit [CompleteSpace K] in
theorem polynomialMap_aeval_generatorLift (k : ℕ) (p : MvPolynomial (Fin P.arity) K) :
    PolynomialLocus.polynomialMap Q (polyradius K Q.arity k)
        (MvPolynomial.aeval (generatorLift K P Q f) p) =
      PolynomialLocus.algebraMap Q (polyradius K Q.arity k) (f (P.map p)) := by
  rw [← PolynomialLocus.algebraMap_map, map_aeval_generatorLift]

omit [CompleteSpace K] in
/-- The lifted generator values do not depend on the chosen lifts. -/
theorem generatorValue_eq_algebraMap (k : ℕ) (t : Fin P.arity) :
    generatorValue K P Q f k t =
      PolynomialLocus.algebraMap Q (polyradius K Q.arity k) (f (P.map (MvPolynomial.X t))) := by
  have h := polynomialMap_aeval_generatorLift K P Q f k (MvPolynomial.X t)
  rw [MvPolynomial.aeval_X] at h
  exact h

/-- The bounded map from the `level k`-th chart algebra of `P` to the `k`-th
chart algebra of `Q`, descended through the closed relation ideal. -/
def chartMap (k : ℕ) :
    BoundedAlgHom K (algebra K P (level K P Q f k)) (algebra K Q k) :=
  PresentedAffinoidAlgebra.descendRelations K P.arity (polyradius K P.arity (level K P Q f k))
    (PolynomialLocus.relations P (polyradius K P.arity (level K P Q f k))) (algebra K Q k)
    (tateMap K P Q f k)
    (by
      rintro _ ⟨p, hp, rfl⟩
      have h0 : P.map p = 0 := RingHom.mem_ker.1 hp
      rw [tateMap_polynomialMap, polynomialMap_aeval_generatorLift, h0, map_zero, map_zero])

theorem chartMap_presentationMap (k : ℕ)
    (g : GeneralizedTateAlgebra (polyradius K P.arity (level K P Q f k)) K) :
    chartMap K P Q f k (presentationMap K (algebra K P (level K P Q f k)) g) =
      tateMap K P Q f k g :=
  rfl

@[simp]
theorem chartMap_coordinate (k : ℕ) (t : Fin P.arity) :
    chartMap K P Q f k (coordinate K (algebra K P (level K P Q f k)) t) =
      generatorValue K P Q f k t :=
  tateMap_X K P Q f k t

/-- The chart maps are compatible with the coordinate-algebra maps and `f`. -/
@[simp]
theorem chartMap_algebraMap (k : ℕ) (a : A) :
    chartMap K P Q f k (PolynomialLocus.algebraMap P (polyradius K P.arity (level K P Q f k)) a) =
      PolynomialLocus.algebraMap Q (polyradius K Q.arity k) (f a) := by
  obtain ⟨p, rfl⟩ := P.surjective a
  rw [PolynomialLocus.algebraMap_map]
  change tateMap K P Q f k
    (GeneralizedTateAlgebra.polynomialMap (polyradius K P.arity (level K P Q f k)) K p) = _
  rw [tateMap_polynomialMap, polynomialMap_aeval_generatorLift]

omit [CompleteSpace K] in
theorem restriction_generatorValue {k k' : ℕ} (h : k ≤ k') (t : Fin P.arity) :
    restriction K Q h (generatorValue K P Q f k' t) = generatorValue K P Q f k t :=
  PolynomialLocus.restriction_polynomial Q _ _ _ _

/-- The chart maps commute with the radius restrictions of both presentations. -/
theorem restriction_comp_chartMap {k k' : ℕ} (h : k ≤ k') :
    (restriction K Q h).comp (chartMap K P Q f k') =
      (chartMap K P Q f k).comp (restriction K P (level_mono K P Q f h)) := by
  apply PresentedAffinoidAlgebra.hom_ext_coordinate
  intro t
  have e1 : chartMap K P Q f k' (coordinate K (algebra K P (level K P Q f k')) t) =
      generatorValue K P Q f k' t :=
    chartMap_coordinate K P Q f k' t
  have e2 : restriction K P (level_mono K P Q f h)
      (coordinate K (algebra K P (level K P Q f k')) t) =
        coordinate K (algebra K P (level K P Q f k)) t :=
    PolynomialLocus.restriction_coordinate P _ _ _ t
  have e3 : chartMap K P Q f k (coordinate K (algebra K P (level K P Q f k)) t) =
      generatorValue K P Q f k t :=
    chartMap_coordinate K P Q f k t
  exact (congrArg (fun b => restriction K Q h b) e1).trans
    ((restriction_generatorValue K P Q f h t).trans
      (e3.symm.trans (congrArg (fun a => chartMap K P Q f k a) e2).symm))

/-! ## The continuous map of analytic spaces -/

/-- The map on one chart spectrum of `Q`. -/
def sigmaMap (x : (k : ℕ) × BanachSpectrum (algebra K Q k)) : Space K P :=
  chart K P (level K P Q f x.1)
    (BanachSpectrum.comap (chartMap K P Q f x.1).toBoundedRingHom x.2)

theorem comap_chartMap_pull {l k : ℕ} (h : l ≤ k) (v : BanachSpectrum (algebra K Q l)) :
    BanachSpectrum.comap (chartMap K P Q f k).toBoundedRingHom
        ((chartSystem K Q).pull h v) =
      (chartSystem K P).pull (level_mono K P Q f h)
        (BanachSpectrum.comap (chartMap K P Q f l).toBoundedRingHom v) := by
  apply BanachSpectrum.ext
  intro a
  change v (restriction K Q h (chartMap K P Q f k a)) =
    v (chartMap K P Q f l (restriction K P (level_mono K P Q f h) a))
  exact congrArg v (congrArg (fun φ : BoundedAlgHom K _ _ => φ a)
    (restriction_comp_chartMap K P Q f h))

theorem sigmaMap_pull {l k : ℕ} (h : l ≤ k) (v : BanachSpectrum (algebra K Q l)) :
    sigmaMap K P Q f ⟨k, (chartSystem K Q).pull h v⟩ = sigmaMap K P Q f ⟨l, v⟩ := by
  change chart K P (level K P Q f k) (BanachSpectrum.comap _ ((chartSystem K Q).pull h v)) = _
  rw [comap_chartMap_pull]
  exact chart_pull K P (level_mono K P Q f h) _

/-- The underlying function, glued from the chart maps. -/
def baseFun : Space K Q → Space K P :=
  Quotient.lift (sigmaMap K P Q f) (by
    intro x y hxy
    obtain ⟨l, hlx, hly, v, hx, hy⟩ := hxy
    obtain ⟨k, s⟩ := x
    obtain ⟨k', s'⟩ := y
    dsimp only at hlx hly hx hy
    subst hx hy
    exact (sigmaMap_pull K P Q f hlx v).trans (sigmaMap_pull K P Q f hly v).symm)

theorem continuous_baseFun : Continuous (baseFun K P Q f) :=
  Continuous.quotient_lift (continuous_sigma fun k =>
    (continuous_chart K P (level K P Q f k)).comp
      (BanachSpectrum.comapContinuous (chartMap K P Q f k).toBoundedRingHom).continuous) _

/-- The continuous map `Space K Q → Space K P` induced by `f`. -/
def baseMap : C(Space K Q, Space K P) :=
  ⟨baseFun K P Q f, continuous_baseFun K P Q f⟩

@[simp]
theorem baseMap_chart (k : ℕ) (x : BanachSpectrum (algebra K Q k)) :
    baseMap K P Q f (chart K Q k x) =
      chart K P (level K P Q f k)
        (BanachSpectrum.comap (chartMap K P Q f k).toBoundedRingHom x) :=
  rfl

/-- The coordinate norms of an image point are the norms of the lifted generator
values at the source point. -/
theorem coordinateNorm_baseMap_chart (k : ℕ) (x : BanachSpectrum (algebra K Q k))
    (t : Fin P.arity) :
    coordinateNorm K P t (baseMap K P Q f (chart K Q k x)) = x (generatorValue K P Q f k t) := by
  rw [baseMap_chart, coordinateNorm_chart]
  change x (chartMap K P Q f k (coordinate K _ t)) = _
  rw [chartMap_coordinate]

theorem baseMap_range_chart_subset (k : ℕ) :
    baseMap K P Q f '' range (chart K Q k) ⊆ range (chart K P (level K P Q f k)) := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact ⟨_, (baseMap_chart K P Q f k x).symm⟩

/-! ## Transport to the selected chart representatives -/

theorem chart_comap_representativeEquiv (m : ℕ) (y : BanachSpectrum (algebra K P m)) :
    chart K P (representative K P m).val
        (BanachSpectrum.comap (representativeEquiv K P m).toBoundedAlgHom.toBoundedRingHom y) =
      chart K P m y := by
  have e := equalRangeEquiv_comp_restriction K P (range_representative K P m)
  have hp : (chartSystem K P).pull (le_max_left (representative K P m).val m)
      (BanachSpectrum.comap (representativeEquiv K P m).toBoundedAlgHom.toBoundedRingHom y) =
        (chartSystem K P).pull (le_max_right (representative K P m).val m) y := by
    apply BanachSpectrum.ext
    intro a
    change y ((representativeEquiv K P m).toBoundedAlgHom
        (restriction K P (le_max_left (representative K P m).val m) a)) =
      y (restriction K P (le_max_right (representative K P m).val m) a)
    exact congrArg y (congrArg (fun φ : BoundedAlgHom K _ _ => φ a) e)
  rw [← chart_pull K P (le_max_left (representative K P m).val m), hp, chart_pull]

theorem representativeEquiv_coordinate (m : ℕ) (t : Fin P.arity) :
    (representativeEquiv K P m).toBoundedAlgHom
        (coordinate K (algebra K P (representative K P m).val) t) =
      coordinate K (algebra K P m) t := by
  have e := equalRangeEquiv_comp_restriction K P (range_representative K P m)
  have hl : restriction K P (le_max_left (representative K P m).val m)
      (coordinate K (algebra K P (max (representative K P m).val m)) t) =
        coordinate K (algebra K P (representative K P m).val) t :=
    PolynomialLocus.restriction_coordinate P _ _ _ t
  have hr : restriction K P (le_max_right (representative K P m).val m)
      (coordinate K (algebra K P (max (representative K P m).val m)) t) =
        coordinate K (algebra K P m) t :=
    PolynomialLocus.restriction_coordinate P _ _ _ t
  rw [← hl, ← hr]
  exact congrArg (fun φ : BoundedAlgHom K _ _ =>
    φ (coordinate K (algebra K P (max (representative K P m).val m)) t)) e

/-! ## The chosen-chart and strong atlas morphisms -/

open AffinoidAtlasPresentation

/-- The selected chart of `P` receiving the selected chart `i` of `Q`. -/
def indexMap (i : (presentation K Q).atlas.Index) : (presentation K P).atlas.Index :=
  representative K P (level K P Q f i.val)

theorem range_chart_indexMap (i : (presentation K Q).atlas.Index) :
    range ((presentation K P).atlas.chart (indexMap K P Q f i)) =
      range (chart K P (level K P Q f i.val)) :=
  range_representative K P (level K P Q f i.val)

theorem indexMap_mono (i j : (presentation K Q).atlas.Index)
    (h : range ((presentation K Q).atlas.chart i) ⊆ range ((presentation K Q).atlas.chart j)) :
    range ((presentation K P).atlas.chart (indexMap K P Q f i)) ⊆
      range ((presentation K P).atlas.chart (indexMap K P Q f j)) := by
  rw [range_chart_indexMap, range_chart_indexMap]
  exact range_chart_mono K P (level_mono K P Q f ((selected_range_subset_iff K Q i j).1 h))

/-- The bounded pullback on a selected chart: transport to the radius level,
followed by the chart map. -/
def pullback (i : (presentation K Q).atlas.Index) :
    BoundedAlgHom K ((presentation K P).atlas.algebra (indexMap K P Q f i))
      ((presentation K Q).atlas.algebra i) :=
  (chartMap K P Q f i.val).comp (representativeEquiv K P (level K P Q f i.val)).toBoundedAlgHom

theorem pullback_coordinate (i : (presentation K Q).atlas.Index) (t : Fin P.arity) :
    pullback K P Q f i
        (coordinate K (algebra K P (representative K P (level K P Q f i.val)).val) t) =
      generatorValue K P Q f i.val t := by
  change chartMap K P Q f i.val ((representativeEquiv K P (level K P Q f i.val)).toBoundedAlgHom
    (coordinate K _ t)) = _
  rw [representativeEquiv_coordinate, chartMap_coordinate]

/-- The pullbacks are compatible with the coordinate-algebra maps and `f`. -/
theorem pullback_algebraMap (i : (presentation K Q).atlas.Index) (a : A) :
    pullback K P Q f i
        (PolynomialLocus.algebraMap P (polyradius K P.arity (indexMap K P Q f i).val) a) =
      PolynomialLocus.algebraMap Q (polyradius K Q.arity i.val) (f a) := by
  change chartMap K P Q f i.val (representativeEquiv K P (level K P Q f i.val)
    (PolynomialLocus.algebraMap P _ a)) = _
  rw [representativeEquiv, equalRangeEquiv_algebraMap, chartMap_algebraMap]

theorem chart_comm_atlasHom (i : ChartIndex K Q) (x : BanachSpectrum (algebra K Q i.val)) :
    chart K P (indexMap K P Q f i).val
        (BanachSpectrum.comap (pullback K P Q f i).toBoundedRingHom x) =
      baseMap K P Q f (chart K Q i.val x) := by
  change chart K P (representative K P (level K P Q f i.val)).val
      (BanachSpectrum.comap
        (representativeEquiv K P (level K P Q f i.val)).toBoundedAlgHom.toBoundedRingHom
        (BanachSpectrum.comap (chartMap K P Q f i.val).toBoundedRingHom x)) = _
  rw [chart_comap_representativeEquiv]
  rfl

theorem restriction_comp_pullback (i j : ChartIndex K Q) (h : i.val ≤ j.val)
    (hP : (indexMap K P Q f i).val ≤ (indexMap K P Q f j).val) :
    (restriction K Q h).comp (pullback K P Q f j) =
      (pullback K P Q f i).comp (restriction K P hP) := by
  apply PresentedAffinoidAlgebra.hom_ext_coordinate
  intro t
  have e1 : pullback K P Q f j (coordinate K (algebra K P (indexMap K P Q f j).val) t) =
      generatorValue K P Q f j.val t :=
    pullback_coordinate K P Q f j t
  have e2 : restriction K P hP (coordinate K (algebra K P (indexMap K P Q f j).val) t) =
      coordinate K (algebra K P (indexMap K P Q f i).val) t :=
    PolynomialLocus.restriction_coordinate P _ _ _ t
  have e3 : pullback K P Q f i (coordinate K (algebra K P (indexMap K P Q f i).val) t) =
      generatorValue K P Q f i.val t :=
    pullback_coordinate K P Q f i t
  exact (congrArg (fun b => restriction K Q h b) e1).trans
    ((restriction_generatorValue K P Q f h t).trans
      (e3.symm.trans (congrArg (fun a => pullback K P Q f i a) e2).symm))

/-- The morphism of constructed atlases induced by `f`, with one selected target
chart and bounded pullback for each selected source chart. -/
def atlasHom : Hom (presentation K Q) (presentation K P) where
  baseMap := baseMap K P Q f
  indexMap := indexMap K P Q f
  index_mono := indexMap_mono K P Q f
  pullback := pullback K P Q f
  chart_comm i x := chart_comm_atlasHom K P Q f i x
  restriction_comm i j h :=
    restriction_comp_pullback K P Q f i j ((selected_range_subset_iff K Q i j).1 h)
      ((selected_range_subset_iff K P _ _).1 (indexMap_mono K P Q f i j h))

/-- The all-admissible-pair strong atlas map induced by `f`, built from the
chosen-chart morphism through the directed charts of `P`. -/
def strongHom : StrongHom (presentation K Q) (presentation K P) :=
  StrongHom.ofDirected (atlasHom K P Q f) (atlas_hasDirectedCharts K P)

@[simp]
theorem strongHom_baseMap : (strongHom K P Q f).baseMap = baseMap K P Q f :=
  rfl

end Langlands.Analytic.AffineAnalytification
