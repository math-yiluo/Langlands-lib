import Langlands.Geometry.Analytic.AffineGroundFieldComparison.Charts
import Langlands.Geometry.Analytic.AffineAnalytificationSeminormProof

/-! # The point map of the affine ground field comparison -/

noncomputable section

universe u u' v

namespace Langlands.Analytic.AffineAnalytification.GroundFieldComparison

open Set Topology PresentedAffinoidAlgebra
open PresentedAffinoidAlgebra.GroundFieldExtension

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
  (hfixed : AffineAnalytificationChartBaseChangeStatement.{u, u', v})

/-- The chart point map through any sufficiently large raw target chart. -/
def rawPoint (i : ChartIndex K P) (n : ℕ)
    (hn : AnalyticAffineSpace.radius K i.val ≤ AnalyticAffineSpace.radius L n)
    (x : BanachSpectrum (E K L P i)) : Space L (Q K L P) :=
  chart L (Q K L P) n (BanachSpectrum.comap (rawPull K L P hfixed i n hn).toBoundedRingHom x)

theorem rawPoint_le (i : ChartIndex K P) {m n : ℕ} (hmn : m ≤ n)
    (hm : AnalyticAffineSpace.radius K i.val ≤ AnalyticAffineSpace.radius L m)
    (hn : AnalyticAffineSpace.radius K i.val ≤ AnalyticAffineSpace.radius L n)
    (x : BanachSpectrum (E K L P i)) :
    rawPoint K L P hfixed i m hm x = rawPoint K L P hfixed i n hn x := by
  have h := chart_pull L (Q K L P) hmn
    (BanachSpectrum.comap (rawPull K L P hfixed i m hm).toBoundedRingHom x)
  change chart L (Q K L P) n (BanachSpectrum.comap (restriction L (Q K L P) hmn).toBoundedRingHom
    (BanachSpectrum.comap (rawPull K L P hfixed i m hm).toBoundedRingHom x)) = _ at h
  rw [← comap_comp, rawPull_comp K L P hfixed i hmn hm hn] at h
  exact h.symm

theorem rawPoint_independent (i : ChartIndex K P) {m n : ℕ}
    (hm : AnalyticAffineSpace.radius K i.val ≤ AnalyticAffineSpace.radius L m)
    (hn : AnalyticAffineSpace.radius K i.val ≤ AnalyticAffineSpace.radius L n)
    (x : BanachSpectrum (E K L P i)) :
    rawPoint K L P hfixed i m hm x = rawPoint K L P hfixed i n hn x := by
  have hp := hm.trans ((AnalyticAffineSpace.radius_le_radius_iff L).2 (le_max_left m n))
  exact (rawPoint_le K L P hfixed i (le_max_left m n) hm hp x).trans
    (rawPoint_le K L P hfixed i (le_max_right m n) hn hp x).symm

/-- A raw `L`-chart index whose radius exceeds that of the original chart `i`. -/
def level (i : ChartIndex K P) : ℕ :=
  (exists_radius_gt L (AnalyticAffineSpace.radius K i.val)).choose

omit [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L] in
theorem le_radius_level (i : ChartIndex K P) :
    AnalyticAffineSpace.radius K i.val ≤ AnalyticAffineSpace.radius L (level K L P i) :=
  (exists_radius_gt L (AnalyticAffineSpace.radius K i.val)).choose_spec.le

/-- The point map on the extended original chart `i`, through the raw chart `level i`. -/
def chartPoint (i : ChartIndex K P) : BanachSpectrum (E K L P i) → Space L (Q K L P) :=
  rawPoint K L P hfixed i (level K L P i) (le_radius_level K L P i)

theorem chartPoint_eq (i : ChartIndex K P) (n : ℕ)
    (hn : AnalyticAffineSpace.radius K i.val ≤ AnalyticAffineSpace.radius L n)
    (x : BanachSpectrum (E K L P i)) :
    chartPoint K L P hfixed i x = rawPoint K L P hfixed i n hn x :=
  rawPoint_independent K L P hfixed i (le_radius_level K L P i) hn x

theorem rawPoint_pull (i j : ChartIndex K P) (h : (S K L P).Sub i j) (n : ℕ)
    (hi : AnalyticAffineSpace.radius K i.val ≤ AnalyticAffineSpace.radius L n)
    (hj : AnalyticAffineSpace.radius K j.val ≤ AnalyticAffineSpace.radius L n)
    (x : BanachSpectrum (E K L P i)) :
    rawPoint K L P hfixed j n hj ((S K L P).pull h x) = rawPoint K L P hfixed i n hi x := by
  change chart L (Q K L P) n (BanachSpectrum.comap (rawPull K L P hfixed j n hj).toBoundedRingHom
    (BanachSpectrum.comap ((S K L P).restriction i j h).toBoundedRingHom x)) = _
  rw [← comap_comp, rawPull_sub K L P hfixed i j h n hi hj]
  rfl

theorem chartPoint_pull (i j : ChartIndex K P) (h : (S K L P).Sub i j)
    (x : BanachSpectrum (E K L P i)) :
    chartPoint K L P hfixed j ((S K L P).pull h x) = chartPoint K L P hfixed i x := by
  let n := level K L P j
  have hj : AnalyticAffineSpace.radius K j.val ≤ AnalyticAffineSpace.radius L n := le_radius_level K L P j
  have hi := ((AnalyticAffineSpace.radius_le_radius_iff K).2 ((selected_range_subset_iff K P i j).1 h)).trans hj
  exact (rawPoint_pull K L P hfixed i j h n hi hj x).trans
    (chartPoint_eq K L P hfixed i n hi x).symm

/-- The actual continuous map of the glued spaces, not a map of a substitute carrier. -/
def pointFun : (S K L P).Space → Space L (Q K L P) :=
  Quotient.lift (fun z => chartPoint K L P hfixed z.1 z.2) (by
    rintro ⟨i, s⟩ ⟨j, t⟩ ⟨m, hmi, hmj, x, hs, ht⟩
    change chartPoint K L P hfixed i s = chartPoint K L P hfixed j t
    change (S K L P).pull hmi x = s at hs
    change (S K L P).pull hmj x = t at ht
    rw [← hs, ← ht, chartPoint_pull K L P hfixed m i hmi, chartPoint_pull K L P hfixed m j hmj])

theorem pointFun_chart (i : ChartIndex K P) (x : BanachSpectrum (E K L P i)) :
    pointFun K L P hfixed ((S K L P).chart i x) = chartPoint K L P hfixed i x := rfl

theorem continuous_pointFun : Continuous (pointFun K L P hfixed) := by
  apply Continuous.quotient_lift
  refine continuous_sigma fun i => ?_
  exact (continuous_chart L (Q K L P) _).comp (BanachSpectrum.comapContinuous
    (rawPull K L P hfixed i (level K L P i) (le_radius_level K L P i)).toBoundedRingHom).continuous

theorem rawPoint_projection (i : ChartIndex K P) (n : ℕ)
    (hn : AnalyticAffineSpace.radius K i.val ≤ AnalyticAffineSpace.radius L n)
    (x : BanachSpectrum (E K L P i)) :
    baseChangeMap K L P (rawPoint K L P hfixed i n hn x) =
      chart K P i.val (spectrumProjection K L (algebra K P i.val) x) := by
  apply SeminormComparison.pointSeminorm_injective K P
  ext a
  rw [pointSeminorm_baseChangeMap]
  unfold rawPoint
  rw [pointSeminorm_chart, pointSeminorm_chart, chartSeminorm_apply, chartSeminorm_apply]
  exact congrArg (fun t : E K L P i => x t) (rawPull_algebraMap K L P hfixed i n hn a)

theorem pointFun_projection (z : (S K L P).Space) :
    baseChangeMap K L P (pointFun K L P hfixed z) =
      IndexedAffinoidAtlas.GroundFieldExtension.projection K L (atlas K P) z := by
  obtain ⟨i, x, rfl⟩ := (S K L P).exists_chart z
  exact rawPoint_projection K L P hfixed i (level K L P i) (le_radius_level K L P i) x

theorem pointSeminorm_X (z : Space K P) (t : Fin P.arity) :
    pointSeminorm K P z (P.map (MvPolynomial.X t)) = coordinateNorm K P t z :=
  (SeminormComparison.coordinateNorm_eq K P t z).symm

open scoped TensorProduct in
theorem coordinateNorm_baseChange (y : Space L (Q K L P)) (t : Fin P.arity) :
    coordinateNorm K P t (baseChangeMap K L P y) = coordinateNorm L (Q K L P) t y :=
  (pointSeminorm_X K P _ t).symm.trans
    ((pointSeminorm_baseChangeMap K L P y (P.map (MvPolynomial.X t))).trans
      ((congrArg (fun a : L ⊗[K] A => pointSeminorm L (Q K L P) y a)
        (baseChangePresentation_map_X K L P t).symm).trans
        (pointSeminorm_X L (Q K L P) y t)))

theorem range_chartPoint (i : ChartIndex K P) :
    range (chartPoint K L P hfixed i) =
      baseChangeMap K L P ⁻¹' range (chart K P i.val) := by
  ext y
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨_, (rawPoint_projection K L P hfixed i (level K L P i) (le_radius_level K L P i) s).symm⟩
  · intro hy
    have hb := (mem_range_chart_iff K P i.val (baseChangeMap K L P y)).mp hy
    obtain ⟨m, s, rfl⟩ := exists_chart L (Q K L P) y
    let n := max m (level K L P i)
    have hmn : m ≤ n := le_max_left _ _
    have hn : AnalyticAffineSpace.radius K i.val ≤ AnalyticAffineSpace.radius L n :=
      (le_radius_level K L P i).trans ((AnalyticAffineSpace.radius_le_radius_iff L).2 (le_max_right _ _))
    let t := (AffineAnalytification.chartSystem L (Q K L P)).pull hmn s
    have ht : chart L (Q K L P) n t = chart L (Q K L P) m s := chart_pull L (Q K L P) hmn s
    have ht' : t ∈ range (BanachSpectrum.comap (rawPull K L P hfixed i n hn).toBoundedRingHom) := by
      rw [(rawPull_represents K L P hfixed i n hn).2.1]
      intro j
      calc t (coordinate L (algebra L (Q K L P) n) j) =
          coordinateNorm L (Q K L P) j (chart L (Q K L P) n t) := rfl
        _ = coordinateNorm L (Q K L P) j (chart L (Q K L P) m s) :=
          congrArg (coordinateNorm L (Q K L P) j) ht
        _ = coordinateNorm K P j (baseChangeMap K L P (chart L (Q K L P) m s)) :=
          (coordinateNorm_baseChange K L P _ j).symm
        _ ≤ _ := hb j
    obtain ⟨x, hx⟩ := ht'
    exact ⟨x, (chartPoint_eq K L P hfixed i n hn x).trans
      ((congrArg (chart L (Q K L P) n) hx).trans ht)⟩

theorem isEmbedding_chartPoint (i : ChartIndex K P) : IsEmbedding (chartPoint K L P hfixed i) := by
  let n := level K L P i
  let hn := le_radius_level K L P i
  let f := rawPull K L P hfixed i n hn
  have hinj := comap_injective_of_represents (rawPull_represents K L P hfixed i n hn)
  have hc := (BanachSpectrum.comapContinuous f.toBoundedRingHom).continuous
  exact (isClosedEmbedding_chart L (Q K L P) n).isEmbedding.comp (hc.isClosedEmbedding hinj).isEmbedding

open IndexedAffinoidAtlas.GroundFieldExtension in
set_option maxHeartbeats 1000000 in
theorem isHomeomorph_pointFun : IsHomeomorph (pointFun K L P hfixed) := by
  let p := projection K L (atlas K P)
  let g := pointFun K L P hfixed
  let D := Space L (Q K L P)
  have hproj : ∀ z, baseChangeMap K L P (g z) = p z := pointFun_projection K L P hfixed
  have hinj : Function.Injective g := by
    intro x y hxy
    have hp : p x = p y := (hproj x).symm.trans ((congrArg (baseChangeMap K L P) hxy).trans (hproj y))
    obtain ⟨i, s, rfl⟩ := (S K L P).exists_chart x
    have hs : p ((S K L P).chart i s) ∈ range (chart K P i.val) := ⟨_, rfl⟩
    have hy : y ∈ range ((S K L P).chart i) := (range_chart K L (atlas K P) i).symm ▸
      (show y ∈ p ⁻¹' range (chart K P i.val) from (show p y ∈ range (chart K P i.val) from hp ▸ hs))
    obtain ⟨t, rfl⟩ := hy
    exact congrArg ((S K L P).chart i) ((isEmbedding_chartPoint K L P hfixed i).injective hxy)
  let τ : Set (Set D) := (Set.preimage (baseChangeMap K L P : D → Space K P)) ''
    range (fun i : ChartIndex K P => range (chart K P i.val))
  have hτ : AtlasTopology.IsQuasinet τ :=
    (selected_isNet K P).1.preimage_image (baseChangeMap K L P).continuous
  have hMem {V : Set D} (hV : V ∈ τ) : ∃ i, V = range (chartPoint K L P hfixed i) := by
    obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := hV
    exact ⟨i, (range_chartPoint K L P hfixed i).symm⟩
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨V, hV, hy⟩ := Set.mem_sUnion.mp (show y ∈ ⋃₀ τ from hτ.covers.symm ▸ mem_univ y)
    obtain ⟨i, rfl⟩ := hMem hV
    obtain ⟨x, hx⟩ := hy
    exact ⟨(S K L P).chart i x, hx⟩
  let e := Equiv.ofBijective g ⟨hinj, hsurj⟩
  refine isHomeomorph_iff_exists_inverse.mpr
    ⟨continuous_pointFun K L P hfixed, e.symm, e.left_inv, e.right_inv, ?_⟩
  apply hτ.continuous
  intro V hV
  obtain ⟨i, rfl⟩ := hMem hV
  apply continuousOn_iff_continuous_domRestrict.mpr
  let eᵢ := (isEmbedding_chartPoint K L P hfixed i).toHomeomorph
  have heq : (range (chartPoint K L P hfixed i)).domRestrict e.symm =
      (S K L P).chart i ∘ eᵢ.symm := by
    funext z
    apply e.injective
    change e (e.symm z) = chartPoint K L P hfixed i (eᵢ.symm z)
    rw [Equiv.apply_symm_apply]
    exact (congrArg Subtype.val (eᵢ.apply_symm_apply z)).symm
  rw [heq]
  exact ((S K L P).continuous_chart i).comp eᵢ.symm.continuous

end Langlands.Analytic.AffineAnalytification.GroundFieldComparison
