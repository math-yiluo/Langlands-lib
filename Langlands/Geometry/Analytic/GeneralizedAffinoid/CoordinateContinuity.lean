import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeSeriesMap
import Langlands.Geometry.Analytic.GeneralizedAffinoid.NormContinuousAction

/-! # Continuity from finite coordinates of actual weighted quotients -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open CategoryTheory Filter GeneralizedTateAlgebra
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/-- Source-radius bounds on all coordinates force an actual bounded map to
be contractive for the constructed quotient norms, including a zero target. -/
theorem norm_map_le_of_coordinates
    {A B : PresentedAffinoidAlgebra K} (φ : BoundedAlgHom K A B)
    (hc : ∀ i, ‖φ (coordinate K A i)‖ ≤ A.polyradius i) (a : A) :
    ‖φ a‖ ≤ ‖a‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨f, hf, hn⟩ := exists_representative_norm_lt K A a hε
  have heval : ‖φ (presentationMap K A f)‖ ≤ ‖f‖ := by
    change ‖(φ.comp (presentationMap K A)) f‖ ≤ ‖f‖
    rw [map_eq_evaluate A.polyradius K B (φ.comp (presentationMap K A))]
    exact (evaluate_norm_le_bound A.polyradius K B
      (fun i => φ (coordinate K A i)) 1 zero_lt_one
      (fun d => by
        simpa only [one_mul] using monomialValue_norm_le_weight A.polyradius B
          (norm_one_le K B) (fun i => φ (coordinate K A i)) hc d) f).trans_eq (one_mul _)
  rw [hf] at heval
  exact heval.trans hn.le

/-- A finite continuous tuple locally stays within its arbitrary positive
radius bounds, using ultrametricity at the center. -/
theorem eventually_coordinates_norm_le
    {T : Type v} [TopologicalSpace T] {x : T}
    {B : PresentedAffinoidAlgebra K} {ι : Type w} [Finite ι]
    (r : PositivePolyradius ι) (c : T → ι → B)
    (hc : ∀ i, ContinuousAt (fun t => c t i) x)
    (hx : ∀ i, ‖c x i‖ ≤ r i) :
    ∀ᶠ t in 𝓝 x, ∀ i, ‖c t i‖ ≤ r i := by
  apply Filter.eventually_all.mpr
  intro i
  filter_upwards [Metric.continuousAt_iff'.mp (hc i) (r i) (r.positive i)] with t ht
  calc
    ‖c t i‖ = ‖(c t i - c x i) + c x i‖ := by rw [sub_add_cancel]
    _ ≤ max ‖c t i - c x i‖ ‖c x i‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ r i := max_le (by simpa only [dist_eq_norm] using ht.le) (hx i)

/-- Finitely many coordinate continuities derive one neighborhood on which
every operator is contractive on every section. -/
theorem eventually_contractive_of_coordinates
    {T : Type v} [TopologicalSpace T] {x : T}
    {A B : PresentedAffinoidAlgebra K} (φ : T → BoundedAlgHom K A B)
    (hc : ∀ i, ContinuousAt (fun t => φ t (coordinate K A i)) x)
    (hx : ∀ i, ‖φ x (coordinate K A i)‖ ≤ A.polyradius i) :
    ∀ᶠ t in 𝓝 x, ∀ a, ‖φ t a‖ ≤ ‖a‖ := by
  filter_upwards [eventually_coordinates_norm_le A.polyradius
    (fun t i => φ t (coordinate K A i)) hc hx] with t ht
  exact norm_map_le_of_coordinates (φ t) ht

/-- The image of a monomial is continuous when all coordinate images are. -/
theorem continuousAt_map_monomial
    {T : Type v} [TopologicalSpace T] {x : T}
    {A B : PresentedAffinoidAlgebra K} (φ : T → BoundedAlgHom K A B)
    (hc : ∀ i, ContinuousAt (fun t => φ t (coordinate K A i)) x)
    (m : Fin A.arity →₀ ℕ) (a : K) :
    ContinuousAt (fun t =>
      φ t (presentationMap K A (monomial A.polyradius K m a))) x := by
  change ContinuousAt (fun t =>
    (φ t |>.comp (presentationMap K A)) (monomial A.polyradius K m a)) x
  simp_rw [map_monomial]
  change ContinuousAt (fun t => algebraMap K B a *
    StrictTateAlgebra.monomialValue (Fin A.arity) B
      (fun i => φ t (coordinate K A i)) m) x
  have hm : ContinuousAt (fun t =>
      StrictTateAlgebra.monomialValue (Fin A.arity) B
        (fun i => φ t (coordinate K A i)) m) x := by
    unfold StrictTateAlgebra.monomialValue Finsupp.prod
    exact tendsto_finsetProd _ (fun i _ => (hc i).pow _)
  exact continuousAt_const.mul hm

/-- Quotient images of finite coefficient-monomial sums approximate every
actual quotient element in its norm, without coefficient completeness. -/
theorem exists_partial_sum_approx (A : PresentedAffinoidAlgebra K)
    (b : A) {ε : ℝ} (hε : 0 < ε) :
    ∃ (f : GeneralizedTateAlgebra A.polyradius K) (s : Finset (Fin A.arity →₀ ℕ)),
      ‖b - presentationMap K A (∑ m ∈ s,
        monomial A.polyradius K m (MvPowerSeries.coeff m (series A.polyradius K f)))‖ <
        ε := by
  classical
  obtain ⟨f, rfl⟩ := presentationMap_surjective K A b
  have ht : Tendsto (fun s : Finset (Fin A.arity →₀ ℕ) =>
      ∑ m ∈ s, monomial A.polyradius K m
        (MvPowerSeries.coeff m (series A.polyradius K f))) atTop (𝓝 f) :=
    hasSum_monomials A.polyradius K f
  obtain ⟨s, hs⟩ := Metric.tendsto_atTop.mp ht ε hε
  refine ⟨f, s, ?_⟩
  calc
    _ = ‖presentationMap K A (f - ∑ m ∈ s,
      monomial A.polyradius K m (MvPowerSeries.coeff m (series A.polyradius K f)))‖ := by
        rw [map_sub]
    _ ≤ ‖f - ∑ m ∈ s,
      monomial A.polyradius K m (MvPowerSeries.coeff m (series A.polyradius K f))‖ :=
      norm_presentationMap_le K A _
    _ < ε := by
      simpa only [dist_eq_norm, norm_sub_rev] using hs s le_rfl

/-- Finite monomial sums have continuous images under the same coordinate
continuity hypothesis. -/
theorem continuousAt_map_partial_sum
    {T : Type v} [TopologicalSpace T] {x : T}
    {A B : PresentedAffinoidAlgebra K} (φ : T → BoundedAlgHom K A B)
    (hc : ∀ i, ContinuousAt (fun t => φ t (coordinate K A i)) x)
    (f : GeneralizedTateAlgebra A.polyradius K) (s : Finset (Fin A.arity →₀ ℕ)) :
    ContinuousAt (fun t => φ t (presentationMap K A (∑ m ∈ s,
      monomial A.polyradius K m (MvPowerSeries.coeff m (series A.polyradius K f))))) x := by
  classical
  have heq : (fun t => φ t (presentationMap K A (∑ m ∈ s,
      monomial A.polyradius K m (MvPowerSeries.coeff m (series A.polyradius K f))))) =
      (fun t => ∑ m ∈ s, φ t (presentationMap K A
        (monomial A.polyradius K m (MvPowerSeries.coeff m (series A.polyradius K f))))) := by
    funext t
    rw [map_sum, map_sum]
  rw [heq]
  exact tendsto_finsetSum s (fun m _ => continuousAt_map_monomial φ hc m _)

/-- The derived common local contraction and finite-monomial approximation
extend coordinate continuity to every section in the quotient norm. -/
theorem continuousAt_map_of_coordinates
    {T : Type v} [TopologicalSpace T] {x : T}
    {A B : PresentedAffinoidAlgebra K} (φ : T → BoundedAlgHom K A B)
    (hc : ∀ i, ContinuousAt (fun t => φ t (coordinate K A i)) x)
    (hx : ∀ i, ‖φ x (coordinate K A i)‖ ≤ A.polyradius i) (b : A) :
    ContinuousAt (fun t => φ t b) x := by
  classical
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨f, s, hs⟩ := exists_partial_sum_approx A b hε3
  let q := presentationMap K A (∑ m ∈ s,
    monomial A.polyradius K m (MvPowerSeries.coeff m (series A.polyradius K f)))
  have happrox : ‖b - q‖ < ε / 3 := hs
  have hp : ContinuousAt (fun t => φ t q) x := continuousAt_map_partial_sum φ hc f s
  filter_upwards [eventually_contractive_of_coordinates φ hc hx,
    Metric.continuousAt_iff'.mp hp (ε / 3) hε3] with t ht hp
  have hleft : dist (φ t b) (φ t q) ≤ ‖b - q‖ := by
    rw [dist_eq_norm, ← map_sub (φ t).toAlgHom]
    exact ht _
  have hright : dist (φ x q) (φ x b) ≤ ‖b - q‖ := by
    rw [dist_comm, dist_eq_norm, ← map_sub (φ x).toAlgHom]
    exact norm_map_le_of_coordinates (φ x) hx _
  calc
    dist (φ t b) (φ x b) ≤
        dist (φ t b) (φ t q) + dist (φ t q) (φ x q) + dist (φ x q) (φ x b) :=
      dist_triangle4 _ _ _ _
    _ < ε := by linarith only [hleft, hp, hright, happrox]

/-- For a multiplicative family of bounded endomorphisms, identity-orbit
continuity translates to continuity everywhere in the given topological group. -/
theorem continuous_map_of_continuousAt_one
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A : PresentedAffinoidAlgebra K} (φ : G → BoundedAlgHom K A A)
    (hm : ∀ g h, φ (g * h) = (φ g).comp (φ h))
    (hc : ∀ a : A, ContinuousAt (fun g => φ g a) 1) (a : A) :
    Continuous (fun g => φ g a) := by
  apply continuous_iff_continuousAt.mpr
  intro g
  have ht : Tendsto (fun h : G => g⁻¹ * h) (𝓝 g) (𝓝 (1 : G)) := by
    have htrans : ContinuousAt (fun h : G => g⁻¹ * h) g :=
      continuous_const.continuousAt.mul continuous_id.continuousAt
    simpa only [inv_mul_cancel] using htrans.tendsto
  have h := (φ g).continuous.continuousAt.tendsto.comp ((hc a).tendsto.comp ht)
  have heq : (fun h => φ g (φ (g⁻¹ * h) a)) = (fun h => φ h a) := by
    funext h
    change ((φ g).comp (φ (g⁻¹ * h))) a = _
    rw [← hm, mul_inv_cancel_left]
  have hcenter : φ g (φ 1 a) = φ g a := by
    change ((φ g).comp (φ 1)) a = _
    rw [← hm, mul_one]
  change Tendsto (fun h => φ g (φ (g⁻¹ * h) a)) (𝓝 g) (𝓝 (φ g (φ 1 a))) at h
  rw [heq, hcenter] at h
  exact h

/-- Coordinate orbit continuity only at the identity constructs the full
norm-continuous action on the actual quotient, with no common bound supplied. -/
def normContinuousActionOfCoordinates
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : PresentedAffinoidAlgebra K) (σ : G →* Aut A)
    (hc : ∀ i, ContinuousAt
      (fun g : G => (σ g).hom.toAlgHom (coordinate K A i)) 1) :
    NormContinuousAction K G :=
  NormContinuousAction.ofAut A σ (fun b => by
    have hm (g h : G) : (σ (g * h)).hom = ((σ g).hom).comp (σ h).hom := by
      change (σ (g * h)).hom = ((σ g) * (σ h)).hom
      rw [map_mul]
    apply continuous_map_of_continuousAt_one
      (fun g => (σ g).hom) hm ?_ b
    intro a
    apply continuousAt_map_of_coordinates (fun g => (σ g).hom) hc
    intro i
    rw [map_one]
    exact norm_coordinate_le K A i)

@[simp]
theorem normContinuousActionOfCoordinates_actionAut
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : PresentedAffinoidAlgebra K) (σ : G →* Aut A)
    (hc : ∀ i, ContinuousAt
      (fun g : G => (σ g).hom.toAlgHom (coordinate K A i)) 1) :
    (normContinuousActionOfCoordinates A σ hc).actionAut = σ :=
  NormContinuousAction.actionAut_ofAut _ _ _

end Langlands.Analytic.PresentedAffinoidAlgebra
