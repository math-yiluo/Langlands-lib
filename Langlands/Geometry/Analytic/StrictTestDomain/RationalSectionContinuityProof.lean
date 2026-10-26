import Langlands.Geometry.Analytic.StrictTestDomain.RationalSectionContinuityStatement
import Mathlib.Analysis.Normed.Ring.Units

/-! # Continuity of the fixed rational-quotient section action -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Filter
open scoped Topology
open PresentedStrictAffinoidAlgebra StrictTateAlgebra

namespace PresentedStrictAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- The quotient norm of the unit is at most one, also in a zero quotient. -/
theorem quotient_norm_one_le (A : PresentedStrictAffinoidAlgebra K) :
    ‖(1 : A)‖ ≤ 1 := by
  exact (Ideal.Quotient.norm_mk_le A.ideal
    (1 : StrictTateAlgebra (Fin A.arity) K)).trans_eq norm_one

/-- Coordinate images in the unit ball force a bounded map of actual
presentations to be contractive. The zero target is included. -/
theorem norm_map_le_of_coordinates
    {A B : PresentedStrictAffinoidAlgebra K} (φ : BoundedAlgHom K A B)
    (hc : ∀ i, ‖φ (coordinate K A i)‖ ≤ 1) (a : A) :
    ‖φ a‖ ≤ ‖a‖ := by
  by_cases hB : Subsingleton B
  · let := hB
    simpa only [Subsingleton.elim (φ a) 0, norm_zero] using norm_nonneg a
  · let : Nontrivial B := not_subsingleton_iff_nontrivial.mp hB
    let : NormOneClass B := ⟨le_antisymm (quotient_norm_one_le B) (one_le_norm_one B)⟩
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨f, hf, hn⟩ := exists_representative_norm_lt K A a hε
    have heval :
        ‖φ (presentationMap K A f)‖ ≤ ‖f‖ := by
      change ‖(φ.comp (presentationMap K A)) f‖ ≤ ‖f‖
      rw [map_eq_evaluate (Fin A.arity) K B
        (φ.comp (presentationMap K A))]
      exact evaluate_norm_le (Fin A.arity) K B
        (fun i => φ (coordinate K A i)) hc f
    rw [hf] at heval
    exact heval.trans hn.le

omit [CompleteSpace K] in
/-- A continuous finite tuple whose value at the center is in the closed unit
ball remains in that ball locally, by ultrametricity. -/
theorem eventually_coordinates_norm_le
    {T : Type v} [TopologicalSpace T] {x : T}
    {B : PresentedStrictAffinoidAlgebra K} {ι : Type w} [Finite ι]
    (c : T → ι → B)
    (hc : ∀ i, ContinuousAt (fun t => c t i) x)
    (hx : ∀ i, ‖c x i‖ ≤ 1) :
    ∀ᶠ t in 𝓝 x, ∀ i, ‖c t i‖ ≤ 1 := by
  apply Filter.eventually_all.mpr
  intro i
  filter_upwards [Metric.continuousAt_iff'.mp (hc i) 1 zero_lt_one] with t ht
  calc
    ‖c t i‖ = ‖(c t i - c x i) + c x i‖ := by rw [sub_add_cancel]
    _ ≤ max ‖c t i - c x i‖ ‖c x i‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le (by simpa only [dist_eq_norm] using ht.le) (hx i)

/-- Finitely many coordinate orbit continuities give one local bound for
every operator, without assuming a common bound in advance. -/
theorem eventually_contractive_of_coordinates
    {T : Type v} [TopologicalSpace T] {x : T}
    {A B : PresentedStrictAffinoidAlgebra K} (φ : T → BoundedAlgHom K A B)
    (hc : ∀ i, ContinuousAt (fun t => φ t (coordinate K A i)) x)
    (hx : ∀ i, ‖φ x (coordinate K A i)‖ ≤ 1) :
    ∀ᶠ t in 𝓝 x, ∀ a, ‖φ t a‖ ≤ ‖a‖ := by
  filter_upwards [eventually_coordinates_norm_le
    (fun t i => φ t (coordinate K A i)) hc hx] with t ht
  exact norm_map_le_of_coordinates (φ t) ht

omit [CompleteSpace K] in
/-- A monomial has a continuous image when the coordinate images are continuous. -/
theorem continuousAt_map_monomial
    {T : Type v} [TopologicalSpace T] {x : T}
    {A B : PresentedStrictAffinoidAlgebra K} (φ : T → BoundedAlgHom K A B)
    (hc : ∀ i, ContinuousAt (fun t => φ t (coordinate K A i)) x)
    (m : Fin A.arity →₀ ℕ) (a : K) :
    ContinuousAt (fun t => φ t (presentationMap K A (monomial _ K m a))) x := by
  change ContinuousAt (fun t =>
    (φ t |>.comp (presentationMap K A)) (monomial _ K m a)) x
  simp_rw [map_monomial]
  change ContinuousAt (fun t => algebraMap K B a *
    monomialValue (Fin A.arity) B (fun i => φ t (coordinate K A i)) m) x
  have hm : ContinuousAt (fun t =>
      monomialValue (Fin A.arity) B (fun i => φ t (coordinate K A i)) m) x := by
    unfold monomialValue Finsupp.prod
    exact tendsto_finsetProd _ (fun i _ => (hc i).pow _)
  exact continuousAt_const.mul hm

/-- Quotient images of finite monomial sums are dense in the quotient norm. -/
theorem exists_partial_sum_approx (A : PresentedStrictAffinoidAlgebra K)
    (b : A) {ε : ℝ} (hε : 0 < ε) :
    ∃ (f : StrictTateAlgebra (Fin A.arity) K) (s : Finset (Fin A.arity →₀ ℕ)),
      ‖b - presentationMap K A (∑ m ∈ s,
        monomial _ K m (MvPowerSeries.coeff m (series _ K f)))‖ < ε := by
  classical
  obtain ⟨f, rfl⟩ := presentationMap_surjective K A b
  have ht : Tendsto (fun s : Finset (Fin A.arity →₀ ℕ) =>
      ∑ m ∈ s, monomial _ K m (MvPowerSeries.coeff m (series _ K f)))
      atTop (𝓝 f) := hasSum_monomials _ K f
  obtain ⟨s, hs⟩ := Metric.tendsto_atTop.mp ht ε hε
  refine ⟨f, s, ?_⟩
  calc
    _ = ‖presentationMap K A (f - ∑ m ∈ s,
      monomial _ K m (MvPowerSeries.coeff m (series _ K f)))‖ := by rw [map_sub]
    _ ≤ ‖f - ∑ m ∈ s, monomial _ K m (MvPowerSeries.coeff m (series _ K f))‖ :=
      Ideal.Quotient.norm_mk_le A.ideal _
    _ < ε := by
      simpa only [dist_eq_norm, norm_sub_rev] using hs s le_rfl

omit [CompleteSpace K] in
/-- Finite monomial sums have continuous images. -/
theorem continuousAt_map_partial_sum
    {T : Type v} [TopologicalSpace T] {x : T}
    {A B : PresentedStrictAffinoidAlgebra K} (φ : T → BoundedAlgHom K A B)
    (hc : ∀ i, ContinuousAt (fun t => φ t (coordinate K A i)) x)
    (f : StrictTateAlgebra (Fin A.arity) K) (s : Finset (Fin A.arity →₀ ℕ)) :
    ContinuousAt (fun t => φ t (presentationMap K A (∑ m ∈ s,
      monomial _ K m (MvPowerSeries.coeff m (series _ K f))))) x := by
  classical
  have heq : (fun t => φ t (presentationMap K A (∑ m ∈ s,
      monomial _ K m (MvPowerSeries.coeff m (series _ K f))))) =
      (fun t => ∑ m ∈ s, φ t (presentationMap K A
        (monomial _ K m (MvPowerSeries.coeff m (series _ K f))))) := by
    funext t
    rw [map_sum, map_sum]
  rw [heq]
  exact tendsto_finsetSum s (fun m _ => continuousAt_map_monomial φ hc m _)

/-- Coordinate continuity and the derived local contraction bound extend to
every section by finite monomial approximation in the quotient norm. -/
theorem continuousAt_map_of_coordinates
    {T : Type v} [TopologicalSpace T] {x : T}
    {A B : PresentedStrictAffinoidAlgebra K} (φ : T → BoundedAlgHom K A B)
    (hc : ∀ i, ContinuousAt (fun t => φ t (coordinate K A i)) x)
    (hx : ∀ i, ‖φ x (coordinate K A i)‖ ≤ 1) (b : A) :
    ContinuousAt (fun t => φ t b) x := by
  classical
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨f, s, hs⟩ := exists_partial_sum_approx A b hε3
  let q := presentationMap K A (∑ m ∈ s,
    monomial _ K m (MvPowerSeries.coeff m (series _ K f)))
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

end PresentedStrictAffinoidAlgebra

namespace StrictTestDomain.RationalData

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K} (d : StrictTestDomain.RationalData K P)

/-- A bounded map preserves the invertibility of the rational denominator. -/
theorem isUnit_map_denominator
    {B : PresentedStrictAffinoidAlgebra K} (φ : BoundedAlgHom K d.algebra B) :
    IsUnit (φ (d.baseMap d.denominator)) := by
  exact (RationalLocalization.isUnit_baseMap_denominator K P d.arity
    d.denominator d.numerator d.generatesUnitIdeal).map φ.toAlgHom

/-- The mapped fractions are determined by inversion of the mapped denominator. -/
theorem map_fraction_eq_inverse_mul
    {B : PresentedStrictAffinoidAlgebra K} (φ : BoundedAlgHom K d.algebra B)
    (j : Fin d.arity) :
    φ (d.fraction j) = Ring.inverse (φ (d.baseMap d.denominator)) *
      φ (d.baseMap (d.numerator j)) := by
  rw [← d.baseMap_denominator_mul_fraction j, map_mul]
  exact (Ring.inverse_mul_cancel_left _ _ (d.isUnit_map_denominator φ)).symm

/-- Continuity on base sections gives continuity on the new fraction coordinates. -/
theorem continuousAt_map_fraction
    {T : Type v} [TopologicalSpace T] {x : T}
    {B : PresentedStrictAffinoidAlgebra K} (φ : T → BoundedAlgHom K d.algebra B)
    (hb : ∀ a : P, ContinuousAt (fun t => φ t (d.baseMap a)) x)
    (j : Fin d.arity) :
    ContinuousAt (fun t => φ t (d.fraction j)) x := by
  obtain ⟨z, hz⟩ := d.isUnit_map_denominator (φ x)
  have hi : ContinuousAt (fun t => Ring.inverse (φ t (d.baseMap d.denominator))) x := by
    have h : ContinuousAt Ring.inverse (φ x (d.baseMap d.denominator)) :=
      hz ▸ NormedRing.inverse_continuousAt z
    exact h.comp (f := fun t => φ t (d.baseMap d.denominator)) (hb d.denominator)
  simp_rw [d.map_fraction_eq_inverse_mul]
  exact hi.mul (hb (d.numerator j))

/-- An old quotient coordinate is the image of an actual base section. -/
theorem baseMap_model_coordinate (i : Fin P.arity) :
    d.baseMap (RationalLocalization.modelEquiv K P
      (coordinate K (RationalLocalization.model K P) i)) =
        coordinate K d.algebra (Fin.castAdd d.arity i) := by
  change RationalPresentation.baseMap K P.arity d.arity P.ideal
    (RationalLocalization.seriesLift K P d.denominator)
    (fun j => RationalLocalization.seriesLift K P (d.numerator j))
    ((RationalLocalization.modelEquiv K P).symm
      (RationalLocalization.modelEquiv K P
        (coordinate K (RationalLocalization.model K P) i))) = _
  rw [BoundedAlgEquiv.symm_apply_apply]
  exact RationalPresentation.baseMap_coordinate K P.arity d.arity P.ideal _ _ i

/-- Continuity on base sections gives continuity on every presentation coordinate
of the rational quotient, including when either arity is zero. -/
theorem continuousAt_map_coordinates
    {T : Type v} [TopologicalSpace T] {x : T}
    {B : PresentedStrictAffinoidAlgebra K} (φ : T → BoundedAlgHom K d.algebra B)
    (hb : ∀ a : P, ContinuousAt (fun t => φ t (d.baseMap a)) x)
    (i : Fin d.algebra.arity) :
    ContinuousAt (fun t => φ t (coordinate K d.algebra i)) x := by
  change Fin (P.arity + d.arity) at i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simpa only [d.baseMap_model_coordinate] using
      hb (RationalLocalization.modelEquiv K P
        (coordinate K (RationalLocalization.model K P) i))
  · exact d.continuousAt_map_fraction φ hb j

end StrictTestDomain.RationalData

namespace PresentedStrictAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/-- Every coordinate in an actual quotient presentation has norm at most one. -/
theorem coordinate_norm_le_one (A : PresentedStrictAffinoidAlgebra K) (i : Fin A.arity) :
    ‖coordinate K A i‖ ≤ 1 := by
  exact (Ideal.Quotient.norm_mk_le A.ideal (X (Fin A.arity) K i)).trans_eq
    (norm_X (Fin A.arity) K i)

/-- For an algebraic action by bounded maps, continuity of every orbit at the
identity implies continuity everywhere, by group translation and a fixed map. -/
theorem continuous_map_of_continuousAt_one
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A : PresentedStrictAffinoidAlgebra K} (φ : G → BoundedAlgHom K A A)
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

end PresentedStrictAffinoidAlgebra

namespace StrictTestDomain.RationalAutomorphism

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K} (d : RationalData K P)
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : G →* locusStabilizer d)
  (hb : ∀ a : P, Continuous (fun g : G => (ρ g : Aut P).hom.toAlgHom a))

omit [IsTopologicalGroup G] in
include hb in
/-- The action's base-section orbits inherit the given base orbit continuity. -/
theorem continuous_section_baseMap (a : P) :
    Continuous (fun g : G => (stabilizerSectionAction d (ρ g)).hom.toAlgHom (d.baseMap a)) := by
  simp_rw [stabilizerSectionAction_baseMap]
  exact d.baseMap.continuous.comp (hb a)

omit [IsTopologicalGroup G] in
include hb in
/-- Each section orbit is continuous at the identity, using the common local
contraction bound derived from the finite rational presentation. -/
theorem continuousAt_section_one (b : d.algebra) :
    ContinuousAt (fun g : G => (stabilizerSectionAction d (ρ g)).hom.toAlgHom b) 1 := by
  apply continuousAt_map_of_coordinates (fun g => (stabilizerSectionAction d (ρ g)).hom)
    (d.continuousAt_map_coordinates _ (fun a =>
      (continuous_section_baseMap d ρ hb a).continuousAt))
  intro i
  change ‖stabilizerSectionMap d (ρ 1) (coordinate K d.algebra i)‖ ≤ 1
  rw [map_one, stabilizerSectionMap_one]
  exact coordinate_norm_le_one d.algebra i

include hb in
/-- The actual fixed rational-quotient action has continuous section orbits. -/
theorem continuous_section_orbit (b : d.algebra) :
    Continuous (fun g : G => (stabilizerSectionAction d (ρ g)).hom.toAlgHom b) := by
  apply continuous_map_of_continuousAt_one
    (fun g => (stabilizerSectionAction d (ρ g)).hom)
    (fun g h => ?_) (continuousAt_section_one d ρ hb) b
  change stabilizerSectionMap d (ρ (g * h)) =
    (stabilizerSectionMap d (ρ g)).comp (stabilizerSectionMap d (ρ h))
  rw [map_mul, stabilizerSectionMap_mul]

/-- Exact two-universe proof of the published section-orbit continuity target. -/
theorem rationalSectionOrbitContinuity : RationalSectionOrbitContinuityStatement.{u,v} := by
  intro K _ _ _ P d G _ _ _ ρ hb b
  exact continuous_section_orbit d ρ hb b

end StrictTestDomain.RationalAutomorphism

end Langlands.Analytic
