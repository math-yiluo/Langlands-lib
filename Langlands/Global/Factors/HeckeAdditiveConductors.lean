import Langlands.Global.Factors.HeckeLocalNontrivial
import Langlands.Global.Factors.HeckeFiniteEpsilon
import Langlands.Global.IntegralFiniteAdeles

/-! # Finite additive conductors from the actual adelic pairing -/

noncomputable section

open Filter Topology

namespace Langlands.Global.HeckeFunctionalEquation

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- Every compact set of actual adeles is integral, uniformly over that set,
outside a finite set of finite places. -/
theorem eventually_integral_on_isCompact {C : Set (Adeles K)} (hC : IsCompact C) :
    ∀ᶠ v : FinitePlace K in cofinite, ∀ a ∈ C,
      finiteProjection K v a ∈ v.adicCompletionIntegers K := by
  classical
  let U (a : Adeles K) : Set (Adeles K) :=
    {x | x.2 - a.2 ∈ integralFiniteAdeles K}
  have hU (a : Adeles K) : IsOpen (U a) :=
    (isOpen_integralFiniteAdeles K).preimage (continuous_snd.sub continuous_const)
  have hcover : C ⊆ ⋃ a, U a := by
    intro a _
    apply Set.mem_iUnion.mpr
    refine ⟨a, ?_⟩
    change a.2 - a.2 ∈ integralFiniteAdeles K
    rw [sub_self]
    exact (integralFiniteAdeles K).zero_mem
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover U hU hcover
  have hrep : ∀ᶠ v : FinitePlace K in cofinite, ∀ a ∈ t,
      finiteProjection K v a ∈ v.adicCompletionIntegers K := by
    apply (Filter.eventually_all_finset t).mpr
    intro a _
    exact a.2.2
  filter_upwards [hrep] with v hv a ha
  obtain ⟨b, hbt, hab⟩ := Set.mem_iUnion₂.mp (ht ha)
  have hdiff := (mem_integralFiniteAdeles K _).mp hab v
  have hsum := add_mem hdiff (hv b hbt)
  change (a.2 v - b.2 v) + b.2 v ∈ v.adicCompletionIntegers K at hsum
  change a.2 v ∈ v.adicCompletionIntegers K
  simpa only [sub_add_cancel] using hsum

section Local

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

/-- An inverse uniformizer is outside the specified valuation integers. -/
theorem inverse_uniformizer_not_mem_integers :
    T.uniformizer⁻¹ ∉ T.Integers := by
  rw [T.mem_integers_iff_discreteValuation_le_one, map_inv₀,
    T.discreteValuation_uniformizer]
  simp

/-- At additive conductor at least one, scaling any integer by an inverse
uniformizer gives a trivial character value. -/
theorem inverse_uniformizer_mul_eq_one
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (hn : 1 ≤ T.additiveConductor ψ) (x : F.Carrier) (hx : x ∈ T.Integers) :
    ψ (T.uniformizer⁻¹ * x) = 1 := by
  apply ((T.additiveTrivialAt_iff_le_conductor ψ 1).mpr hn)
  rw [T.mem_additiveLattice, map_mul, map_inv₀, T.discreteValuation_uniformizer]
  simpa only [WithZero.inv_exp, neg_neg, mul_one] using
    mul_le_mul_of_nonneg_left ((T.mem_integers_iff_discreteValuation_le_one x).mp hx)
      (show (0 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp 1 from zero_le)

end Local

section Global

variable (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K))
    (e : Multiplicative (Adeles K) ≃ₜ* PontryaginDual (Multiplicative (Adeles K)))
    (he : ∀ a x : Multiplicative (Adeles K),
      e a x = ψ (Multiplicative.toAdd a * Multiplicative.toAdd x))
    (ψf : ∀ v : FinitePlace K,
      @HarmonicAnalysis.UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (CompletionPadic.topologicalData v).topology)
    (hψf : ∀ v, IsFiniteAdditiveComponent ψ v (ψf v))

/-- A single-place inverse uniformizer when the additive conductor is positive,
and zero otherwise. -/
def conductorProbe (v : FinitePlace K) : Adeles K :=
  finiteAdditiveInclusion K v
    (if 1 ≤ (CompletionPadic.topologicalData v).additiveConductor (ψf v) then
      (CompletionPadic.topologicalData v).uniformizer⁻¹ else 0)

include hψf in
/-- Each probe is annihilated by adeles integral at its chosen place. -/
theorem conductorProbe_pairing_eq_one (v : FinitePlace K) (a : Adeles K)
    (ha : finiteProjection K v a ∈ v.adicCompletionIntegers K) :
    ψ (conductorProbe ψf v * a) = 1 := by
  classical
  unfold conductorProbe
  rw [finiteAdditiveInclusion_mul]
  have hcomp (x : FiniteCompletion K v) :
      ψf v x = ψ (finiteAdditiveInclusion K v x) := hψf v x
  rw [← hcomp]
  split_ifs with hn
  · exact inverse_uniformizer_mul_eq_one (CompletionPadic.topologicalData v)
      (ψf v) hn _ ((mem_localIntegers_iff v _).mpr ha)
  · change (ψf v).toAddChar (0 * finiteProjection K v a) = 1
    simp

include e he hψf in
/-- Topological duality forces the additive conductor to be nonpositive outside
a finite set: the dual characters of positive-conductor probes tend to one. -/
theorem eventually_additiveConductor_nonpos_of_pairing :
    ∀ᶠ v : FinitePlace K in cofinite,
      (CompletionPadic.topologicalData v).additiveConductor (ψf v) ≤ 0 := by
  classical
  let f (v : FinitePlace K) : PontryaginDual (Multiplicative (Adeles K)) :=
    e (Multiplicative.ofAdd (conductorProbe ψf v))
  let g (v : FinitePlace K) : C(Multiplicative (Adeles K), Circle) :=
    (f v : Multiplicative (Adeles K) →ₜ* Circle).toContinuousMap
  have hg : Tendsto g cofinite (𝓝 (1 : C(Multiplicative (Adeles K), Circle))) := by
    apply ContinuousMap.tendsto_nhds_compactOpen.mpr
    intro C hC U _hU hU
    have hint := eventually_integral_on_isCompact
      (hC.image (show Continuous (Multiplicative.toAdd : Multiplicative (Adeles K) → Adeles K)
        from continuous_id))
    filter_upwards [hint] with v hv
    intro x hx
    have hvalue : g v x = 1 := by
      change e (Multiplicative.ofAdd (conductorProbe ψf v)) x = 1
      rw [he]
      exact conductorProbe_pairing_eq_one ψ ψf hψf v (Multiplicative.toAdd x)
        (hv _ ⟨x, hx, rfl⟩)
    rw [hvalue]
    exact hU hx
  have hf : Tendsto f cofinite (𝓝 (1 : PontryaginDual (Multiplicative (Adeles K)))) := by
    change Tendsto (fun v => (f v : Multiplicative (Adeles K) →ₜ* Circle)) cofinite
      (𝓝 (1 : Multiplicative (Adeles K) →ₜ* Circle))
    exact (ContinuousMonoidHom.isInducing_toContinuousMap _ _).tendsto_nhds_iff.mpr hg
  have hprobes : Tendsto (fun v => conductorProbe ψf v) cofinite (𝓝 (0 : Adeles K)) := by
    change Tendsto (fun v => Multiplicative.ofAdd (conductorProbe ψf v)) cofinite
      (𝓝 (1 : Multiplicative (Adeles K)))
    have h := (e.symm.continuous.tendsto (1 : PontryaginDual (Multiplicative (Adeles K)))).comp hf
    change Tendsto (fun v => e.symm (e (Multiplicative.ofAdd (conductorProbe ψf v))))
      cofinite (𝓝 (e.symm 1)) at h
    simpa only [e.symm_apply_apply, map_one] using h
  have hzero : (0 : Adeles K) ∈ {a : Adeles K | a.2 ∈ integralFiniteAdeles K} :=
    (integralFiniteAdeles K).zero_mem
  have hint := hprobes.eventually
    (((isOpen_integralFiniteAdeles K).preimage continuous_snd).mem_nhds hzero)
  filter_upwards [hint] with v hv
  by_contra hn
  have hn' : 1 ≤ (CompletionPadic.topologicalData v).additiveConductor (ψf v) := by
    omega
  have hcoord := (mem_integralFiniteAdeles K _).mp hv v
  change (Pi.single v
    (if 1 ≤ (CompletionPadic.topologicalData v).additiveConductor (ψf v) then
      (CompletionPadic.topologicalData v).uniformizer⁻¹ else 0) :
      ∀ w, FiniteCompletion K w) v ∈ v.adicCompletionIntegers K at hcoord
  simp only [Pi.single_eq_same, ite_eq_left hn'] at hcoord
  exact inverse_uniformizer_not_mem_integers (CompletionPadic.topologicalData v)
    ((mem_localIntegers_iff v _).mpr hcoord)

include hψf in
/-- Continuity of the global character makes the additive conductors
nonnegative almost everywhere, for every actual supplied component family. -/
theorem eventually_additiveConductor_nonneg :
    ∀ᶠ v : FinitePlace K in cofinite,
      0 ≤ (CompletionPadic.topologicalData v).additiveConductor (ψf v) := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_integral_restriction_eq_one ψ
  filter_upwards [S.eventually_cofinite_notMem] with v hv
  apply ((CompletionPadic.topologicalData v).additiveTrivialAt_iff_le_conductor
    (ψf v) 0).mp
  intro x hx
  have hxO := ((CompletionPadic.topologicalData v).mem_additiveLattice_zero x).mp hx
  have h := hS v hv ⟨x, (mem_localIntegers_iff v x).mp hxO⟩
  exact (hψf v x).trans h

include e he hψf in
/-- Every supplied actual component family has additive conductor zero at
almost every finite place, under the exact topological pairing hypothesis. -/
theorem eventually_additiveConductor_eq_zero_of_pairing :
    ∀ᶠ v : FinitePlace K in cofinite,
      (CompletionPadic.topologicalData v).additiveConductor (ψf v) = 0 := by
  filter_upwards [eventually_additiveConductor_nonpos_of_pairing ψ e he ψf hψf,
    eventually_additiveConductor_nonneg ψ ψf hψf] with v hupper hlower
  exact le_antisymm hupper hlower

include e he hψf in
/-- A finite exceptional set for the additive conductors of every supplied
actual component family. -/
theorem exists_finset_additiveConductor_eq_zero_of_pairing :
    ∃ S : Finset (FinitePlace K), ∀ v ∉ S,
      (CompletionPadic.topologicalData v).additiveConductor (ψf v) = 0 := by
  classical
  have hfin := Filter.eventually_cofinite.mp
    (eventually_additiveConductor_eq_zero_of_pairing ψ e he ψf hψf)
  refine ⟨hfin.toFinset, fun v hv => ?_⟩
  by_contra hn
  exact hv (hfin.mem_toFinset.mpr hn)

include e he hψf in
/-- The exact finite-epsilon exceptional-set conclusion of the global target,
under actual topological duality, for all supplied self-dual Haar measures. -/
theorem exists_finset_finiteEpsilon_eq_one_of_pairing (χ : HeckeCharacter K)
    (μ : ∀ v : FinitePlace K,
      LocalFactor.PadicAbelian.SelfDualHaar (CompletionPadic.topologicalData v) (ψf v)) :
    ∃ S : Finset (FinitePlace K), ∀ v ∉ S, ∀ s : ℂ,
      finiteEpsilon χ ψf μ v s = 1 := by
  obtain ⟨S, hS⟩ := exists_finset_additiveConductor_eq_zero_of_pairing ψ e he ψf hψf
  exact exists_finset_finiteEpsilon_eq_one_of_additiveConductor χ ψf μ S hS

end Global

end Langlands.Global.HeckeFunctionalEquation
