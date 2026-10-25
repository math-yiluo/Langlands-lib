import Langlands.ClassFieldTheory.Local.UnitNormProof
import Langlands.ClassFieldTheory.Local.UnitFiltrationStructuralProof
import Langlands.Global.CompletionPadic
import Langlands.Global.AdelicFunctoriality.CompletedRamification
import Mathlib.RingTheory.DedekindDomain.Different

/-! # Local unit norms at unramified finite places

At a finite place `q` of `L` over a finite place `p` of `K` with ramification index one,
every unit of the completed integers of `K` at `p` is the local norm of a unit of the
completed integers of `L` at `q`. The proof transports the published local theorem
`Langlands.LocalClassField.unramifiedUnitNorms` along the `p`-adic-field realizations of the
two completions. Only finitely many finite places of `K` have a ramified place above them.
-/

noncomputable section

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped NumberField WithZero FiniteExtension

universe u v w

section Valuations

/-- Two equivalent valuations of a field onto `ℤᵐ⁰` coincide. -/
theorem valuation_eq_of_isEquiv_of_surjective {R : Type w} [Field R]
    {v₁ v₂ : Valuation R ℤᵐ⁰} (h : v₁.IsEquiv v₂) (h₁ : Function.Surjective v₁)
    (h₂ : Function.Surjective v₂) : v₁ = v₂ := by
  have key : ∀ {γ : ℤᵐ⁰}, γ ≠ 0 → γ < 1 → γ ≤ WithZero.exp (-1) := by
    intro γ h0 h1
    apply WithZero.le_exp_of_log_le
    have : WithZero.log γ < 0 := by
      rw [WithZero.log_lt_iff_lt_exp h0]
      simpa using h1
    omega
  obtain ⟨π, hπ⟩ := h₁ (WithZero.exp (-1))
  obtain ⟨ϖ, hϖ⟩ := h₂ (WithZero.exp (-1))
  have hπ2 : v₂ π = WithZero.exp (-1) := by
    apply le_antisymm
    · apply key
      · rw [Ne, ← h.eq_zero, hπ]
        exact WithZero.exp_ne_zero
      · rw [← h.lt_one_iff_lt_one, hπ]
        simp
    · rw [← hϖ]
      apply (h.le_iff_le).1
      rw [hπ]
      apply key
      · rw [Ne, h.eq_zero, hϖ]
        exact WithZero.exp_ne_zero
      · rw [h.lt_one_iff_lt_one, hϖ]
        simp
  ext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h1x : v₁ x ≠ 0 := by simpa using hx
  have hv1 : v₁ x = v₁ (π ^ (-WithZero.log (v₁ x))) := by
    rw [map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, neg_neg,
      WithZero.exp_log h1x]
  calc v₁ x = v₁ (π ^ (-WithZero.log (v₁ x))) := hv1
    _ = v₂ (π ^ (-WithZero.log (v₁ x))) := by rw [map_zpow₀, map_zpow₀, hπ, hπ2]
    _ = v₂ x := ((h.eq_iff).1 hv1).symm

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{w} p} (T : F.TopologicalData)

/-- If the valuative relation of `T` is the order of a valuation `v`, the canonical valuation
of `T` is equivalent to `v`. -/
theorem valuativeRel_valuation_isEquiv (v : Valuation F.Carrier ℤᵐ⁰)
    (hv : ∀ x y, @ValuativeRel.vle F.Carrier _ T.valuativeRel x y ↔ v x ≤ v y) :
    (letI := T.valuativeRel; ValuativeRel.valuation F.Carrier).IsEquiv v := by
  let := T.valuativeRel
  intro x y
  rw [← Valuation.vle_iff_le]
  exact hv x y

/-- If the valuative relation of `T` is the order of a valuation `v` onto `ℤᵐ⁰`, the normalized
discrete valuation of `T` is `v`. -/
theorem discreteValuation_eq_of_vle (v : Valuation F.Carrier ℤᵐ⁰)
    (hv : ∀ x y, @ValuativeRel.vle F.Carrier _ T.valuativeRel x y ↔ v x ≤ v y)
    (hs : Function.Surjective v) : T.discreteValuation = v := by
  let := T.topology
  let := T.valuativeRel
  have := T.localField
  refine valuation_eq_of_isEquiv_of_surjective ?_ T.discreteValuation_surjective hs
  exact (Valuation.isEquiv_map_self_of_strictMono _
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier).strictMono).trans
    (valuativeRel_valuation_isEquiv T v hv)

/-- Under the same hypothesis, the valuation-unit subgroup of `T` consists of the elements of
`v`-value one. -/
theorem mem_unitSubgroup_iff_of_vle (v : Valuation F.Carrier ℤᵐ⁰)
    (hv : ∀ x y, @ValuativeRel.vle F.Carrier _ T.valuativeRel x y ↔ v x ≤ v y)
    (x : F.Carrierˣ) : x ∈ T.unitSubgroup ↔ v (x : F.Carrier) = 1 := by
  let := T.valuativeRel
  change x ∈ (ValuativeRel.valuation F.Carrier).valuationSubring.unitGroup ↔ _
  rw [Valuation.mem_unitGroup_iff]
  exact (valuativeRel_valuation_isEquiv T v hv).eq_one_iff_eq_one

end Valuations

namespace FiniteExtension

open CompletionPadic

variable {K : Type u} {L : Type v} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  (p : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
  [q.asIdeal.LiesOver p.asIdeal]

section Tower

/-- The continuous ring embedding `ℚ_p → K_p → L_q`. -/
def towerPadicMap : Padic (residuePrime p) →+* q.adicCompletion L :=
  (completionMap p q).comp (padicMap p)

theorem continuous_towerPadicMap : Continuous (towerPadicMap p q) :=
  (continuous_completionMap p q).comp (continuous_padicMap p)

/-- The `ℚ_p`-algebra structure on `L_q` through `K_p`. -/
@[instance_reducible]
def towerPadicAlgebra : Algebra (Padic (residuePrime p)) (q.adicCompletion L) :=
  (towerPadicMap p q).toAlgebra

theorem towerPadicFinite :
    letI := towerPadicAlgebra p q
    FiniteDimensional (Padic (residuePrime p)) (q.adicCompletion L) := by
  let := towerPadicAlgebra p q
  let := padicAlgebra p
  have := padicFinite p
  have : IsScalarTower (Padic (residuePrime p)) (p.adicCompletion K) (q.adicCompletion L) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := local_finite p q
  exact Module.Finite.trans (p.adicCompletion K) (q.adicCompletion L)

/-- `L_q` as a finite extension of `ℚ_p`, where `p` is the residue characteristic of the
place `p` of `K` below `q`. -/
abbrev towerPadicField : PadicField.{v} (residuePrime p) where
  Carrier := q.adicCompletion L
  algebra := towerPadicAlgebra p q
  finiteDimensional := towerPadicFinite p q

/-- The completion topology of `L_q` is the `ℚ_p`-module topology for the tower structure. -/
theorem tower_isModuleTopology :
    letI := towerPadicAlgebra p q
    IsModuleTopology (Padic (residuePrime p)) (q.adicCompletion L) := by
  let := towerPadicAlgebra p q
  have := towerPadicFinite p q
  have : ContinuousSMul (Padic (residuePrime p)) (q.adicCompletion L) :=
    continuousSMul_of_algebraMap _ _ (continuous_towerPadicMap p q)
  exact isModuleTopologyOfFiniteDimensional

theorem tower_topology_eq :
    inferInstanceAs (TopologicalSpace (q.adicCompletion L)) =
      (towerPadicField p q).canonicalTopologicalData.topology := by
  rw [PadicField.canonicalTopologicalData_topology]
  let := towerPadicAlgebra p q
  have := tower_isModuleTopology p q
  exact eq_moduleTopology (Padic (residuePrime p)) (q.adicCompletion L)

theorem tower_valued_lt_one_iff (x : q.adicCompletion L) :
    Valued.v x < 1 ↔ (towerPadicField p q).canonicalNorm x < 1 := by
  have h₁ : Valued.v x < 1 ↔ Tendsto (fun n : ℕ => x ^ n) atTop (nhds 0) :=
    Valued.toNormedField.norm_lt_one_iff.symm.trans
      tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.symm
  have h₂ : (towerPadicField p q).canonicalNorm x < 1 ↔
      Tendsto (fun n : ℕ => x ^ n) atTop
        (@nhds _ (towerPadicField p q).canonicalTopologicalData.topology 0) :=
    @norm_lt_one_iff_tendsto_pow _ (towerPadicField p q).canonicalNormedField.toNormedField x
  rw [← tower_topology_eq p q] at h₂
  exact h₁.trans h₂.symm

theorem tower_valued_isEquiv :
    (Valued.v : Valuation (q.adicCompletion L) ℤᵐ⁰).IsEquiv
      (towerPadicField p q).canonicalValuation :=
  Valuation.isEquiv_iff_val_lt_one.mpr fun {x} => (tower_valued_lt_one_iff p q x).trans <| by
    rw [← PadicField.canonicalValuation_coe, NNReal.coe_lt_one]

/-- The local-field realization of `L_q` over `ℚ_p` whose topology is the completion
topology. -/
def towerTopologicalData : (towerPadicField p q).TopologicalData where
  topology := inferInstanceAs (TopologicalSpace (q.adicCompletion L))
  valuativeRel := (towerPadicField p q).canonicalTopologicalData.valuativeRel
  valuativeExtension := (towerPadicField p q).canonicalTopologicalData.valuativeExtension
  moduleTopology := tower_isModuleTopology p q
  localField := by
    have h := (towerPadicField p q).canonicalTopologicalData.localField
    rw [← tower_topology_eq p q] at h
    exact h

/-- The valuative relation of `towerTopologicalData p q` is the completion's valuation order. -/
theorem towerTopologicalData_vle (x y : q.adicCompletion L) :
    @ValuativeRel.vle (towerPadicField p q).Carrier _ (towerTopologicalData p q).valuativeRel
      x y ↔ Valued.v x ≤ Valued.v y := by
  refine ((towerPadicField p q).canonicalTopologicalData_vle x y).trans ?_
  rw [← PadicField.canonicalValuation_coe,
    ← PadicField.canonicalValuation_coe, NNReal.coe_le_coe]
  exact (tower_valued_isEquiv p q x y).symm

end Tower

section Norms

/-- The normalized order of the base realization is minus the logarithm of the completion
valuation. -/
theorem topologicalData_discreteValuation :
    (topologicalData p).discreteValuation = (Valued.v : Valuation (p.adicCompletion K) ℤᵐ⁰) :=
  discreteValuation_eq_of_vle (topologicalData p) Valued.v (topologicalData_vle p)
    (p.valuedAdicCompletion_surjective K)

theorem towerTopologicalData_discreteValuation :
    (towerTopologicalData p q).discreteValuation =
      (Valued.v : Valuation (q.adicCompletion L) ℤᵐ⁰) :=
  discreteValuation_eq_of_vle (towerTopologicalData p q) Valued.v (towerTopologicalData_vle p q)
    (q.valuedAdicCompletion_surjective L)

/-- With ramification index one, the two realizations have the same absolute ramification
index over `ℚ_p`. -/
theorem ramificationIndex_eq_of_ramificationIdx_eq_one
    (he : q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    (topologicalData p).ramificationIndex = (towerTopologicalData p q).ramificationIndex := by
  unfold PadicField.TopologicalData.ramificationIndex PadicField.TopologicalData.ord
  rw [topologicalData_discreteValuation, towerTopologicalData_discreteValuation]
  have hcast : ((residuePrime p : ℕ) : (towerPadicField p q).Carrier) =
      completionMap p q ((residuePrime p : ℕ) : (padicField p).Carrier) :=
    (map_natCast (completionMap p q) _).symm
  rw [hcast, valuation_completionMap, he, pow_one]

/-- At a place with ramification index one, every valuation unit of `K_p` is the local norm of
a valuation unit of `L_q`. -/
theorem exists_localNorm_eq_of_ramificationIdx_eq_one
    (he : q.asIdeal.ramificationIdx (𝓞 K) = 1) (u : (p.adicCompletion K)ˣ)
    (hu : Valued.v (u : p.adicCompletion K) = 1) :
    ∃ c : (q.adicCompletion L)ˣ, Valued.v (c : q.adicCompletion L) = 1 ∧
      localNorm p q c = u := by
  let : Algebra (Padic (residuePrime p)) (padicField p).Carrier := padicAlgebra p
  let : Algebra (Padic (residuePrime p)) (towerPadicField p q).Carrier := towerPadicAlgebra p q
  have : IsScalarTower (Padic (residuePrime p)) (padicField p).Carrier
      (towerPadicField p q).Carrier := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional (padicField p).Carrier (towerPadicField p q).Carrier :=
    local_finite p q
  have h := LocalClassField.unramifiedUnitNorms (residuePrime p) (padicField p)
    (towerPadicField p q) (topologicalData p) (towerTopologicalData p q)
    (ramificationIndex_eq_of_ramificationIdx_eq_one p q he) 0
  rw [PadicField.TopologicalData.unitFiltration_zero,
    PadicField.TopologicalData.unitFiltration_zero] at h
  have hu' : u ∈ (topologicalData p).unitSubgroup :=
    (mem_unitSubgroup_iff_of_vle (topologicalData p) Valued.v (topologicalData_vle p) u).2 hu
  rw [← h] at hu'
  obtain ⟨c, hc, hcu⟩ := hu'
  exact ⟨c, (mem_unitSubgroup_iff_of_vle (towerTopologicalData p q) Valued.v
    (towerTopologicalData_vle p q) c).1 hc, congrArg Units.val hcu⟩

end Norms

end FiniteExtension

section Ramified

variable (K : Type u) (L : Type v) [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

/-- Only finitely many finite places of `L` are ramified over `K`: a ramified place divides the
different ideal of `𝓞 L` over `𝓞 K`, which is nonzero. -/
theorem finite_setOf_ramificationIdx_ne_one :
    {q : HeightOneSpectrum (𝓞 L) | q.asIdeal.ramificationIdx (𝓞 K) ≠ 1}.Finite := by
  have hne : differentIdeal (𝓞 K) (𝓞 L) ≠ 0 := by
    rw [Ideal.zero_eq_bot]
    exact differentIdeal_ne_bot
  refine (Ideal.finite_factors hne).subset fun q hq => ?_
  by_contra hdvd
  have := (not_dvd_differentIdeal_iff (A := 𝓞 K) (P := q.asIdeal)).1 hdvd
  exact hq (Ideal.ramificationIdx_eq_one q.asIdeal (𝓞 K))

/-- For all but finitely many finite places `p` of `K`, every finite place of `L` above `p`
has ramification index one. -/
theorem eventually_ramificationIdx_eq_one :
    ∀ᶠ p : HeightOneSpectrum (𝓞 K) in cofinite, ∀ q : HeightOneSpectrum (𝓞 L),
      q.asIdeal.LiesOver p.asIdeal → q.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  refine Filter.eventually_cofinite.2 (((finite_setOf_ramificationIdx_ne_one K L).image
    fun q => q.under (𝓞 K)).subset ?_)
  intro p hp
  simp only [Set.mem_ofPred_eq, not_forall] at hp
  obtain ⟨q, hq, hne⟩ := hp
  exact ⟨q, hne, HeightOneSpectrum.ext hq.over.symm⟩

end Ramified

end Langlands.Global.AdelicFunctoriality
