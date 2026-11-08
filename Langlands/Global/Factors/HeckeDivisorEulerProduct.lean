import Langlands.Global.Factors.DivisorEulerProduct
import Langlands.Global.Factors.HeckeEulerProduct
import Langlands.Global.Factors.HeckeFiniteEpsilon
import Langlands.LocalFactor.Abelian.EulerTestShells
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Filter Topology NumberField
open Langlands.LocalFactor.PadicAbelian
open Langlands.Global.CompletionPadic

namespace Langlands.Global.HeckeDivisorEulerProduct

universe u

section Series

variable {ι : Type u}

/-- The mass of the strictly positive part of a real geometric series. -/
theorem hasSum_positive_geometric {r : ℝ} (hr : 0 ≤ r) (h1 : r < 1) :
    HasSum (fun k : ℤ => if 0 < k then r ^ k else 0) (r / (1 - r)) := by
  have hpos : HasSum (fun n : ℕ => if 0 < (n : ℤ) then r ^ (n : ℤ) else 0)
      (r / (1 - r)) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_one, Int.natCast_zero, lt_self_iff_false, ite_false, sub_zero]
    convert (hasSum_geometric_of_lt_one hr h1).mul_left r using 1
    · funext n
      rw [ite_eq_left (by omega), zpow_natCast, pow_succ]
      ring
    · exact div_eq_mul_inv _ _
  have hneg : HasSum (fun n : ℕ => if 0 < -((n : ℤ) + 1) then
      r ^ (-((n : ℤ) + 1)) else 0) 0 := by
    convert (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0) using 1
    funext n
    rw [ite_eq_right (by omega)]
  simpa only [add_zero] using
    (HasSum.of_nat_of_neg_add_one (f := fun k : ℤ => if 0 < k then r ^ k else 0)
      hpos hneg)

/-- Joint absolute convergence of positive geometric tails follows from summability
of their first coefficients and pointwise strict contraction. -/
theorem summable_positive_geometric (z : ι → ℂ)
    (hz : Summable (fun i => ‖z i‖)) (h1 : ∀ i, ‖z i‖ < 1) :
    Summable (fun p : ι × ℤ => if 0 < p.2 then ‖z p.1‖ ^ p.2 else 0) := by
  refine (summable_prod_of_nonneg (fun p => by split_ifs <;> positivity)).mpr ⟨?_, ?_⟩
  · intro i
    exact (hasSum_positive_geometric (norm_nonneg _) (h1 i)).summable
  · have hs : Summable (fun i => ‖z i‖ / (1 - ‖z i‖)) := by
      apply (hz.mul_left 2).of_norm_bounded_eventually
      filter_upwards [hz.tendsto_cofinite_zero.eventually (gt_mem_nhds (by norm_num :
        (0 : ℝ) < 1 / 2))] with i hi
      rw [Real.norm_eq_abs, abs_of_nonneg
        (div_nonneg (norm_nonneg _) (sub_nonneg.mpr (h1 i).le))]
      apply (div_le_iff₀ (by linarith : 0 < 1 - ‖z i‖)).mpr
      nlinarith [norm_nonneg (z i)]
    exact hs.congr fun i => (hasSum_positive_geometric (norm_nonneg _) (h1 i)).tsum_eq.symm

/-- Changing finitely many local series preserves joint summability away from zero. -/
theorem summable_nonzero_of_eq_off_finset (S : Finset ι) (h g : ι → ℤ → ℂ)
    (hg : Summable (fun p : ι × ℤ => if p.2 = 0 then (0 : ℝ) else ‖g p.1 p.2‖))
    (hh : ∀ i, Summable (fun k => ‖h i k‖))
    (heq : ∀ i ∉ S, h i = g i) :
    Summable (fun p : ι × ℤ => if p.2 = 0 then (0 : ℝ) else ‖h p.1 p.2‖) := by
  classical
  have hgs := (summable_prod_of_nonneg (fun p => by split_ifs <;> positivity)).mp hg
  refine (summable_prod_of_nonneg (fun p => by split_ifs <;> positivity)).mpr ⟨?_, ?_⟩
  · intro i
    apply (hh i).congr_cofinite
    filter_upwards [eventually_cofinite_ne (0 : ℤ)] with k hk
    exact (ite_eq_right hk).symm
  · apply hgs.2.congr_cofinite
    filter_upwards [S.eventually_cofinite_notMem] with i hi
    rw [heq i hi]

end Series

variable {K : Type u} [Field K] [NumberField K]

/-- The actual finite Euler test's Mellin coefficient at a uniformizer power. -/
def shellWeight (χ : HeckeCharacter K) (v : FinitePlace K) (s : ℂ) (k : ℤ) : ℂ :=
  shellMellinTerm (topologicalData v) (eulerTest (topologicalData v) (χ.finiteComponent v))
    (χ.finiteComponent v) s k

/-- The unramified geometric coefficient before suppressing ramified places. -/
def geometricCoefficient (χ : HeckeCharacter K) (v : FinitePlace K) (s : ℂ) : ℂ :=
  (χ.finiteComponent v (uniformizerUnit (topologicalData v)) : ℂ) *
    spectralVariable (topologicalData v) s

@[simp] theorem shellWeight_zero (χ : HeckeCharacter K) (v : FinitePlace K) (s : ℂ) :
    shellWeight χ v s 0 = 1 := by
  classical
  by_cases hc : (topologicalData v).multiplicativeConductor (χ.finiteComponent v) = 0
  · rw [shellWeight, shellMellinTerm,
      eulerTest_uniformizer_pow_unramified (topologicalData v) _ hc]
    simp
  · rw [shellWeight, shellMellinTerm,
      eulerTest_uniformizer_pow_ramified (topologicalData v) _ hc]
    simp

theorem shellWeight_nonzero_norm_le (χ : HeckeCharacter K) (v : FinitePlace K)
    (s : ℂ) (k : ℤ) :
    (if k = 0 then (0 : ℝ) else ‖shellWeight χ v s k‖) ≤
      if 0 < k then ‖geometricCoefficient χ v s‖ ^ k else 0 := by
  classical
  by_cases hc : (topologicalData v).multiplicativeConductor (χ.finiteComponent v) = 0
  · rw [shellWeight, shellMellinTerm,
      eulerTest_uniformizer_pow_unramified (topologicalData v) _ hc]
    by_cases hk : k = 0
    · simp [hk]
    · by_cases hp : 0 < k
      · simp [hk, hp, le_of_lt hp, geometricCoefficient, norm_zpow]
      · simp [hk, hp, show ¬0 ≤ k by omega]
  · rw [shellWeight, shellMellinTerm,
      eulerTest_uniformizer_pow_ramified (topologicalData v) _ hc]
    by_cases hk : k = 0
    · simp [hk]
    · simp only [ite_eq_right hk, zero_mul, norm_zero]
      split_ifs <;> positivity

theorem norm_geometricCoefficient (χ : HeckeCharacter K) {β : ℝ}
    (hβ : ∀ v : FinitePlace K,
      ‖(χ.finiteComponent v (uniformizerUnit (topologicalData v)) : ℂ)‖ =
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-β))
    (v : FinitePlace K) (s : ℂ) :
    ‖geometricCoefficient χ v s‖ =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-(β + s.re)) := by
  have hN : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (zero_lt_one.trans this)
  rw [geometricCoefficient, norm_mul, hβ, HeckeEulerProduct.norm_spectralVariable,
    ← Real.rpow_add hN, neg_add]

/-- On one right half-plane all actual local geometric coefficients are strictly
contracting and their norms are summable. -/
theorem exists_geometric_convergence (χ : HeckeCharacter K) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Summable (fun v => ‖geometricCoefficient χ v s‖) ∧
        ∀ v, ConvergesAt (topologicalData v) (uniformizerUnit (topologicalData v))
          (χ.finiteComponent v) s := by
  obtain ⟨β, hβ⟩ := HeckeEulerProduct.exists_norm_finiteComponent_uniformizer χ
  refine ⟨1 - β, fun s hs => ?_⟩
  have hσ : 1 < β + s.re := by linarith
  constructor
  · simpa only [norm_geometricCoefficient χ hβ] using
      (HeckeEulerProduct.summable_absNorm_rpow (K := K) hσ)
  · intro v
    apply (convergesAt_iff_norm_lt_one (topologicalData v) _ _ _).mpr
    change ‖geometricCoefficient χ v s‖ < 1
    rw [norm_geometricCoefficient χ hβ]
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    · linarith

/-- The actual local Euler-test weights are jointly absolutely summable away
from their zero-index terms on the geometric convergence half-plane. -/
theorem summable_nonzero_shellWeight (χ : HeckeCharacter K) (s : ℂ)
    (hsum : Summable (fun v => ‖geometricCoefficient χ v s‖))
    (hconv : ∀ v, ConvergesAt (topologicalData v) (uniformizerUnit (topologicalData v))
      (χ.finiteComponent v) s) :
    Summable (fun p : FinitePlace K × ℤ =>
      if p.2 = 0 then (0 : ℝ) else ‖shellWeight χ p.1 s p.2‖) := by
  have hlt : ∀ v, ‖geometricCoefficient χ v s‖ < 1 := fun v =>
    (convergesAt_iff_norm_lt_one (topologicalData v) _ _ _).mp (hconv v)
  exact
    (summable_positive_geometric (fun v => geometricCoefficient χ v s) hsum hlt).of_nonneg_of_le
        (fun p => by split_ifs <;> positivity)
        (fun p => shellWeight_nonzero_norm_le χ p.1 s p.2)

/-- The actual Euler-test divisor series converges absolutely and has the exact
finite local Euler product on a right half-plane. -/
theorem exists_hasProd_shellWeight (χ : HeckeCharacter K) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Summable (fun d : FinitePlace K →₀ ℤ =>
        ‖DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ v s) d‖) ∧
      HasProd (fun v => lFactor (topologicalData v) (χ.finiteComponent v) s)
        (∑' d : FinitePlace K →₀ ℤ,
          DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ v s) d) := by
  classical
  obtain ⟨σ, hσ⟩ := exists_geometric_convergence χ
  refine ⟨σ, fun s hs => ?_⟩
  obtain ⟨hsum, hconv⟩ := hσ s hs
  have hj := summable_nonzero_shellWeight χ s hsum hconv
  refine ⟨DivisorEulerProduct.summable_norm_coefficient ∅ _ hj, ?_⟩
  convert DivisorEulerProduct.hasProd_tsum ∅ (fun v => shellWeight χ v s)
    (fun v _ => shellWeight_zero χ v s) hj using 1
  funext v
  exact (hasSum_eulerTest (topologicalData v) (χ.finiteComponent v) s (hconv v)).tsum_eq.symm

section Fourier

variable
    (χ : HeckeCharacter K)
    (ψf : ∀ v : FinitePlace K,
      @HarmonicAnalysis.UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (topologicalData v).topology)
    (μ : ∀ v : FinitePlace K, SelfDualHaar (topologicalData v) (ψf v))

/-- The actual Fourier-transformed finite Euler test's dual Mellin coefficient. -/
def fourierShellWeight (v : FinitePlace K) (s : ℂ) (k : ℤ) : ℂ :=
  let := (topologicalData v).topology
  let := (topologicalData v).valuativeRel
  let := (topologicalData v).localField
  let := borel (FiniteCompletion K v)
  let : BorelSpace (FiniteCompletion K v) := ⟨rfl⟩
  shellMellinTerm (topologicalData v)
    (HarmonicAnalysis.fourierTransform (ψf v) (μ v).val
      (eulerTest (topologicalData v) (χ.finiteComponent v)))
    (χ.finiteComponent v)⁻¹ s k

theorem hasSum_fourierShellWeight (v : FinitePlace K) (s : ℂ)
    (hs : ConvergesAt (topologicalData v) (uniformizerUnit (topologicalData v))
      (χ⁻¹.finiteComponent v) s) :
    HasSum (fourierShellWeight χ ψf μ v s)
      (HeckeFunctionalEquation.finiteEpsilon χ ψf μ v (1 - s) *
        lFactor (topologicalData v) (χ⁻¹.finiteComponent v) s) := by
  exact hasSum_fourier_eulerTest (topologicalData v) (χ.finiteComponent v)
    (ψf v) (μ v).val s hs

/-- At zero additive and multiplicative conductors, the Fourier weight is exactly
the original weight for the inverse Hecke character, for every supplied self-dual Haar. -/
theorem fourierShellWeight_eq_shellWeight_inv (v : FinitePlace K)
    (hχ : (topologicalData v).multiplicativeConductor (χ.finiteComponent v) = 0)
    (hψ : (topologicalData v).additiveConductor (ψf v) = 0) (s : ℂ) :
    fourierShellWeight χ ψf μ v s = shellWeight χ⁻¹ v s := by
  let := (topologicalData v).topology
  let := (topologicalData v).valuativeRel
  let := (topologicalData v).localField
  let := borel (FiniteCompletion K v)
  let : BorelSpace (FiniteCompletion K v) := ⟨rfl⟩
  have hμ : ((μ v).val.measure (integerRing (topologicalData v))).toReal = 1 := by
    rw [HeckeFunctionalEquation.selfDualHaar_integerRing_eq_one
      (topologicalData v) (ψf v) (μ v) hψ, ENNReal.toReal_one]
  have hinv : (topologicalData v).multiplicativeConductor (χ⁻¹.finiteComponent v) = 0 := by
    rw [HeckeCharacter.finiteComponent_inv, multiplicativeConductor_inv_eq, hχ]
  have heq : (eulerTest (topologicalData v) (χ.finiteComponent v) :
      FiniteCompletion K v → ℂ) =
      (eulerTest (topologicalData v) (χ⁻¹.finiteComponent v) : FiniteCompletion K v → ℂ) := by
    rw [eulerTest_coe, eulerTest_coe, ite_eq_left hχ, ite_eq_left hinv]
  funext k
  change shellMellinTerm (topologicalData v)
    (HarmonicAnalysis.fourierTransform (ψf v) (μ v).val
      (eulerTest (topologicalData v) (χ.finiteComponent v)))
    (χ.finiteComponent v)⁻¹ s k =
      shellMellinTerm (topologicalData v) (eulerTest (topologicalData v) (χ⁻¹.finiteComponent v))
        (χ⁻¹.finiteComponent v) s k
  rw [fourier_eulerTest_eq_self (topologicalData v) (χ.finiteComponent v) hχ
    (ψf v) hψ (μ v).val hμ, heq]
  rfl

/-- Given a finite additive-conductor exceptional set, the actual Fourier divisor
series converges absolutely and equals epsilon times the dual local Euler product. -/
theorem exists_hasProd_fourierShellWeight
    (Sψ : Finset (FinitePlace K))
    (hψ : ∀ v ∉ Sψ, (topologicalData v).additiveConductor (ψf v) = 0) :
    ∃ (σ : ℝ) (S : Finset (FinitePlace K)),
      (∀ v ∉ S, ∀ s : ℂ, fourierShellWeight χ ψf μ v s 0 = 1) ∧
      (∀ v ∉ S, ∀ s : ℂ, HeckeFunctionalEquation.finiteEpsilon χ ψf μ v s = 1) ∧
      ∀ s : ℂ, σ < s.re →
        Summable (fun d : FinitePlace K →₀ ℤ =>
          ‖DivisorEulerProduct.coefficient S (fun v => fourierShellWeight χ ψf μ v s) d‖) ∧
        HasProd (fun v =>
          HeckeFunctionalEquation.finiteEpsilon χ ψf μ v (1 - s) *
            lFactor (topologicalData v) (χ⁻¹.finiteComponent v) s)
          (∑' d : FinitePlace K →₀ ℤ,
            DivisorEulerProduct.coefficient S (fun v => fourierShellWeight χ ψf μ v s) d) := by
  classical
  obtain ⟨Sχ, hχ⟩ := HeckeFunctionalEquation.exists_finset_isUnramifiedAt K χ
  let S := Sχ ∪ Sψ
  have hc (v : FinitePlace K) (hv : v ∉ S) :
      (topologicalData v).multiplicativeConductor (χ.finiteComponent v) = 0 :=
    HeckeFunctionalEquation.multiplicativeConductor_eq_zero_of_isUnramifiedAt χ v
      (hχ v (fun h => hv (Finset.mem_union_left _ h)))
  have hn (v : FinitePlace K) (hv : v ∉ S) :
      (topologicalData v).additiveConductor (ψf v) = 0 :=
    hψ v (fun h => hv (Finset.mem_union_right _ h))
  have heq (v : FinitePlace K) (hv : v ∉ S) (s : ℂ) :=
    fourierShellWeight_eq_shellWeight_inv χ ψf μ v (hc v hv) (hn v hv) s
  obtain ⟨σ, hσ⟩ := exists_geometric_convergence χ⁻¹
  refine ⟨σ, S, ?_, ?_, fun s hs => ?_⟩
  · intro v hv s
    rw [heq v hv s, shellWeight_zero]
  · intro v hv s
    exact HeckeFunctionalEquation.epsilon_eq_one_of_conductors_eq_zero
      (topologicalData v) (χ.finiteComponent v) (ψf v) (μ v) (hc v hv) (hn v hv) s
  · obtain ⟨hsum, hconv⟩ := hσ s hs
    have hj := summable_nonzero_of_eq_off_finset S
      (fun v => fourierShellWeight χ ψf μ v s) (fun v => shellWeight χ⁻¹ v s)
      (summable_nonzero_shellWeight χ⁻¹ s hsum hconv)
      (fun v => (hasSum_fourierShellWeight χ ψf μ v s (hconv v)).summable.norm)
      (fun v hv => heq v hv s)
    refine ⟨DivisorEulerProduct.summable_norm_coefficient S _ hj, ?_⟩
    convert DivisorEulerProduct.hasProd_tsum S (fun v => fourierShellWeight χ ψf μ v s)
      (fun v hv => by rw [heq v hv s, shellWeight_zero]) hj using 1
    funext v
    exact (hasSum_fourierShellWeight χ ψf μ v s (hconv v)).tsum_eq.symm

/-- The actual Fourier divisor sum is the finite epsilon product times the
original divisor sum for the inverse Hecke character. No coefficient is divided out. -/
theorem exists_fourierShellWeight_factorization
    (Sψ : Finset (FinitePlace K))
    (hψ : ∀ v ∉ Sψ, (topologicalData v).additiveConductor (ψf v) = 0) :
    ∃ (σ : ℝ) (S : Finset (FinitePlace K)), ∀ s : ℂ, σ < s.re →
      Summable (fun d : FinitePlace K →₀ ℤ =>
        ‖DivisorEulerProduct.coefficient S (fun v => fourierShellWeight χ ψf μ v s) d‖) ∧
      Summable (fun d : FinitePlace K →₀ ℤ =>
        ‖DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ⁻¹ v s) d‖) ∧
      (∑' d : FinitePlace K →₀ ℤ,
        DivisorEulerProduct.coefficient S (fun v => fourierShellWeight χ ψf μ v s) d) =
        (∏ v ∈ S, HeckeFunctionalEquation.finiteEpsilon χ ψf μ v (1 - s)) *
          ∑' d : FinitePlace K →₀ ℤ,
            DivisorEulerProduct.coefficient ∅ (fun v => shellWeight χ⁻¹ v s) d := by
  classical
  obtain ⟨σf, S, _, hε, hf⟩ := exists_hasProd_fourierShellWeight χ ψf μ Sψ hψ
  obtain ⟨σd, hd⟩ := exists_hasProd_shellWeight χ⁻¹
  refine ⟨max σf σd, S, fun s hs => ?_⟩
  obtain ⟨hsf, hpf⟩ := hf s (lt_of_le_of_lt (le_max_left _ _) hs)
  obtain ⟨hsd, hpd⟩ := hd s (lt_of_le_of_lt (le_max_right _ _) hs)
  have hpε : HasProd (fun v => HeckeFunctionalEquation.finiteEpsilon χ ψf μ v (1 - s))
      (∏ v ∈ S, HeckeFunctionalEquation.finiteEpsilon χ ψf μ v (1 - s)) :=
    hasProd_prod_of_ne_finset_one (fun v hv => hε v hv (1 - s))
  exact ⟨hsf, hsd, hpf.unique (hpε.mul hpd)⟩

end Fourier

end Langlands.Global.HeckeDivisorEulerProduct
