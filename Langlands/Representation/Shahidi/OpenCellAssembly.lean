import Langlands.Representation.Shahidi.OpenCellSum

/-! # Assembly: the half-plane and the sum from the shell identities -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open Langlands.GeneralLinear

/-- The abscissa of the uniform half-plane. -/
def openCellAbscissa (r t : ℕ) (A B : ℝ) : ℝ :=
  2 * ((r : ℝ) + t + 1) + 2 * ((r : ℝ) + 1) * max A 0 + 2 * ((t : ℝ) + 1) * max B 0 +
    ((r : ℝ) + 1) * ((t : ℝ) + 1) + 1

theorem paramBound_le_rpow {q : ℕ} (hq : 1 ≤ q) (A : ℝ) :
    paramBound q A ≤ (q : ℝ) ^ max A 0 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  apply max_le
  · exact Real.one_le_rpow hq1 (le_max_right _ _)
  · exact Real.rpow_le_rpow_of_exponent_le hq1 (le_max_left _ _)

/-- Past the abscissa, the ratio beats the growth of the shells. -/
theorem pow_mul_summandRatio_le {q : ℕ} (hq : 2 ≤ q) (r t : ℕ) (A B : ℝ) {s : ℂ}
    (hs : openCellAbscissa r t A B < s.re) :
    (q : ℝ) ^ ((r + 1) * (t + 1)) * summandRatio q r t A B s ≤ 1 / 2 := by
  have hq0 : (0 : ℝ) < q := by
    have : (0 : ℝ) < 2 := by norm_num
    exact this.trans_le (by exact_mod_cast hq)
  have hq1 : (1 : ℝ) ≤ q := by
    have : (1 : ℝ) ≤ 2 := by norm_num
    exact this.trans (by exact_mod_cast hq)
  have h2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  set a := max A 0
  set b := max B 0
  have hMA := paramBound_le_rpow (q := q) (by omega) A
  have hMB := paramBound_le_rpow (q := q) (by omega) B
  have hMA0 : 0 ≤ paramBound q A := zero_le_one.trans (paramBound_one_le q A)
  have hMB0 : 0 ≤ paramBound q B := zero_le_one.trans (paramBound_one_le q B)
  set X : ℝ := (q : ℝ) with hX
  have hXpow : ∀ n : ℕ, X ^ n = X ^ (n : ℝ) := fun n => (Real.rpow_natCast X n).symm
  have hMpow : ∀ (M e : ℝ) (n : ℕ), 0 ≤ M → M ≤ X ^ e → M ^ n ≤ X ^ (e * n) := by
    intro M e n hM0 hMe
    rw [Real.rpow_mul hq0.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ hM0 hMe n
  have h2pow : ∀ n : ℕ, (2 : ℝ) ^ n ≤ X ^ (n : ℝ) := by
    intro n
    rw [← hXpow]
    exact pow_le_pow_left₀ (by norm_num) h2 n
  have hstep : X ^ ((r + 1) * (t + 1)) * summandRatio q r t A B s ≤
      X ^ ((((r + 1) * (t + 1) : ℕ) : ℝ)) * (X ^ (-s.re) * (X ^ (((r + t : ℕ) : ℝ)) *
        ((X ^ (((r + 1 : ℕ) : ℝ)) * X ^ (a * ((2 * (r + 1) : ℕ) : ℝ))) *
          (X ^ (((t + 1 : ℕ) : ℝ)) * X ^ (b * ((2 * (t + 1) : ℕ) : ℝ)))))) := by
    rw [summandRatio, hXpow, hXpow (r + t)]
    gcongr
    · exact h2pow _
    · exact hMpow _ _ _ hMA0 hMA
    · exact h2pow _
    · exact hMpow _ _ _ hMB0 hMB
  have hcomb : X ^ ((((r + 1) * (t + 1) : ℕ) : ℝ)) * (X ^ (-s.re) * (X ^ (((r + t : ℕ) : ℝ)) *
        ((X ^ (((r + 1 : ℕ) : ℝ)) * X ^ (a * ((2 * (r + 1) : ℕ) : ℝ))) *
          (X ^ (((t + 1 : ℕ) : ℝ)) * X ^ (b * ((2 * (t + 1) : ℕ) : ℝ)))))) =
      X ^ (openCellAbscissa r t A B - 1 - s.re) := by
    simp only [← Real.rpow_add hq0]
    congr 1
    simp only [openCellAbscissa, a, b]
    push_cast
    ring
  have hfin : X ^ (openCellAbscissa r t A B - 1 - s.re) ≤ 1 / 2 := by
    have hle : X ^ (openCellAbscissa r t A B - 1 - s.re) ≤ X ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    refine hle.trans ?_
    rw [Real.rpow_neg_one]
    rw [inv_le_comm₀ hq0 (by norm_num)]
    norm_num
    exact h2
  exact hstep.trans (hcomb.le.trans hfin)

/-- The degree-`D` part of `∏_p (1 - x_p)`: `∑_(|T| = D) ∏_(p ∈ T) (-x_p)`. -/
def shellCoefficient {ι : Type*} [Fintype ι] (x : ι → ℂ) (D : ℕ) : ℂ :=
  ∑ T ∈ Finset.powersetCard D (Finset.univ : Finset ι), ∏ p ∈ T, (-x p)

theorem hasSum_shellCoefficient {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    HasSum (shellCoefficient x) (∏ p, (1 - x p)) := by
  classical
  have hsupp : ∀ D ∉ Finset.range ((Finset.univ : Finset ι).card + 1),
      shellCoefficient x D = 0 := by
    intro D hD
    rw [Finset.mem_range, not_lt] at hD
    rw [shellCoefficient, Finset.powersetCard_eq_empty.2 (by omega), Finset.sum_empty]
  have h : HasSum (shellCoefficient x) _ := hasSum_sum_of_ne_finset_zero hsupp
  have heq : ∑ D ∈ Finset.range ((Finset.univ : Finset ι).card + 1), shellCoefficient x D =
      ∏ p, (1 - x p) := by
    rw [show (∏ p, (1 - x p)) = ∏ p, (1 + (-x p)) by simp [sub_eq_add_neg],
      Finset.prod_one_add, Finset.powerset_card_disjiUnion]
    exact (Finset.sum_disjiUnion _ _ _).symm
  rwa [heq] at h

theorem summandConstant_nonneg (q r t : ℕ) (A B : ℝ) : 0 ≤ summandConstant q r t A B := by
  have h1 := zero_le_one.trans (paramBound_one_le q A)
  have h2 := zero_le_one.trans (paramBound_one_le q B)
  unfold summandConstant
  positivity

theorem summandRatio_nonneg (q r t : ℕ) (A B : ℝ) (s : ℂ) : 0 ≤ summandRatio q r t A B s := by
  have h1 := zero_le_one.trans (paramBound_one_le q A)
  have h2 := zero_le_one.trans (paramBound_one_le q B)
  unfold summandRatio
  positivity

section Padic

universe u

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

local instance ocAssemblyTopologicalSpace : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
local instance ocAssemblyValuativeRel : ValuativeRel K.Carrier := K.canonicalTopologicalData.valuativeRel
local instance ocAssemblyIsNonarchimedeanLocalField : IsNonarchimedeanLocalField K.Carrier := K.canonicalTopologicalData.localField

variable {r t : ℕ}
  {ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _ K.canonicalTopologicalData.topology}
  {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
    (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)
  {a : Fin (r + 1) → ℂˣ} {c : Fin (t + 1) → ℂˣ} {s : ℂ}
  {f : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier → ℂ}

/-- The depth of a class of `M_((t+1)×(r+1))(K) / M_((t+1)×(r+1))(𝒪)`, read off its chosen
representative. -/
def classDepth (y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier ⧸ integralMatrices K (t + 1) (r + 1)) :
    ℕ :=
  (openCellDepth hϖ (Quotient.out y)).toNat

/-- The pair parameters `a_i c_j⁻¹ q^(-(1+s))`. -/
def pairParameter (q : ℕ) (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ)
    (x : Fin (r + 1) × Fin (t + 1)) : ℂ :=
  (a x.1 : ℂ) * ((c x.2 : ℂ))⁻¹ * (q : ℂ) ^ (-(1 + s))

variable (ψ a c s f) in
/-- The shell identity: the classes of depth `D` contribute the degree-`D` part of
`∏_(i,j) (1 - a_i c_j⁻¹ q^(-(1+s)))`. -/
def ShellIdentity : Prop :=
  ∀ D : ℕ, HasSum (fun y : {y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier ⧸
      integralMatrices K (t + 1) (r + 1) // classDepth K hϖ y = D} =>
        openCellSummand K ψ f (Quotient.out y.1))
    (shellCoefficient (pairParameter K.canonicalTopologicalData.residueCardinality a c s) D)

/-- **Reduction to the shell identities.** -/
theorem hasSum_of_shellIdentity
    (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (hf : IsOpenCellSection K ψ hϖ a c s f) {A B : ℝ}
    (ha : ∀ i, ‖(a i : ℂ)‖ ≤ (K.canonicalTopologicalData.residueCardinality : ℝ) ^ A)
    (hc : ∀ j, ‖((c j)⁻¹ : ℂ)‖ ≤ (K.canonicalTopologicalData.residueCardinality : ℝ) ^ B)
    (hs : openCellAbscissa r t A B < s.re) (hshell : ShellIdentity K ψ hϖ a c s f) :
    HasSum (fun y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier ⧸
        integralMatrices K (t + 1) (r + 1) => openCellSummand K ψ f (Quotient.out y))
      (∏ i, ∏ j, (1 - (a i : ℂ) * ((c j : ℂ))⁻¹ *
        (K.canonicalTopologicalData.residueCardinality : ℂ) ^ (-(1 + s)))) := by
  set q := K.canonicalTopologicalData.residueCardinality with hqdef
  have hq2 : 2 ≤ q := K.canonicalTopologicalData.residueCardinality_gt_one
  set C := summandConstant q r t A B
  set ρ := summandRatio q r t A B s
  have hC := summandConstant_nonneg q r t A B
  have hρ := summandRatio_nonneg q r t A B s
  have hratio := pow_mul_summandRatio_le hq2 r t A B hs
  -- the shells
  have hshellS : ∀ D, ({y | classDepth K hϖ y = D} :
      Set (Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier ⧸ integralMatrices K (t + 1) (r + 1))).Finite ∧
      ({y | classDepth K hϖ y = D} :
        Set (Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier ⧸
          integralMatrices K (t + 1) (r + 1))).ncard ≤ q ^ ((t + 1) * (r + 1) * D) := by
    intro D
    apply finite_and_ncard_le K hϖ (t + 1) (r + 1)
    intro y hy i j
    have hD : openCellDepth hϖ (Quotient.out y) = (D : ℤ) := by
      rw [← hy, classDepth, Int.toNat_of_nonneg (openCellDepth_nonneg hϖ _)]
    have h := uniformizer_pow_depth_mul_mem hϖ (Quotient.out y) i j
    rwa [hD] at h
  have hsum : Summable fun y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier ⧸
      integralMatrices K (t + 1) (r + 1) => openCellSummand K ψ f (Quotient.out y) := by
    apply summable_of_depth_bound _ (classDepth K hϖ) hC hρ (fun D => (hshellS D).1)
      (fun D => (hshellS D).2)
    · intro y
      exact norm_openCellSummand_le K hϖ hψ hf ha hc (Quotient.out y)
    · have hg : Summable fun D : ℕ => C * ((q : ℝ) ^ ((t + 1) * (r + 1)) * ρ) ^ D := by
        apply Summable.mul_left
        apply summable_geometric_of_lt_one (by positivity)
        rw [mul_comm (t + 1)]
        linarith
      convert hg using 2 with D
      push_cast
      rw [mul_pow, ← pow_mul]
      ring
  have hprod : (∏ i, ∏ j, (1 - (a i : ℂ) * ((c j : ℂ))⁻¹ * (q : ℂ) ^ (-(1 + s)))) =
      ∏ x : Fin (r + 1) × Fin (t + 1), (1 - pairParameter q a c s x) := by
    rw [← Finset.univ_product_univ, Finset.prod_product]
    rfl
  rw [hprod]
  exact hasSum_of_depth_fibers _ (classDepth K hϖ) (hasSum_shellCoefficient _) hshell hsum

end Padic

section Statement

universe u

/-- The shell identities for all ranks, all `p`-adic fields, all unitary additive characters of
conductor `𝒪`, all uniformizers, all parameters `a`, `c`, `s` and every section with the target
transformation law (`IsOpenCellSection`). -/
def OpenCellShellIdentityStatement : Prop :=
  ∀ (r t : ℕ) (p : ℕ) [Fact p.Prime] (K : PadicField.{u} p)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _
      K.canonicalTopologicalData.topology),
    K.canonicalTopologicalData.additiveConductor ψ = 0 →
  ∀ (ϖ : K.Carrierˣ) (hϖ : Iwasawa.IsUniformizingElement
      (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)
    (a : Fin (r + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ) (s : ℂ)
    (f : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier → ℂ),
    IsOpenCellSection K ψ hϖ a c s f → ShellIdentity K ψ hϖ a c s f

/-- The target statement follows from the shell identities. -/
theorem unramifiedOpenCellSum_of_shellIdentity (h : OpenCellShellIdentityStatement.{u}) :
    UnramifiedOpenCellSumStatement.{u} := by
  intro r t A B
  refine ⟨openCellAbscissa r t A B, ?_⟩
  intro p _ K ψ hψ ϖ hϖ a c ha hc s hs f hf
  exact hasSum_of_shellIdentity K hϖ hψ hf ha hc hs (h r t p K ψ hψ ϖ hϖ a c s f hf)

end Statement

end Langlands.Shahidi.OpenCell
