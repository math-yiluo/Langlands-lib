import Langlands.Global.Factors.CuspidalPairEisensteinOneplace
import Langlands.Global.Factors.CuspidalPairSchemeAutomorphy
import Langlands.Global.Factors.CuspidalPairSchemeSeries
import Langlands.Global.AdelicBlockSmoothSectionGrowth
import Langlands.Global.RankinSelberg.CuspCentralBound
import Langlands.Automorphic.IrreducibleCentralCharacterProof
import Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerBasic

/-! # Power bounds for the Levi Whittaker coefficient of a cuspidal-pair section

Each block coefficient of an irreducible cuspidal realization is bounded by a fixed power of
`|det|` (`RankinSelbergGlobal.CuspCentralBound.exists_norm_evaluate_le_rpow`). For a smooth
compact-finite block section the normalized Levi slices at all points of the standard maximal
compact subgroup lie in one finite-dimensional space of such coefficients, which gives a bound
`C ∏_i |det m_i|^(β_i)` uniform in the compact variable. For a cuspidal-pair section `φ` this
bounds the Levi Whittaker coefficient `W_M(φ_s)(p k)` by
`|δ_P(m)^(1/2 + s/(r+t+2))| · C |det m_1|^(β_1) |det m_2|^(β_2)`, `m = diag(m_1, m_2)` the Levi
part of `p`. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false

universe u

open NumberField Langlands.Automorphic

namespace Langlands.Global.AdelicBlockScalarSections

open Langlands.GeneralLinear AdelicBlockParabolic AdelicBlockDeterminantCharacter
  PrimitiveAdelicHeight

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} {B : BlockShape n}
  {S : ∀ i : Fin B.length, OperatorRealization F (B.size i)}

/-- The weight `∏_i |det m_i|^(β_i)` on the adelic Levi. -/
def blockPowerWeight (β : Fin B.length → ℝ) (m : FullLevi F B) : ℝ :=
  ∏ i, absDet F (B.size i) (m i) ^ β i

theorem blockPowerWeight_nonneg (β : Fin B.length → ℝ) (m : FullLevi F B) :
    0 ≤ blockPowerWeight β m :=
  Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (absDet_pos F _ _).le _

variable [CompactSpace (AdeleQuotient F)]

variable (S) in
/-- **Power bound for the block coefficients.** If the adele quotient is compact, all block
sizes are positive and every block realization is irreducible and cuspidal, there are exponents
`β_i` such that every finite combination of block coefficients is bounded by a constant times
`∏_i |det m_i|^(β_i)`. -/
theorem exists_blockPowerWeight_bound (hpos : ∀ i, B.size i ≠ 0)
    (hS : ∀ i, (S i).IsCuspidal) (hI : ∀ i, (S i).IsIrreducible) :
    ∃ β : Fin B.length → ℝ, ∀ f ∈ coefficientValues F B S,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ m : FullLevi F B, ‖f m‖ ≤ C * blockPowerWeight β m := by
  choose χ hχ _ using fun i => (S i).existsUnique_hasCentralCharacter (hI i)
  choose β hβ using fun i =>
    RankinSelbergGlobal.CuspCentralBound.exists_norm_evaluate_le_rpow (hpos i) (S i) (hS i)
      (χ i) (hχ i)
  refine ⟨β, fun f hf => ?_⟩
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨v, rfl⟩ := hf
    choose c hc0 hc using fun i => hβ i (v i)
    refine ⟨∏ i, c i, Finset.prod_nonneg fun i _ => hc0 i, fun m => ?_⟩
    rw [blockCoefficient, Complex.norm_prod, blockPowerWeight, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => hc i (m i)
  | zero => exact ⟨0, le_rfl, fun m => by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨C, hC, hb⟩ := hf
    obtain ⟨D, hD, hd⟩ := hg
    refine ⟨C + D, add_nonneg hC hD, fun m => ?_⟩
    rw [add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hb m) (hd m))
  | smul a f _ hf =>
    obtain ⟨C, hC, hb⟩ := hf
    refine ⟨‖a‖ * C, mul_nonneg (norm_nonneg _) hC, fun m => ?_⟩
    rw [Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb m) (norm_nonneg _)

local instance sliceBoundVAGroup :
    AddCommGroup (FiniteSmoothRealizedSections F B S) := Submodule.addCommGroup _
local instance sliceBoundWAGroup :
    AddCommGroup (smoothCompactFiniteSections F B S) := Submodule.addCommGroup _

omit [CompactSpace (AdeleQuotient F)] in
/-- **Uniform slice bound.** Under a power bound for the block coefficients, the normalized
Levi slices of a smooth compact-finite block section at all points `k` of the standard maximal
compact subgroup are bounded by one constant times `∏_i |det m_i|^(β_i)`. -/
theorem exists_norm_normalizedSlice_le {β : Fin B.length → ℝ}
    (hβ : ∀ f ∈ coefficientValues F B S,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ m : FullLevi F B, ‖f m‖ ≤ C * blockPowerWeight β m)
    (f : smoothCompactFiniteSections F B S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : standardCompact F n) (m : FullLevi F B),
      ‖normalizedSlice F B f.val.val.val k m‖ ≤ C * blockPowerWeight β m := by
  obtain ⟨V, hV, hCoeff, hMem⟩ := exists_finiteDimensional_compactSlices F B S f
  let v (k : standardCompact F n) : V := ⟨normalizedSlice F B f.val.val.val k, hMem k⟩
  obtain ⟨x, e, he⟩ := EisensteinJet.exists_evaluationEquiv V.subtype
    (Submodule.injective_subtype V)
  let b (j : Fin (Module.finrank ℂ V)) : V := e.symm (Pi.single j 1)
  have hEq (k : standardCompact F n) : v k = ∑ j, e (v k) j • b j := by
    apply e.injective
    rw [map_sum]
    simp only [map_smul, b, LinearEquiv.apply_symm_apply]
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hcont (j : Fin (Module.finrank ℂ V)) : Continuous (fun k => e (v k) j) := by
    simp only [he]
    exact continuous_const.mul ((continuous_smoothBlockSection F B S f).comp
      (continuous_const.mul continuous_subtype_val))
  have : CompactSpace (standardCompact F n) :=
    isCompact_iff_compactSpace.mp (isCompact_standardCompact F n)
  have hcoeff (j : Fin (Module.finrank ℂ V)) : ∃ D : ℝ, 0 ≤ D ∧ ∀ k, ‖e (v k) j‖ ≤ D := by
    obtain ⟨D, hD⟩ := isCompact_univ.exists_bound_of_continuousOn (hcont j).continuousOn
    exact ⟨max 0 D, le_max_left _ _, fun k => (hD k (Set.mem_univ _)).trans (le_max_right _ _)⟩
  choose D hD hDk using hcoeff
  choose C hC hCm using fun j => hβ _ (hCoeff (b j).property)
  refine ⟨∑ j, D j * C j, Finset.sum_nonneg fun j _ => mul_nonneg (hD j) (hC j),
    fun k m => ?_⟩
  have h := congrArg (fun w : V => w.val m) (hEq k)
  change normalizedSlice F B f.val.val.val k m = _ at h
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h
  rw [h, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, mul_assoc]
  exact mul_le_mul (hDk j k) (hCm j m) (norm_nonneg _) (hD j)

end Langlands.Global.AdelicBlockScalarSections

namespace Langlands.Global.CuspidalPairEisenstein.OpenCellBound

open AdelicBlockScalarSections AdelicBlockParabolic AdelicBlockDeterminantCharacter
  PrimitiveAdelicHeight Oneplace RankinSelbergGlobal
open scoped CategoryTheory.MonObj

local instance sliceBoundSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (RankinSelbergGlobal.Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance sliceBoundSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (RankinSelbergGlobal.Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r t : ℕ}
  {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
  {φ : AdelicGL F (r + t + 2) → ℂ}

omit [CompactSpace (AdeleQuotient F)] in
variable (r t) in
/-- The weight `|det m_1|^(β₁) |det m_2|^(β₂)` on the adelic Levi `GL_(r+1) × GL_(t+1)`. -/
def pairWeight (β₁ β₂ : ℝ) (m : FullLevi F (blockShape r t)) : ℝ :=
  absDet F (r + 1) (leviFst m) ^ β₁ * absDet F (t + 1) (leviSnd m) ^ β₂

omit [CompactSpace (AdeleQuotient F)] in
theorem pairWeight_nonneg (β₁ β₂ : ℝ) (m : FullLevi F (blockShape r t)) :
    0 ≤ pairWeight r t β₁ β₂ m :=
  mul_nonneg (Real.rpow_nonneg (absDet_pos F _ _).le _) (Real.rpow_nonneg (absDet_pos F _ _).le _)

theorem blockRealizations_isCuspidal (T : CuspidalOperatorRealization F r)
    (T' : CuspidalOperatorRealization F t) (i : Fin (blockShape r t).length) :
    (blockRealizations T T' i).IsCuspidal := by
  have h : ∀ j : Fin 2, (blockRealizations T T' j).IsCuspidal := by
    intro j
    fin_cases j
    · exact T.cuspidal
    · exact (dualRealization T').cuspidal
  exact h i

theorem blockRealizations_isIrreducible (T : CuspidalOperatorRealization F r)
    (T' : CuspidalOperatorRealization F t) (i : Fin (blockShape r t).length) :
    (blockRealizations T T' i).IsIrreducible := by
  have h : ∀ j : Fin 2, (blockRealizations T T' j).IsIrreducible := by
    intro j
    fin_cases j
    · exact T.irreducible
    · exact (dualRealization T').irreducible
  exact h i

/-- **Slice bound for a cuspidal-pair section.** For a section `φ` with `IsSection T T' φ`
(and compact adele quotient) there are exponents `β₁`, `β₂` and a constant
`C` with `|δ_P(m)^(-1/2) φ(m k)| ≤ C |det m_1|^(β₁) |det m_2|^(β₂)` for every adelic Levi
element `m = diag(m_1, m_2)` and every `k` in the standard maximal compact subgroup. -/
theorem exists_slice_bound (hφ : IsSection T T' φ) :
    ∃ β₁ β₂ C : ℝ, 0 ≤ C ∧ ∀ (k : standardCompact F (r + t + 2))
      (m : FullLevi F (blockShape r t)),
      ‖((leviHalfCharacter F (blockShape r t) m : ℂˣ) : ℂ)⁻¹ *
          φ ((blockShape r t).leviEmbedding (Adeles F) m * k.val)‖ ≤
        C * pairWeight r t β₁ β₂ m := by
  obtain ⟨β, hβ⟩ := exists_blockPowerWeight_bound (blockRealizations T T')
    (fun i => ((blockShape r t).positive i).ne') (blockRealizations_isCuspidal T T')
    (blockRealizations_isIrreducible T T')
  obtain ⟨C, hC, hb⟩ := exists_norm_normalizedSlice_le hβ (smoothSection hφ)
  refine ⟨β (firstBlock r t), β (secondBlock r t), C, hC, fun k m => ?_⟩
  have h := hb k m
  rw [blockPowerWeight, prod_blocks] at h
  exact h

omit [CompactSpace (AdeleQuotient F)] in
theorem pairWeight_leviOf_unipotent_mul (β₁ β₂ : ℝ)
    (x : RankinSelbergGlobal.unipotentAdelic F (r + 1))
    (z : RankinSelbergGlobal.unipotentAdelic F (t + 1)) (N : FullLevi F (blockShape r t)) :
    pairWeight r t β₁ β₂ (leviOf (GeneralLinearGroupPoints.adelicEquiv F (r + 1)
        (x : RankinSelbergGlobal.Points F (r + 1)))
      (GeneralLinearGroupPoints.adelicEquiv F (t + 1)
        (z : RankinSelbergGlobal.Points F (t + 1))) * N) = pairWeight r t β₁ β₂ N := by
  have hx : absDet F (r + 1) (GeneralLinearGroupPoints.adelicEquiv F (r + 1)
      (x : RankinSelbergGlobal.Points F (r + 1))) = 1 := by
    change ((determinantNorm F (r + 1) _ : NNReal) : ℝ) = 1
    rw [determinantNorm_unipotentAdelic x, Units.val_one, NNReal.coe_one]
  have hz : absDet F (t + 1) (GeneralLinearGroupPoints.adelicEquiv F (t + 1)
      (z : RankinSelbergGlobal.Points F (t + 1))) = 1 := by
    change ((determinantNorm F (t + 1) _ : NNReal) : ℝ) = 1
    rw [determinantNorm_unipotentAdelic z, Units.val_one, NNReal.coe_one]
  have h1 : leviFst (leviOf (GeneralLinearGroupPoints.adelicEquiv F (r + 1)
        (x : RankinSelbergGlobal.Points F (r + 1)))
      (GeneralLinearGroupPoints.adelicEquiv F (t + 1)
        (z : RankinSelbergGlobal.Points F (t + 1))) * N) =
      GeneralLinearGroupPoints.adelicEquiv F (r + 1) (x : RankinSelbergGlobal.Points F (r + 1)) *
        leviFst N := rfl
  have h2 : leviSnd (leviOf (GeneralLinearGroupPoints.adelicEquiv F (r + 1)
        (x : RankinSelbergGlobal.Points F (r + 1)))
      (GeneralLinearGroupPoints.adelicEquiv F (t + 1)
        (z : RankinSelbergGlobal.Points F (t + 1))) * N) =
      GeneralLinearGroupPoints.adelicEquiv F (t + 1) (z : RankinSelbergGlobal.Points F (t + 1)) *
        leviSnd N := rfl
  rw [pairWeight, pairWeight, h1, h2, absDet_mul, absDet_mul, hx, hz, one_mul, one_mul]

omit [CompactSpace (AdeleQuotient F)] in
/-- The twisted section at a Levi translate of a compact element: `φ_s(m k)` is
`δ_P(m)^(1/2 + s/(r+t+2))` times the normalized slice of `φ` at `k`. -/
theorem twisted_levi_mul_eq (s : ℂ) (m : FullLevi F (blockShape r t))
    (k : standardCompact F (r + t + 2)) :
    twisted φ s ((blockShape r t).leviEmbedding (Adeles F) m * k.val) =
      levFactor s m * (((leviHalfCharacter F (blockShape r t) m : ℂˣ) : ℂ)⁻¹ *
        φ ((blockShape r t).leviEmbedding (Adeles F) m * k.val)) := by
  rw [twisted, heightPower_levi_mul s m k.val k.property, levFactor]
  have hne : ((leviHalfCharacter F (blockShape r t) m : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

/-- **The Levi Whittaker bound.** Let `ψ` be a standard additive character and `φ` a section
with `IsSection T T' φ`. If the normalized slices of `φ` are bounded by
`C |det m_1|^(β₁) |det m_2|^(β₂)`, then for every `p` in the parabolic and `k` in the standard
maximal compact subgroup, `|W_M(φ_s)(p k)| ≤ |δ_P(m)^(1/2 + s/(r+t+2))| · C |det m_1|^(β₁)
|det m_2|^(β₂)`, where `m` is the Levi part of `p`. -/
theorem norm_leviWhittaker_le (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (hφ : IsSection T T' φ) {β₁ β₂ C : ℝ}
    (hC : ∀ (k : standardCompact F (r + t + 2)) (m : FullLevi F (blockShape r t)),
      ‖((leviHalfCharacter F (blockShape r t) m : ℂˣ) : ℂ)⁻¹ *
          φ ((blockShape r t).leviEmbedding (Adeles F) m * k.val)‖ ≤
        C * pairWeight r t β₁ β₂ m)
    (s : ℂ) (p : Full F (blockShape r t)) (k : standardCompact F (r + t + 2)) :
    ‖leviWhittaker F r t ψ (twisted φ s) (p.val * k.val)‖ ≤
      ‖levFactor s ((blockShape r t).leviProjection (Adeles F) p)‖ *
        (C * pairWeight r t β₁ β₂ ((blockShape r t).leviProjection (Adeles F) p)) := by
  set m := (blockShape r t).leviProjection (Adeles F) p
  set u := (((blockShape r t).unipotentPart (Adeles F) p : (blockShape r t).parabolic (Adeles F)) :
    AdelicGL F (r + t + 2))
  have key : ∀ (x : unipotentAdelic F (r + 1)) (z : unipotentAdelic F (t + 1)),
      ‖twisted φ s (leviPair F r t
        (GeneralLinearGroupPoints.adelicEquiv F (r + 1) ((x : Points F (r + 1)) * (1 : Points F (r + 1))))
        (GeneralLinearGroupPoints.adelicEquiv F (t + 1)
          ((z : Points F (t + 1)) * (1 : Points F (t + 1)))) *
          (p.val * k.val))‖ ≤
        ‖levFactor s m‖ * (C * pairWeight r t β₁ β₂ m) := by
    intro x z
    rw [mul_one, mul_one, leviPair_eq_leviEmbedding]
    set Q := leviOf (GeneralLinearGroupPoints.adelicEquiv F (r + 1) (x : Points F (r + 1)))
      (GeneralLinearGroupPoints.adelicEquiv F (t + 1) (z : Points F (t + 1)))
    have e : (blockShape r t).leviEmbedding (Adeles F) Q * (p.val * k.val) =
        ((blockShape r t).leviEmbedding (Adeles F) Q * u *
          ((blockShape r t).leviEmbedding (Adeles F) Q)⁻¹) *
        ((blockShape r t).leviEmbedding (Adeles F) (Q * m) * k.val) := by
      rw [parabolic_eq_unipotent_mul_levi p, map_mul]
      group
      rfl
    rw [e, twisted_unipotent_mul hφ s _ (levi_conj_mem Q u (unipotentPart_mem p)),
      twisted_levi_mul_eq, norm_mul, levFactor_unipotent_mul]
    refine mul_le_mul_of_nonneg_left ((hC k (Q * m)).trans_eq ?_) (norm_nonneg _)
    rw [pairWeight_leviOf_unipotent_mul]
  unfold leviWhittaker
  refine Unfolding.norm_whittaker_le F ψ hψ _ 1 _ fun x => ?_
  exact Unfolding.norm_whittaker_le F ψ hψ _ 1 _ fun z => key x z

end Langlands.Global.CuspidalPairEisenstein.OpenCellBound
