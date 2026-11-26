import Langlands.Global.RankinSelberg.ComplexLastRowFiber
import Langlands.Global.RankinSelberg.ComplexRowFourierPoint
import Langlands.Global.RankinSelberg.ComplexUnequalOrdinaryFamily
import Langlands.Global.RankinSelberg.ComplexWhittakerTranslatedMellin
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerRegularity
import Langlands.Global.RankinSelberg.StandardCompactPadding
import Langlands.Representation.GodementJacquet.ComplexJacquetDeterminantWeight
import Langlands.Global.RankinSelberg.ComplexRankZeroHaar
import Langlands.Representation.Whittaker.UpperUnipotentCharacterFactorization
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.RingTheory.Complex
import Langlands.Global.RankinSelberg.ArchimedeanQuotientMeasures

/-! # Descent of ordinary unequal-rank vanishing along the smaller rank -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal Matrix.Norms.Operator FourierTransform

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexUnequalOrdinaryDescent

open Langlands.GeneralLinear ArchimedeanLocal
open Langlands.Archimedean (unitaryCompact)
open Langlands.LocalFactor.Archimedean
open ComplexUnequalFamily (HasLeftCharacter)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ComplexLocalIwasawa (alpha kpart npart npart_mul_logTorus_mul_kpart alpha_iwasawa)
open ComplexLocalWhittakerGauge (logTorus logTorus_val)
open RealConvergenceAnalysis (rootPos rootPos_nonneg)
open ComplexLastRowFiber (pad₁ pad₁_cc pad₁_cl pad₁_lc pad₁_ll pad₁_mem colUnip
  blockMatrix blockJoin_val blockMatrix_mul_pad pad₁_mul_blockMatrix)

attribute [local instance] archimedeanComplexGLMeasurable archimedeanComplexGLBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel archimedeanComplexQMeasurable
  archimedeanComplexQBorel

local notation:max "GL" n:max => Langlands.GeneralLinear n ℂ
local notation "ρ" => ArchimedeanLocal.translateFunction

section Padding

/-- Padding sends upper unipotent matrices to upper unipotent matrices. -/
theorem padGL_mem_upperUnipotent {m n : ℕ} (h : m ≤ n)
    (u : Langlands.GeneralLinear.upperUnipotent m ℂ) :
    padGL h u.val ∈ Langlands.GeneralLinear.upperUnipotent n ℂ := by
  constructor
  · intro i j hij
    change j < i at hij
    rw [UnequalAnalytic.padGL_apply]
    split
    · exact UpperUnipotent.entry_eq_zero u hij
    · exact Matrix.one_apply_ne hij.ne'
  · intro i
    rw [UnequalAnalytic.padGL_apply]
    split
    · exact UpperUnipotent.entry_diag u _
    · exact Matrix.one_apply_eq i

/-- Padding preserves the standard generic character. -/
theorem complexWhittakerCharacter_padGL (a : ℂˣ) {m n : ℕ} (h : m + 1 ≤ n + 1)
    (g : GL (m + 1)) :
    complexWhittakerCharacter a (padGL h g) = complexWhittakerCharacter a g := by
  apply congrArg (fun z : ℂ => (complexScaledCharacter a).complex z)
  have hmn : m ≤ n := Nat.le_of_succ_le_succ h
  let e := Fin.castLEEmb hmn
  calc
    _ = ∑ i ∈ Finset.univ.map e, (padGL h g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        i.castSucc i.succ := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have ht : ¬ i.val < m := by
        intro ht
        exact hi (Finset.mem_map.mpr ⟨⟨i.val, ht⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      rw [UnequalAnalytic.padGL_apply, dite_eq_right (fun h' => ht (Nat.lt_of_succ_lt_succ h'.2))]
      exact Matrix.one_apply_ne (ne_of_lt i.castSucc_lt_succ)
    _ = _ := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro i _
      rw [UnequalAnalytic.padGL_apply]
      have hi : (e i).castSucc.val < m + 1 ∧ (e i).succ.val < m + 1 :=
        ⟨Nat.lt_succ_of_lt i.isLt, Nat.succ_lt_succ i.isLt⟩
      rw [dite_eq_left hi]
      rfl

theorem complexWhittakerCharacter_one (a : ℂˣ) (n : ℕ) :
    complexWhittakerCharacter a (1 : GL (n + 1)) = 1 := by
  unfold complexWhittakerCharacter
  have h : ∀ i : Fin n, ((1 : GL (n + 1)) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      i.castSucc i.succ = 0 := fun i => Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := i)).ne
  simp only [h, Finset.sum_const_zero]
  exact AddChar.map_zero_eq_one _

end Padding

section Good

/-- A function on `GL_(n+1)(ℂ)` with the left Whittaker law for `ψ_a`, continuous, and with
uniform simple-root bounds on every compact family of right translates. -/
structure IsGood {n : ℕ} (a : ℂˣ) (W : (GL (n + 1)) → ℂ) : Prop where
  left : HasLeftCharacter a W
  continuous : Continuous W
  bound : ∀ S : Set (GL (n + 1)), IsCompact S →
    HasUniformSimpleRootBound S (fun γ g => W (g * γ))

theorem uniformSimpleRootBound_of_subset {n : ℕ} {P P' : Type*} {S : Set P} {S' : Set P'}
    {W : P → (GL (n + 1)) → ℂ} {W' : P' → (GL (n + 1)) → ℂ}
    (hW : HasUniformSimpleRootBound S W) (h : ∀ q' ∈ S', ∃ q ∈ S, W' q' = W q) :
    HasUniformSimpleRootBound S' W' := by
  obtain ⟨N, hN⟩ := hW
  refine ⟨N, fun J => ?_⟩
  obtain ⟨C, hC, hb⟩ := hN J
  refine ⟨C, hC, fun q' hq' g => ?_⟩
  obtain ⟨q, hq, he⟩ := h q' hq'
  rw [he]
  exact hb q hq g

theorem IsGood.translate {n : ℕ} {a : ℂˣ} {W : (GL (n + 1)) → ℂ} (hW : IsGood a W)
    (γ : GL (n + 1)) : IsGood a (ρ γ W) where
  left u g := by
    change W (u.val * g * γ) = _ * W (g * γ)
    rw [mul_assoc, hW.left]
  continuous := hW.continuous.comp (continuous_id.mul continuous_const)
  bound S hS := by
    refine uniformSimpleRootBound_of_subset
      (hW.bound ((fun x => x * γ) '' S) (hS.image (continuous_id.mul continuous_const))) ?_
    intro q hq
    refine ⟨q * γ, ⟨q, hq, rfl⟩, ?_⟩
    funext g
    change W (g * q * γ) = W (g * (q * γ))
    rw [mul_assoc]

theorem isGood_of_mem_model {r : ℕ} {ds : List ComplexCharacterData} {a : ℂˣ}
    {W : (GL (r + 1)) → ℂ} (hW : W ∈ complexWhittakerModel r ds a) : IsGood a W where
  left u g := complexWhittakerModel_left_equivariant hW u.val u.2 g
  continuous := (contMDiff_of_mem_complexWhittakerModel hW).continuous
  bound S hS :=
    ComplexWhittakerTranslatedMellin.compact_rightTranslate_uniformSimpleRootBound ⟨W, hW⟩ S hS

/-- Restriction to `GL_(k+1)` along `h ↦ diag(h, 1)`. -/
def restrict {k : ℕ} (V : (GL (k + 1 + 1)) → ℂ) (h : GL (k + 1)) : ℂ := V (pad₁ k h)

private theorem logTorus_snoc {k : ℕ} (y : Fin (k + 1) → ℝ) :
    pad₁ k (logTorus y) = logTorus (Fin.snoc (α := fun _ => ℝ) y 0) := by
  apply Units.ext
  ext i j
  rw [logTorus_val]
  refine Fin.lastCases ?_ (fun i₀ => ?_) i <;> refine Fin.lastCases ?_ (fun j₀ => ?_) j
  · rw [pad₁_ll]
    simp
  · rw [pad₁_lc, Matrix.diagonal_apply_ne _ (Fin.castSucc_lt_last j₀).ne']
  · rw [pad₁_cl, Matrix.diagonal_apply_ne _ (Fin.castSucc_lt_last i₀).ne]
  · rw [pad₁_cc, logTorus_val]
    by_cases hij : i₀ = j₀
    · subst hij
      simp
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _
        (fun h => hij (Fin.castSucc_injective _ h))]

theorem alpha_pad₁ {k : ℕ} (h : GL (k + 1)) :
    alpha (pad₁ k h) = Fin.snoc (α := fun _ => ℝ) (alpha h) 0 := by
  have hdecomp := npart_mul_logTorus_mul_kpart h
  let u : Langlands.GeneralLinear.upperUnipotent (k + 1 + 1) ℂ := ⟨pad₁ k (npart h).val, pad₁_mem (npart h)⟩
  let K : unitaryCompact ℂ (k + 1 + 1) :=
    ⟨pad₁ k (kpart h).val, unitary_padGL _ _ (kpart h).2⟩
  have : pad₁ k h = (u : GL (k + 1 + 1)) * logTorus (Fin.snoc (α := fun _ => ℝ) (alpha h) 0) *
      (K : GL (k + 1 + 1)) := by
    rw [← logTorus_snoc]
    conv_lhs => rw [← hdecomp]
    simp only [map_mul]
    rfl
  rw [this, alpha_iwasawa]

private theorem sum_abs_snoc {k : ℕ} (y : Fin (k + 1) → ℝ) :
    ∑ i, |Fin.snoc (α := fun _ => ℝ) y 0 i| = ∑ i, |y i| := by
  rw [Fin.sum_univ_castSucc]
  simp

private theorem rootPos_snoc {k : ℕ} (y : Fin (k + 1) → ℝ) :
    rootPos y ≤ rootPos (Fin.snoc (α := fun _ => ℝ) y 0) := by
  unfold rootPos
  rw [Fin.sum_univ_castSucc]
  have h : ∀ i : Fin k, max (Fin.snoc (α := fun _ => ℝ) y 0 i.castSucc.castSucc -
      Fin.snoc (α := fun _ => ℝ) y 0 i.castSucc.succ) 0 = max (y i.castSucc - y i.succ) 0 := by
    intro i
    rw [show i.castSucc.succ = i.succ.castSucc from rfl, Fin.snoc_castSucc, Fin.snoc_castSucc]
  simp_rw [h]
  exact le_add_of_nonneg_right (le_max_right _ _)

theorem uniformSimpleRootBound_restrict {k : ℕ} {P : Type*} {S : Set P}
    {V : P → (GL (k + 1 + 1)) → ℂ} (hV : HasUniformSimpleRootBound S V) :
    HasUniformSimpleRootBound S (fun p h => V p (pad₁ k h)) := by
  obtain ⟨N, hN⟩ := hV
  refine ⟨N, fun J => ?_⟩
  obtain ⟨C, hC, hb⟩ := hN J
  refine ⟨C, hC, fun p hp g => (hb p hp (pad₁ k g)).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC)⟩
  rw [alpha_pad₁, sum_abs_snoc]
  have := rootPos_snoc (alpha g)
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  nlinarith

theorem IsGood.restrict {k : ℕ} {b : ℂˣ} {V : (GL (k + 1 + 1)) → ℂ} (hV : IsGood b V) :
    IsGood b (restrict V) where
  left u g := by
    change V (pad₁ k (u.val * g)) = _ * V (pad₁ k g)
    rw [map_mul, hV.left ⟨pad₁ k u.val, pad₁_mem u⟩]
    congr 1
    exact complexWhittakerCharacter_padGL b _ u.val
  continuous := hV.continuous.comp (UnequalAnalytic.continuous_padGL _)
  bound S hS := by
    refine uniformSimpleRootBound_of_subset (uniformSimpleRootBound_restrict
      (hV.bound (pad₁ k '' S) (hS.image (UnequalAnalytic.continuous_padGL _)))) ?_
    intro γ hγ
    refine ⟨pad₁ k γ, ⟨γ, hγ, rfl⟩, ?_⟩
    funext g
    change V (pad₁ k (g * γ)) = V (pad₁ k g * pad₁ k γ)
    rw [map_mul]

end Good

section Phase

variable {r k : ℕ} (hk : k + 1 < r)

/-- The upper unipotent element of `GL_(r+1)` whose entries in rows `0, …, k + 1` of the
zero-based column `k + 2` are `x`. With one-based indices, `x` fills the column immediately to
the right of the leading `(k + 2) × (k + 2)` block. -/
def phase (x : Fin (k + 1 + 1) → ℂ) : GL (r + 1) :=
  padGL (show k + 1 + 1 + 1 ≤ r + 1 by omega) (colUnip (k := k + 1) x).val

theorem phase_mem (x : Fin (k + 1 + 1) → ℂ) :
    phase hk x ∈ Langlands.GeneralLinear.upperUnipotent (r + 1) ℂ :=
  padGL_mem_upperUnipotent _ (colUnip (k := k + 1) x)

theorem character_phase (a : ℂˣ) (x : Fin (k + 1 + 1) → ℂ) :
    complexWhittakerCharacter a (phase hk x) = (complexScaledCharacter a).complex (x (Fin.last (k + 1))) := by
  rw [phase, complexWhittakerCharacter_padGL, ComplexJacquet.complexWhittakerCharacter_blockJoin]
  rw [show ((1 : Langlands.GeneralLinear.upperUnipotent (k + 1 + 1) ℂ) : GL (k + 1 + 1)) = 1 from rfl,
    complexWhittakerCharacter_one, one_mul]

private theorem pad₁_mul_colUnip (g : GL (k + 1 + 1)) (x : Fin (k + 1 + 1) → ℂ) :
    pad₁ (k + 1) g * (colUnip (k := k + 1) x).val =
      (colUnip (k := k + 1) (g.val.mulVec x)).val * pad₁ (k + 1) g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, blockJoin_val, blockJoin_val, pad₁_mul_blockMatrix,
    blockMatrix_mul_pad]
  simp

theorem pad_mul_phase (g : GL (k + 1 + 1)) (x : Fin (k + 1 + 1) → ℂ) :
    padGL (Nat.succ_le_succ hk.le) g * phase hk x =
      phase hk (g.val.mulVec x) * padGL (Nat.succ_le_succ hk.le) g := by
  have hpad : padGL (Nat.succ_le_succ hk.le) g =
      padGL (show k + 1 + 1 + 1 ≤ r + 1 by omega) (pad₁ (k + 1) g) :=
    (UnequalAnalytic.padGL_padGL _ _ g).symm
  rw [hpad, phase, phase, ← map_mul, ← map_mul, pad₁_mul_colUnip]

theorem integrand_phase {a : ℂˣ} {W : (GL (r + 1)) → ℂ} (hW : HasLeftCharacter a W)
    (V : (GL (k + 1 + 1)) → ℂ) (γ : GL (r + 1)) (x : Fin (k + 1 + 1) → ℂ) (s : ℂ)
    (q : Langlands.RankinSelberg.LeftUnipotentQuotient (k + 1) ℂ) :
    complexUnequalIntegrand hk (ρ (phase hk x * γ) W) V s q =
      (complexScaledCharacter a).complex (∑ j, ComplexLastRowFiber.lastRow k q.out j * x j) *
        complexUnequalIntegrand hk (ρ γ W) V s q := by
  simp only [complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand,
    ArchimedeanLocal.translateFunction]
  rw [← mul_assoc, pad_mul_phase, mul_assoc (phase hk _),
    hW ⟨phase hk _, phase_mem hk _⟩ (padGL (Nat.succ_le_succ hk.le) q.out * γ), character_phase]
  simp only [Matrix.mulVec, dotProduct, ComplexLastRowFiber.lastRow]
  ring

theorem constant_rootBound {n : ℕ} {b : ℂˣ} {W : (GL (n + 1)) → ℂ} (hW : IsGood b W) :
    HasUniformSimpleRootBound (univ : Set ℂ) (fun _ => W) :=
  uniformSimpleRootBound_of_subset (hW.bound {1} isCompact_singleton)
    (fun _ _ => ⟨1, rfl, by funext g; simp⟩)

/-- For a fixed right translate, all column modulations are holomorphic on one right
half-plane, where the unmodulated kernel is integrable. -/
theorem phase_holomorphy (D : ComplexQuotientMeasureData (k + 1)) {a : ℂˣ}
    {W : (GL (r + 1)) → ℂ} {V : (GL (k + 1 + 1)) → ℂ} (hW : IsGood a W) (hV : IsGood (-a) V)
    (γ : GL (r + 1)) :
    ∃ σ : ℝ, (∀ s : ℂ, σ < s.re → Integrable (complexUnequalIntegrand hk (ρ γ W) V s) D.measure) ∧
      ∀ x : Fin (k + 1 + 1) → ℂ,
        DifferentiableOn ℂ (complexUnequalIntegral hk D (ρ (phase hk x * γ) W) V) {s | σ < s.re} := by
  have hWγ := hW.translate γ
  obtain ⟨σ, hdom⟩ := ComplexUnequalFamily.ordinary_halfPlaneDomination hk D (univ : Set ℂ)
    (fun _ => ρ γ W) (fun _ => V) id (fun _ => hWγ.left) (fun _ => hV.left)
    (constant_rootBound hWγ) (constant_rootBound hV)
  have hcont (W' : (GL (r + 1)) → ℂ) (hW' : IsGood a W') (s : ℂ) :
      Continuous (complexUnequalIntegrand hk W' V s) :=
    ComplexUnequalFamily.continuous_ordinaryKernel hk hW'.left hV.left hW'.continuous
      hV.continuous s
  refine ⟨σ, fun s hs => ?_, fun x => ?_⟩
  · obtain ⟨M, hM, hbound⟩ := hdom s.re
    exact hM.mono' (hcont _ hWγ s).aestronglyMeasurable
      (ae_of_all _ (hbound s (mem_univ s) hs le_rfl))
  · let K := fun s => complexUnequalIntegrand hk (ρ (phase hk x * γ) W) V s
    have hK : ∀ s q, K s q = (complexScaledCharacter a).complex
        (∑ j, ComplexLastRowFiber.lastRow k q.out j * x j) * complexUnequalIntegrand hk (ρ γ W) V s q :=
      integrand_phase hk hW.left V γ x
    have hdomK : ComplexUnequalFamily.HalfPlaneDomination D.measure univ id K σ := by
      intro τ
      obtain ⟨M, hM, hbound⟩ := hdom τ
      refine ⟨M, hM, fun s hs hσ hτ q => ?_⟩
      simpa only [hK, id_eq, norm_mul, HarmonicAnalysis.UnitaryAdditiveCharacter.norm_complex,
        one_mul] using hbound s hs hσ hτ q
    have hKd (q : Langlands.RankinSelberg.LeftUnipotentQuotient (k + 1) ℂ) :
        Differentiable ℂ (fun s => K s q) :=
      (ComplexUnequalFamily.differentiable_detPower_parameter q.out differentiable_id _).const_mul _
    have hd := (ComplexUnequalFamily.differentiableOn_integral_of_halfPlaneDomination isOpen_univ
      differentiable_id (fun s => (hcont _ (hW.translate _) s).aestronglyMeasurable)
      (fun q => (hKd q).differentiableOn) hdomK).2
    change DifferentiableOn ℂ (fun s => ∫ q, K s q ∂D.measure) _
    simpa only [univ_inter, id_eq] using hd

end Phase

local instance complexGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear n ℂ) := by
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  exact inferInstance

section Lower

variable {r k : ℕ} (hk : k + 1 < r)

/-- The smaller-rank integral of the pair translated by a padded element and restricted. -/
def lowerIntegral (D' : ComplexQuotientMeasureData k) (W : (GL (r + 1)) → ℂ)
    (V : (GL (k + 1 + 1)) → ℂ) (γ : GL (r + 1)) (s : ℂ) (p : GL (k + 1 + 1)) : ℂ :=
  complexUnequalIntegral (Nat.lt_of_succ_lt hk) D'
    (ρ (padGL (Nat.succ_le_succ hk.le) p * γ) W) (restrict (ρ p V)) s

/-- On one right half-plane the smaller-rank integrals of the translated restrictions are
absolutely convergent near the identity and continuous at the identity. -/
theorem lower_continuity (D' : ComplexQuotientMeasureData k) {a : ℂˣ}
    {W : (GL (r + 1)) → ℂ} {V : (GL (k + 1 + 1)) → ℂ} (hW : IsGood a W) (hV : IsGood (-a) V)
    (γ : GL (r + 1)) :
    ∃ (σ : ℝ) (K : Set (GL (k + 1 + 1))), K ∈ 𝓝 1 ∧ ∀ s : ℂ, σ < s.re →
      (∀ p ∈ K, Integrable (complexUnequalIntegrand (Nat.lt_of_succ_lt hk)
        (ρ (padGL (Nat.succ_le_succ hk.le) p * γ) W) (restrict (ρ p V)) s) D'.measure) ∧
      ContinuousAt (lowerIntegral hk D' W V γ s) 1 := by
  obtain ⟨K, hKc, hK⟩ := exists_compact_mem_nhds (1 : GL (k + 1 + 1))
  let hk' := Nat.lt_of_succ_lt hk
  let S : Set (GL (k + 1 + 1) × ℂ) := K ×ˢ univ
  let Wf : GL (k + 1 + 1) × ℂ → (GL (r + 1)) → ℂ :=
    fun p => ρ (padGL (Nat.succ_le_succ hk.le) p.1 * γ) W
  let Vf : GL (k + 1 + 1) × ℂ → (GL (k + 1)) → ℂ := fun p => restrict (ρ p.1 V)
  have hpadc : Continuous (padGL (Nat.succ_le_succ hk.le) : GL (k + 1 + 1) → GL (r + 1)) :=
    UnequalAnalytic.continuous_padGL _
  have hWb : HasUniformSimpleRootBound S Wf := by
    refine uniformSimpleRootBound_of_subset (hW.bound
      ((fun p => padGL (Nat.succ_le_succ hk.le) p * γ) '' K)
      (hKc.image (hpadc.mul continuous_const))) ?_
    rintro ⟨p, z⟩ ⟨hp, -⟩
    exact ⟨_, ⟨p, hp, rfl⟩, rfl⟩
  have hVb : HasUniformSimpleRootBound S Vf := by
    refine uniformSimpleRootBound_of_subset (uniformSimpleRootBound_restrict (hV.bound K hKc)) ?_
    rintro ⟨p, z⟩ ⟨hp, -⟩
    exact ⟨p, hp, rfl⟩
  have hWl : ∀ p, HasLeftCharacter a (Wf p) := fun p => (hW.translate _).left
  have hVl : ∀ p, HasLeftCharacter (-a) (Vf p) := fun p => ((hV.translate p.1).restrict).left
  obtain ⟨σ, hdom⟩ := ComplexUnequalFamily.ordinary_halfPlaneDomination hk' D' S Wf Vf
    Prod.snd hWl hVl hWb hVb
  have hcont (p : GL (k + 1 + 1) × ℂ) (s : ℂ) :
      Continuous (complexUnequalIntegrand hk' (Wf p) (Vf p) s) :=
    ComplexUnequalFamily.continuous_ordinaryKernel hk' (hWl p) (hVl p)
      (hW.translate _).continuous ((hV.translate p.1).restrict).continuous s
  refine ⟨σ, K, hK, fun s hs => ⟨fun p hp => ?_, ?_⟩⟩
  · obtain ⟨M, hM, hbound⟩ := hdom s.re
    exact hM.mono' (hcont (p, s) s).aestronglyMeasurable
      (ae_of_all _ (hbound (p, s) ⟨hp, mem_univ s⟩ hs le_rfl))
  · obtain ⟨M, hM, hbound⟩ := hdom s.re
    refine continuousAt_of_dominated (F := fun p q =>
      complexUnequalIntegrand hk' (Wf (p, s)) (Vf (p, s)) s q) (bound := M)
      (Eventually.of_forall fun p => (hcont (p, s) s).aestronglyMeasurable)
      (Filter.mem_of_superset hK fun p hp => ae_of_all _ (hbound (p, s) ⟨hp, mem_univ s⟩ hs le_rfl))
      hM (ae_of_all _ fun q => ?_)
    change ContinuousAt (fun p : GL (k + 1 + 1) =>
      W (padGL (Nat.succ_le_succ hk'.le) q.out * (padGL (Nat.succ_le_succ hk.le) p * γ)) *
        V (pad₁ k q.out * p) *
        ArchimedeanLocal.detPower complexNormalizedAbs q.out (s - ((r - k : ℕ) : ℂ) / 2)) 1
    exact (((hW.continuous.comp (continuous_const.mul (hpadc.mul continuous_const))).mul
      (hV.continuous.comp (continuous_const.mul continuous_id))).mul continuous_const).continuousAt

end Lower

theorem eq_zero_on_right_of_differentiableOn {f : ℂ → ℂ} {σ τ : ℝ}
    (hf : DifferentiableOn ℂ f {s | σ < s.re}) (hzero : ∀ s : ℂ, τ < s.re → f s = 0) :
    ∀ s : ℂ, σ < s.re → f s = 0 := by
  let z₀ : ℂ := ((max σ τ + 1 : ℝ) : ℂ)
  have hz₀ : max σ τ < z₀.re := by simp [z₀]
  have hU : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  exact (hf.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_re_gt σ).isPreconnected ((le_max_left _ _).trans_lt hz₀)
    ((isOpen_lt continuous_const Complex.continuous_re).eventually_mem
      ((le_max_right _ _).trans_lt hz₀) |>.mono fun s hs => hzero s hs)

section Section

variable {k : ℕ}

/-- The identity matrix with its last row replaced by `η`. -/
def rowSection (η : Fin (k + 1 + 1) → ℂ) : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) ℂ :=
  Matrix.updateRow 1 (Fin.last (k + 1)) η

theorem continuous_rowSection : Continuous (rowSection (k := k)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [rowSection, Matrix.updateRow_apply]
  split_ifs
  · exact continuous_apply j
  · exact continuous_const

theorem rowSection_lastBasis : rowSection (ComplexLastRowFiber.lastBasis k) = 1 := by
  ext i j
  simp only [rowSection, Matrix.updateRow_apply, ComplexLastRowFiber.lastBasis, Matrix.one_apply,
    Pi.single_apply]
  split_ifs <;> simp_all [eq_comm]

/-- An invertible matrix with last row `η` whenever the determinant is nonzero. -/
def sectionGL (η : Fin (k + 1 + 1) → ℂ) : GL (k + 1 + 1) :=
  if h : (rowSection η).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero _ h else 1

theorem sectionGL_val {η : Fin (k + 1 + 1) → ℂ} (h : (rowSection η).det ≠ 0) :
    (sectionGL η).val = rowSection η := by
  rw [sectionGL, dite_eq_left h]
  rfl

theorem eventually_det_rowSection :
    ∀ᶠ η in 𝓝 (ComplexLastRowFiber.lastBasis k), (rowSection η).det ≠ 0 := by
  have hc : Continuous (fun η : Fin (k + 1 + 1) → ℂ => (rowSection η).det) :=
    continuous_id.matrix_det.comp continuous_rowSection
  refine hc.continuousAt.eventually_ne ?_
  rw [rowSection_lastBasis, Matrix.det_one]
  exact one_ne_zero

theorem sectionGL_lastBasis : sectionGL (ComplexLastRowFiber.lastBasis k) = 1 := by
  have h : (rowSection (ComplexLastRowFiber.lastBasis k)).det ≠ 0 := by
    rw [rowSection_lastBasis, Matrix.det_one]
    exact one_ne_zero
  apply Units.ext
  rw [sectionGL_val h, rowSection_lastBasis]
  rfl

theorem lastRow_sectionGL {η : Fin (k + 1 + 1) → ℂ} (h : (rowSection η).det ≠ 0) :
    ComplexLastRowFiber.lastRow k (sectionGL η) = η := by
  unfold ComplexLastRowFiber.lastRow
  rw [sectionGL_val h, rowSection, Matrix.updateRow_self]

theorem continuousAt_sectionGL :
    ContinuousAt (sectionGL (k := k)) (ComplexLastRowFiber.lastBasis k) := by
  rw [(Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ)
    (k + 1 + 1)).isInducing.continuousAt_iff]
  refine continuous_rowSection.continuousAt.congr ?_
  filter_upwards [eventually_det_rowSection] with η hη
  exact (sectionGL_val hη).symm

end Section

section Algebra

theorem detPower_neg_one {n : ℕ} (g : GL n) :
    ArchimedeanLocal.detPower complexNormalizedAbs g (-1) =
      (((‖g.val.det‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hpos : 0 < ‖g.val.det‖ ^ 2 := pow_pos (norm_pos_iff.mpr g.det_ne_zero) 2
  rw [ArchimedeanLocal.detPower, neg_one_mul, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
    Real.exp_neg, Real.exp_log (by simpa [complexNormalizedAbs] using hpos)]
  rfl

theorem detPower_pad₁ {k : ℕ} (h : GL (k + 1)) (z : ℂ) :
    ArchimedeanLocal.detPower complexNormalizedAbs (pad₁ k h) z =
      ArchimedeanLocal.detPower complexNormalizedAbs h z := by
  simp only [ArchimedeanLocal.detPower, UnequalAnalytic.det_padGL]

theorem continuous_detPower (n : ℕ) (z : ℂ) :
    Continuous (fun g : GL n => ArchimedeanLocal.detPower complexNormalizedAbs g z) := by
  have hdet : Continuous (fun g : GL n => Matrix.det g.val) :=
    continuous_id.matrix_det.comp Units.continuous_val
  have hlog := (hdet.norm.pow 2).log (fun g =>
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)))
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hlog))

theorem detPower_one (n : ℕ) (z : ℂ) :
    ArchimedeanLocal.detPower complexNormalizedAbs (1 : GL n) z = 1 := by
  simp [ArchimedeanLocal.detPower, complexNormalizedAbs]

variable {r k : ℕ} (hk : k + 1 < r)

/-- The unequal-rank integrand on the representative `x`. -/
def upperFunction (W : (GL (r + 1)) → ℂ) (V : (GL (k + 1 + 1)) → ℂ) (s : ℂ)
    (x : GL (k + 1 + 1)) : ℂ :=
  W (padGL (Nat.succ_le_succ hk.le) x) * V x *
    ArchimedeanLocal.detPower complexNormalizedAbs x (s - ((r - (k + 1) : ℕ) : ℂ) / 2)

theorem lowerFunction_upperFunction (W : (GL (r + 1)) → ℂ) (V : (GL (k + 1 + 1)) → ℂ)
    (γ : GL (r + 1)) (s : ℂ) (g : GL (k + 1 + 1)) (h : GL (k + 1)) :
    ComplexLastRowFiber.lowerFunction (fun x => upperFunction hk (ρ γ W) V s (x * g)) h =
      ArchimedeanLocal.detPower complexNormalizedAbs g (s - ((r - (k + 1) : ℕ) : ℂ) / 2) *
        ((ρ (padGL (Nat.succ_le_succ hk.le) g * γ) W)
            (padGL (Nat.succ_le_succ (Nat.lt_of_succ_lt hk).le) h) *
          restrict (ρ g V) h *
          ArchimedeanLocal.detPower complexNormalizedAbs h
            (s - 1 / 2 - ((r - k : ℕ) : ℂ) / 2)) := by
  have hpad : padGL (Nat.succ_le_succ hk.le) (pad₁ k h * g) =
      padGL (Nat.succ_le_succ (Nat.lt_of_succ_lt hk).le) h * padGL (Nat.succ_le_succ hk.le) g := by
    rw [map_mul, UnequalAnalytic.padGL_padGL]
  have hc : ((r - k : ℕ) : ℂ) = ((r - (k + 1) : ℕ) : ℂ) + 1 := by
    rw [show r - k = r - (k + 1) + 1 by omega]
    push_cast
    ring
  have hexp : s - 1 / 2 - ((r - k : ℕ) : ℂ) / 2 = (s - ((r - (k + 1) : ℕ) : ℂ) / 2) + -1 := by
    rw [hc]
    ring
  simp only [ComplexLastRowFiber.lowerFunction, upperFunction, restrict,
    ArchimedeanLocal.translateFunction]
  rw [hpad, Langlands.GodementJacquet.detPower_complex_mul, detPower_pad₁, hexp,
    Langlands.GodementJacquet.detPower_complex_add, detPower_neg_one, Complex.real_smul]
  simp only [mul_assoc]
  ring

end Algebra

section Descent

variable {r k : ℕ} (hk : k + 1 < r)

/-- **Descent.** If every right translate of `W` has ordinary integral against `V` vanishing on
a right half-plane, then the same holds for the restriction of `V` along `h ↦ diag(h, 1)`. -/
theorem descent (D : ComplexQuotientMeasureData (k + 1)) (D' : ComplexQuotientMeasureData k)
    {a : ℂˣ} {W : (GL (r + 1)) → ℂ} {V : (GL (k + 1 + 1)) → ℂ} (hW : IsGood a W)
    (hV : IsGood (-a) V)
    (hvan : ∀ γ : GL (r + 1), ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      complexUnequalIntegral hk D (ρ γ W) V s = 0) (γ : GL (r + 1)) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      complexUnequalIntegral (Nat.lt_of_succ_lt hk) D' (ρ γ W) (restrict V) s = 0 := by
  obtain ⟨c₀, c, hc₀, hc, hfib⟩ := ComplexLastRowFiber.lastRowFiber k D D'
  obtain ⟨σ₁, hint₁, hhol⟩ := phase_holomorphy hk D hW hV γ
  obtain ⟨σ₂, K, hK, hlow⟩ := lower_continuity hk D' hW hV γ
  refine ⟨max (σ₁ - 1 / 2) σ₂, fun s' hs' => ?_⟩
  set s : ℂ := s' + 1 / 2 with hs_def
  have hs₁ : σ₁ < s.re := by
    have := (le_max_left _ _).trans_lt hs'
    rw [hs_def, Complex.add_re]
    norm_num
    linarith
  have hs₂ : σ₂ < s'.re := (le_max_right _ _).trans_lt hs'
  have hs's : s - 1 / 2 = s' := by rw [hs_def]; ring
  have hvanx (x : Fin (k + 1 + 1) → ℂ) :
      complexUnequalIntegral hk D (ρ (phase hk x * γ) W) V s = 0 := by
    obtain ⟨τ, hτ⟩ := hvan (phase hk x * γ)
    exact eq_zero_on_right_of_differentiableOn (hhol x) hτ s hs₁
  -- the integrand on the group
  let F := upperFunction hk (ρ γ W) V s
  have hFmk (g : GL (k + 1 + 1)) :
      F g = complexUnequalIntegrand hk (ρ γ W) V s (Quotient.mk _ g) :=
    (ComplexUnequalFamily.ordinaryKernel_mk hk (hW.translate γ).left hV.left s g).symm
  have hFc : Continuous F := by
    rw [show F = fun g => complexUnequalIntegrand hk (ρ γ W) V s (Quotient.mk _ g) from
      funext hFmk]
    exact (ComplexUnequalFamily.continuous_ordinaryKernel hk (hW.translate γ).left hV.left
      (hW.translate γ).continuous hV.continuous s).comp continuous_quotient_mk'
  have hFinv : ∀ (u : Langlands.GeneralLinear.upperUnipotent (k + 1 + 1) ℂ) (g : GL (k + 1 + 1)),
      F (u.val * g) = F g := by
    intro u g
    rw [hFmk, hFmk]
    congr 1
    apply Quotient.sound
    exact QuotientGroup.rightRel_apply.mpr (by simp [mul_inv_rev])
  have hFi : Integrable (fun q : Langlands.RankinSelberg.LeftUnipotentQuotient (k + 1) ℂ =>
      F q.out) D.measure := hint₁ s hs₁
  obtain ⟨Ψ, hΨi, hΨΘ, hΨpt⟩ := hfib F hFc hFinv hFi
  -- all Fourier coefficients of the last-row density vanish
  have hcoef (x : Fin (k + 1 + 1) → ℂ) :
      ∫ η, (complexScaledCharacter a).complex (∑ i, η i * x i) * Ψ η = 0 := by
    have hΘm : Measurable (fun η : Fin (k + 1 + 1) → ℂ =>
        (complexScaledCharacter a).complex (∑ i, η i * x i)) :=
      ((complexScaledCharacter a).continuous_complex.comp
        (continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const)).measurable
    have h := hΨΘ _ hΘm (fun η => by
      rw [HarmonicAnalysis.UnitaryAdditiveCharacter.norm_complex])
    have hL : ∫ q, (complexScaledCharacter a).complex
        (∑ i, ComplexLastRowFiber.lastRow k q.out i * x i) * F q.out ∂D.measure = 0 := by
      rw [← hvanx x]
      refine integral_congr_ae (ae_of_all _ fun q => ?_)
      exact (integrand_phase hk hW.left V γ x s q).symm
    rw [hL] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (by exact_mod_cast hc₀.ne')
  -- the smaller-rank integrals through the point formula
  have hlowF (g : GL (k + 1 + 1)) :
      ∫ q, ComplexLastRowFiber.lowerFunction (fun x => F (x * g)) q.out ∂D'.measure =
        ArchimedeanLocal.detPower complexNormalizedAbs g (s - ((r - (k + 1) : ℕ) : ℂ) / 2) *
          lowerIntegral hk D' W V γ s' g := by
    rw [lowerIntegral, complexUnequalIntegral, ArchimedeanLocal.unequalIntegral,
      ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun q => ?_)
    dsimp only
    rw [show (fun x => F (x * g)) = fun x => upperFunction hk (ρ γ W) V s (x * g) from rfl,
      lowerFunction_upperFunction, hs's]
    rfl
  let Φ : GL (k + 1 + 1) → ℂ := fun g =>
    (((‖g.val.det‖ ^ 2)⁻¹ * c : ℝ) : ℂ) *
      (ArchimedeanLocal.detPower complexNormalizedAbs g (s - ((r - (k + 1) : ℕ) : ℂ) / 2) *
        lowerIntegral hk D' W V γ s' g)
  have hΦc : ContinuousAt Φ 1 := by
    have hdet : Continuous (fun g : GL (k + 1 + 1) => ((‖g.val.det‖ ^ 2)⁻¹ * c : ℝ)) :=
      (((continuous_id.matrix_det.comp Units.continuous_val).norm.pow 2).inv₀ fun g =>
        pow_ne_zero 2 (norm_ne_zero_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero g))).mul
          continuous_const
    exact (Complex.continuous_ofReal.comp hdet).continuousAt.mul
      ((continuous_detPower _ _).continuousAt.mul (hlow s' hs₂).2)
  have hΨeq : Ψ =ᶠ[𝓝 (ComplexLastRowFiber.lastBasis k)] fun η => Φ (sectionGL η) := by
    have hKℓ : ∀ᶠ η in 𝓝 (ComplexLastRowFiber.lastBasis k), sectionGL η ∈ K :=
      continuousAt_sectionGL.preimage_mem_nhds (by rw [sectionGL_lastBasis]; exact hK)
    filter_upwards [eventually_det_rowSection, hKℓ] with η hη hηK
    have hint : Integrable (fun q : Langlands.RankinSelberg.LeftUnipotentQuotient k ℂ =>
        ComplexLastRowFiber.lowerFunction (fun x => F (x * sectionGL η)) q.out) D'.measure := by
      refine (((hlow s' hs₂).1 _ hηK).const_mul (ArchimedeanLocal.detPower complexNormalizedAbs
        (sectionGL η) (s - ((r - (k + 1) : ℕ) : ℂ) / 2))).congr (ae_of_all _ fun q => ?_)
      dsimp only
      rw [show (fun x => F (x * sectionGL η)) = fun x => upperFunction hk (ρ γ W) V s
        (x * sectionGL η) from rfl, lowerFunction_upperFunction, hs's]
      rfl
    have h := hΨpt (sectionGL η) hint
    rw [lastRow_sectionGL hη, hlowF, Complex.real_smul] at h
    exact h
  have hΨc : ContinuousAt Ψ (ComplexLastRowFiber.lastBasis k) := by
    have hΦc' : ContinuousAt Φ (sectionGL (ComplexLastRowFiber.lastBasis k)) := by
      rw [sectionGL_lastBasis]
      exact hΦc
    exact (hΦc'.comp continuousAt_sectionGL).congr hΨeq.symm
  have hΨ0 := ComplexRowFourier.eq_zero_of_character_integrals a hΨi hΨc hcoef
  rw [hΨeq.self_of_nhds] at hΨ0
  dsimp only at hΨ0
  rw [sectionGL_lastBasis] at hΨ0
  simp only [Φ, Units.val_one, Matrix.det_one, norm_one, one_pow, inv_one, one_mul, detPower_one,
    mul_eq_zero, Complex.ofReal_eq_zero, hc.ne', false_or] at hΨ0
  have h1 : lowerIntegral hk D' W V γ s' 1 =
      complexUnequalIntegral (Nat.lt_of_succ_lt hk) D' (ρ γ W) (restrict V) s' := by
    rw [lowerIntegral, map_one, one_mul]
    congr 2
    funext g
    simp [ArchimedeanLocal.translateFunction]
  rw [← h1]
  exact hΨ0

end Descent

section Base

open ComplexRankZero (quotientUnits unitsExtend unitsExtend_val exists_measure_eq quotientUnits_mk
  quotientUnits_symm_out)
open Langlands.Whittaker.UpperUnipotentCharacter (adjacentUnit transvection_apply)

variable {r : ℕ} (h0 : 0 < r)

/-- The simple-root unipotent `1 + z E₁₂` of `GL_(r+1)`. -/
def firstRoot (z : ℂ) : Langlands.GeneralLinear.upperUnipotent (r + 1) ℂ :=
  adjacentUnit ⟨0, h0⟩ z

theorem character_firstRoot (a : ℂˣ) (z : ℂ) :
    complexWhittakerCharacter a (firstRoot h0 z).val = (complexScaledCharacter a).complex z := by
  let i : Fin r := ⟨0, h0⟩
  unfold complexWhittakerCharacter
  congr 1
  change (∑ j : Fin r, Matrix.transvection i.castSucc i.succ z j.castSucc j.succ) = z
  simp only [transvection_apply, ne_of_lt Fin.castSucc_lt_succ, ite_false, zero_add,
    Fin.castSucc_inj, Fin.succ_inj, and_self]
  simp

theorem pad_mul_firstRoot (g : GL 1) (z : ℂ) :
    padGL (Nat.succ_le_succ h0.le) g * (firstRoot h0 z).val =
      (firstRoot h0 (g.val.det * z)).val * padGL (Nat.succ_le_succ h0.le) g := by
  let i : Fin r := ⟨0, h0⟩
  let A := padGL (Nat.succ_le_succ h0.le) g
  have hcol (k : Fin (r + 1)) : A.val k i.castSucc = if k = i.castSucc then g.val.det else 0 := by
    rw [UnequalAnalytic.padGL_apply]
    by_cases hk : k = i.castSucc
    · subst k
      have hi : i.castSucc.val < 1 := Nat.zero_lt_one
      rw [dite_eq_left ⟨hi, hi⟩, ite_eq_left rfl, Matrix.det_fin_one]
      rfl
    · have hk0 : ¬ k.val < 1 := by
        intro hk1
        apply hk
        exact Fin.ext (by change k.val = 0; omega)
      rw [dite_eq_right (fun h' => hk0 h'.1), Matrix.one_apply_ne hk, ite_eq_right hk]
  have hrow (k : Fin (r + 1)) : A.val i.succ k = if i.succ = k then 1 else 0 := by
    rw [UnequalAnalytic.padGL_apply, dite_eq_right (fun h' => by
      have h'1 := h'.1
      change 1 < 1 at h'1
      omega), Matrix.one_apply]
  apply Units.ext
  change A.val * (1 + Matrix.single i.castSucc i.succ z) =
    (1 + Matrix.single i.castSucc i.succ (g.val.det * z)) * A.val
  rw [mul_add, add_mul, mul_one, one_mul]
  congr 1
  ext k l
  by_cases hk : k = i.castSucc
  · subst k
    rw [Matrix.single_mul_apply_same, hrow]
    by_cases hl : l = i.succ
    · subst l
      rw [Matrix.mul_single_apply_same, hcol, ite_eq_left rfl, ite_eq_left rfl, mul_one]
    · rw [Matrix.mul_single_apply_of_ne z _ _ _ _ hl, ite_eq_right (Ne.symm hl), mul_zero]
  · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hk]
    by_cases hl : l = i.succ
    · subst l
      rw [Matrix.mul_single_apply_same, hcol, ite_eq_right hk, zero_mul]
    · rw [Matrix.mul_single_apply_of_ne z _ _ _ _ hl]

theorem integrand_firstRoot {a : ℂˣ} {W : (GL (r + 1)) → ℂ} (hW : HasLeftCharacter a W)
    (V : GL 1 → ℂ) (b s : ℂ) (q : Langlands.RankinSelberg.LeftUnipotentQuotient 0 ℂ) :
    complexUnequalIntegrand h0 (ρ (firstRoot h0 b).val W) V s q =
      (complexScaledCharacter a).complex ((quotientUnits q : ℂ) * b) *
        complexUnequalIntegrand h0 W V s q := by
  have hdet : (quotientUnits q : ℂ) = q.out.val.det :=
    congrArg Units.val ((congrArg quotientUnits (Quotient.out_eq q).symm).trans
      (quotientUnits_mk q.out))
  simp only [complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand,
    ArchimedeanLocal.translateFunction]
  rw [pad_mul_firstRoot h0, hW _ _, character_firstRoot, hdet]
  simp only [mul_assoc]

private theorem fourier_eq_zero_of_character_integrals {f : ℂ → ℂ} (a : ℂˣ)
    (hzero : ∀ b : ℂ, (∫ z, (complexScaledCharacter a).complex (z * b) * f z) = 0) :
    𝓕 f = 0 := by
  funext w
  change 𝓕 f w = 0
  rw [Real.fourier_eq]
  let b : ℂ := -(star w) / (2 * (a : ℂ))
  have htrace (z : ℂ) : Algebra.trace ℝ ℂ ((a : ℂ) * (z * b)) = -(inner ℝ z w) := by
    have hmul : (a : ℂ) * (z * b) = -(z * star w) / 2 := by
      dsimp [b]
      field_simp [a.ne_zero]
    rw [hmul, Algebra.trace_complex_apply]
    simp [real_inner_comm, Complex.inner, Complex.div_ofNat_re]
    ring
  simp_rw [show ∀ z : ℂ, 𝐞 (-(inner ℝ z w)) • f z =
      (complexScaledCharacter a).complex (z * b) * f z by
    intro z
    rw [Circle.smul_def]
    change (Real.fourierChar (-(inner ℝ z w)) : ℂ) * f z =
      (complexScaledCharacter a (z * b) : ℂ) * f z
    rw [complexScaledCharacter_apply, htrace]]
  exact hzero b

/-- **Base of the descent.** For the smaller group `GL₁(ℂ)`, vanishing of the ordinary
integrals of all right translates on right half-planes forces `W(1) V(1) = 0`. -/
theorem base (D : ComplexQuotientMeasureData 0) {a : ℂˣ} {W : (GL (r + 1)) → ℂ}
    {V : GL 1 → ℂ} (hW : IsGood a W) (hV : IsGood (-a) V)
    (hvan : ∀ γ : GL (r + 1), ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      complexUnequalIntegral h0 D (ρ γ W) V s = 0) :
    W 1 * V 1 = 0 := by
  obtain ⟨σ, hdom⟩ := ComplexUnequalFamily.ordinary_halfPlaneDomination h0 D (univ : Set ℂ)
    (fun _ => W) (fun _ => V) id (fun _ => hW.left) (fun _ => hV.left)
    (constant_rootBound hW) (constant_rootBound hV)
  have hcont (W' : (GL (r + 1)) → ℂ) (hW' : IsGood a W') (s : ℂ) :
      Continuous (complexUnequalIntegrand h0 W' V s) :=
    ComplexUnequalFamily.continuous_ordinaryKernel h0 hW'.left hV.left hW'.continuous
      hV.continuous s
  have hint (s : ℂ) (hs : σ < s.re) : Integrable (complexUnequalIntegrand h0 W V s) D.measure := by
    obtain ⟨M, hM, hbound⟩ := hdom s.re
    exact hM.mono' (hcont _ hW s).aestronglyMeasurable
      (ae_of_all _ (hbound s (mem_univ s) hs le_rfl))
  have hhol (b : ℂ) : DifferentiableOn ℂ
      (complexUnequalIntegral h0 D (ρ (firstRoot h0 b).val W) V) {s | σ < s.re} := by
    let K := fun s => complexUnequalIntegrand h0 (ρ (firstRoot h0 b).val W) V s
    have hK : ∀ s q, K s q = (complexScaledCharacter a).complex ((quotientUnits q : ℂ) * b) *
        complexUnequalIntegrand h0 W V s q := integrand_firstRoot h0 hW.left V b
    have hdomK : ComplexUnequalFamily.HalfPlaneDomination D.measure univ id K σ := by
      intro τ
      obtain ⟨M, hM, hbound⟩ := hdom τ
      refine ⟨M, hM, fun s hs hσ hτ q => ?_⟩
      simpa only [hK, id_eq, norm_mul, HarmonicAnalysis.UnitaryAdditiveCharacter.norm_complex,
        one_mul] using hbound s hs hσ hτ q
    have hKd (q : Langlands.RankinSelberg.LeftUnipotentQuotient 0 ℂ) :
        Differentiable ℂ (fun s => K s q) :=
      (ComplexUnequalFamily.differentiable_detPower_parameter q.out differentiable_id _).const_mul _
    have hd := (ComplexUnequalFamily.differentiableOn_integral_of_halfPlaneDomination isOpen_univ
      differentiable_id (fun s => (hcont _ (hW.translate _) s).aestronglyMeasurable)
      (fun q => (hKd q).differentiableOn) hdomK).2
    change DifferentiableOn ℂ (fun s => ∫ q, K s q ∂D.measure) _
    simpa only [univ_inter, id_eq] using hd
  let s₀ : ℂ := ((σ + 1 : ℝ) : ℂ)
  have hs₀ : σ < s₀.re := by simp [s₀]
  have hTranslated (b : ℂ) :
      complexUnequalIntegral h0 D (ρ (firstRoot h0 b).val W) V s₀ = 0 := by
    obtain ⟨τ, hτ⟩ := hvan (firstRoot h0 b).val
    exact eq_zero_on_right_of_differentiableOn (hhol b) hτ s₀ hs₀
  let H := complexUnequalIntegrand h0 W V s₀
  let f (z : ℂ) : ℂ := (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) * unitsExtend H z
  obtain ⟨κ, hκ, hmeasure⟩ := exists_measure_eq D
  have hf : Integrable f := (ComplexRankZero.integrable_iff hκ hmeasure H).mp (hint s₀ hs₀)
  have hzeroF : ∀ b : ℂ, (∫ z, (complexScaledCharacter a).complex (z * b) * f z) = 0 := by
    intro b
    let I := complexUnequalIntegrand h0 (ρ (firstRoot h0 b).val W) V s₀
    have hη := ComplexRankZero.integral_eq hmeasure I
    have hzerob : (∫ q, I q ∂D.measure) = 0 := hTranslated b
    rw [hzerob] at hη
    have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ
    refine Eq.trans ?_ ((mul_eq_zero.mp hη.symm).resolve_left hκ')
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : z = 0
    · simp [f, unitsExtend, hz]
    · let u := Units.mk0 z hz
      change (complexScaledCharacter a).complex (z * b) *
        ((((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) * unitsExtend H u) =
          (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) * unitsExtend I u
      rw [unitsExtend_val, unitsExtend_val]
      dsimp only [I, H]
      rw [integrand_firstRoot h0 hW.left, quotientUnits.apply_symm_apply]
      change _ = _ * ((complexScaledCharacter a).complex (z * b) * _)
      ac_rfl
  have hHc : Continuous H := hcont W hW s₀
  have hc : ContinuousAt f 1 := by
    change ContinuousAt f ((1 : ℂˣ) : ℂ)
    rw [← Units.isOpenEmbedding_val.continuousAt_iff]
    simp only [Function.comp_def, f, unitsExtend_val]
    have hnorm : ContinuousAt (fun u : ℂˣ => ‖(u : ℂ)‖ ^ 2) 1 :=
      (Units.continuous_val.norm.pow 2).continuousAt
    exact (Complex.continuous_ofReal.continuousAt.comp
      (hnorm.inv₀ (by simp))).mul (hHc.comp quotientUnits.symm.continuous).continuousAt
  have hFourier := fourier_eq_zero_of_character_integrals a hzeroF
  have hf₁ : f 1 = 0 := by
    have hinv := hf.fourierInv_fourier_eq (hFourier.symm ▸ integrable_zero _ _ _) hc
    simpa [hFourier, Real.fourierInv_eq] using hinv.symm
  have hq : (quotientUnits.symm 1).out = (1 : GL 1) := by
    rw [quotientUnits_symm_out, map_one]
  change (((‖((1 : ℂˣ) : ℂ)‖ ^ 2)⁻¹ : ℝ) : ℂ) * unitsExtend H (1 : ℂˣ) = 0 at hf₁
  rw [unitsExtend_val] at hf₁
  simpa only [Units.val_one, norm_one, one_pow, inv_one, Complex.ofReal_one, one_mul,
    H, complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand, hq, map_one, detPower_one,
    mul_one] using hf₁

end Base

section Induction

/-- **Iterated descent.** Vanishing on right half-planes of the ordinary integrals of all right
translates of `W` against `V` forces `W(1) V(1) = 0`, for every smaller rank. -/
theorem eq_zero_of_translates_vanish {r : ℕ} {a : ℂˣ} {W : (GL (r + 1)) → ℂ} (hW : IsGood a W) :
    ∀ (t : ℕ) (h : t < r) (D : ComplexQuotientMeasureData t) (V : (GL (t + 1)) → ℂ),
      IsGood (-a) V →
      (∀ γ : GL (r + 1), ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        complexUnequalIntegral h D (ρ γ W) V s = 0) →
      W 1 * V 1 = 0 := by
  intro t
  induction t with
  | zero =>
    intro h D V hV hvan
    exact base h D hW hV hvan
  | succ k ih =>
    intro h D V hV hvan
    have h' := ih (Nat.lt_of_succ_lt h) (complexQuotientMeasureData k) (restrict V) hV.restrict
      (descent h D (complexQuotientMeasureData k) hW hV hvan)
    simpa [restrict] using h'

end Induction

end Langlands.Global.RankinSelbergGlobal.ComplexUnequalOrdinaryDescent
