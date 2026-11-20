import Langlands.Automorphic.CuspidalL2.SiegelCover

/-! # Band bounds for smooth cuspidal functions on `GL_n`

Let `f` be a smooth function on `GL_n(F) \ GL_n(𝔸)` (finite level, smooth in the archimedean
variable) such that every enveloping derivative `u · f` is cuspidal and all these derivatives
grow at most like `exp (c ∑ |x i|)` on the torus translates `torInf x * Q` of compact sets, for
one `c`. Then every `u · f` is bounded on every determinant band `lo ≤ |det| ≤ hi`.

The proof is the Library's argument for operator realizations (modules `CuspidalL2.Decay`,
`CuspidalL2.Representation`, `CuspidalL2.SiegelCover`), applied to the family of enveloping
derivatives of `f` with the exponential weight in place of a power of the height. -/

noncomputable section
universe u
open scoped Classical
open NumberField
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.SmoothWhittakerExpansion

open Langlands.Global Langlands.Automorphic Langlands.Automorphic.CuspidalL2
  Langlands.Automorphic.ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance decayAddCommGroupRationalInvariant :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance decayAddCommGroupContinuousRational :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance decayAddCommGroupFiniteSmoothRational :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _

/-- All enveloping derivatives of a finite-smooth function share one open finite level. -/
theorem exists_common_level (f : FiniteSmoothRationalFunctions F n) :
    ∃ L : Subgroup (FiniteAdelicGL F n), IsOpen (L : Set (FiniteAdelicGL F n)) ∧
      ∀ (u : ArchimedeanGL.EnvelopingAlgebra F n) (g : AdelicGL F n), ∀ l ∈ L,
        evaluate F n (finiteSmoothEnvelopingAction F n u f).val (g * AdelicGL.ofFinite F n l) =
          evaluate F n (finiteSmoothEnvelopingAction F n u f).val g := by
  obtain ⟨L, hL⟩ := f.property.2
  refine ⟨L.toSubgroup, L.isOpen, fun u g l hl => ?_⟩
  have hf : f.val ∈ levelSubmodule F n L.toSubgroup := fun l => hL l
  have h : continuousRightAction F n (AdelicGL.ofFinite F n l)
      (finiteSmoothEnvelopingAction F n u f).val =
      (finiteSmoothEnvelopingAction F n u f).val :=
    finiteSmoothEnvelopingAction_preserves_level F n u L f hf ⟨l, hl⟩
  exact congrArg (fun G : ContinuousRationalFunctions F n => evaluate F n G g) h

/-- The archimedean slices of the enveloping derivatives, with their basis derivatives. -/
theorem slice_data (f : FiniteSmoothRationalFunctions F n)
    (u : ArchimedeanGL.EnvelopingAlgebra F n) (y : FiniteAdelicGL F n) :
    ∃ s : ArchimedeanGL.SmoothFunctions F n,
      (∀ g, s.val g = evaluate F n (finiteSmoothEnvelopingAction F n u f).val
        (AdelicGL.ofInfinite F n g * AdelicGL.ofFinite F n y)) ∧
      ∀ k g, (ArchimedeanGL.smoothDifferential F n (ArchimedeanGL.lieDirection F n k) s).val g =
        evaluate F n (finiteSmoothEnvelopingAction F n
          (OperatorRealization.basisGenerator F n k * u) f).val
          (AdelicGL.ofInfinite F n g * AdelicGL.ofFinite F n y) := by
  refine ⟨finiteSmoothSlice F n y (finiteSmoothEnvelopingAction F n u f), fun g => ?_,
    fun k g => ?_⟩
  · rw [finiteSmoothSlice_apply, OperatorRealization.pair_eq_ofInfinite_mul_ofFinite]
  · have e2 := finiteSmoothSlice_envelopingAction F n (OperatorRealization.basisGenerator F n k)
      (finiteSmoothEnvelopingAction F n u f) y
    have e3 : ArchimedeanGL.envelopingAction F n (OperatorRealization.basisGenerator F n k) =
        ArchimedeanGL.smoothDifferential F n (ArchimedeanGL.lieDirection F n k) :=
      ArchimedeanGL.envelopingAction_real_generator F n (ArchimedeanGL.lieDirection F n k)
    have e5 : finiteSmoothEnvelopingAction F n (OperatorRealization.basisGenerator F n k * u) f =
        finiteSmoothEnvelopingAction F n (OperatorRealization.basisGenerator F n k)
          (finiteSmoothEnvelopingAction F n u f) :=
      LinearMap.congr_fun (map_mul (finiteSmoothEnvelopingAction F n)
        (OperatorRealization.basisGenerator F n k) u) f
    rw [e5, ← OperatorRealization.pair_eq_ofInfinite_mul_ofFinite, ← finiteSmoothSlice_apply,
      e2, e3]

/-- Vanishing of one constant term gives the mean-value form of cuspidality used by the
decay induction. -/
theorem norm_le_of_constantTerm_eq_zero [CompactSpace (AdeleQuotient F)] {a b : ℕ}
    (h : a + b = n) (f : ContinuousRationalFunctions F n) (g : AdelicGL F n)
    (h0 : constantTerm F n h f g = 0) (M : ℝ)
    (hM : ∀ Y : Matrix (Fin a) (Fin b) (Adeles F),
      ‖evaluate F n f (GeneralLinear.blockUnipotent h Y * g) - evaluate F n f g‖ ≤ M) :
    ‖evaluate F n f g‖ ≤ M := by
  have hint := integrable_constantTermIntegrand h f g
  have key : evaluate F n f g =
      ∫ X, (evaluate F n f g - constantTermIntegrand F n h f g X)
        ∂(matrixQuotientHaar F a b) := by
    rw [MeasureTheory.integral_sub (MeasureTheory.integrable_const _) hint,
      MeasureTheory.integral_const]
    unfold constantTerm at h0
    rw [h0]
    simp
  rw [key]
  calc _ ≤ M * (matrixQuotientHaar F a b).real Set.univ :=
        MeasureTheory.norm_integral_le_of_norm_le_const
          (Filter.Eventually.of_forall fun X => by
            rw [norm_sub_rev]
            exact hM (matrixLift X))
    _ = M := by simp

variable [CompactSpace (AdeleQuotient F)]

/-- **Rapid decay along a maximal block.** If every enveloping derivative of `f` is cuspidal
and bounded by `C * exp (c ∑ |x i|)` on `torInf x * Q` for compact `Q`, then along every
maximal block each derivative gains a factor `exp (-N ℓ)` on the region where all
across-the-block gaps are at most `-ℓ ≤ 0`. -/
theorem exists_blockDecay (f : FiniteSmoothRationalFunctions F n)
    (hcusp : ∀ u, IsCuspidal F n (finiteSmoothEnvelopingAction F n u f).val) {c : ℝ}
    (hgrowth : ∀ (u : ArchimedeanGL.EnvelopingAlgebra F n) (Q : Set (AdelicGL F n)),
      IsCompact Q → ∃ C : ℝ, ∀ x, ∀ q ∈ Q,
        ‖evaluate F n (finiteSmoothEnvelopingAction F n u f).val
            (AdelicGL.ofInfinite F n (torInf F n x) * q)‖ ≤
          C * Real.exp (c * ∑ i, |x i|))
    (u : ArchimedeanGL.EnvelopingAlgebra F n) (Q : Set (AdelicGL F n)) (hQ : IsCompact Q)
    {a b : ℕ} (h : a + b = n) (ha : 0 < a) (hb : 0 < b) (N : ℕ) :
    ∃ C : ℝ, ∀ (x : Fin n → ℝ) (ℓ : ℝ), 0 ≤ ℓ →
      (∀ p r, x (finSumFinEquiv.trans (finCongr h) (Sum.inr r)) -
        x (finSumFinEquiv.trans (finCongr h) (Sum.inl p)) ≤ -ℓ) →
      ∀ q ∈ Q, ‖evaluate F n (finiteSmoothEnvelopingAction F n u f).val
          (AdelicGL.ofInfinite F n (torInf F n x) * q)‖ ≤
        C * Real.exp (-(N * ℓ)) * Real.exp (c * ∑ i, |x i|) := by
  obtain ⟨L, hLo, hlevel⟩ := exists_common_level f
  exact blockDecay_of_cuspidal F n h
    (fun u => evaluate F n (finiteSmoothEnvelopingAction F n u f).val)
    (fun k u => OperatorRealization.basisGenerator F n k * u)
    (fun u γ g => evaluate_rational F n _ γ g)
    L hLo hlevel (fun u y => slice_data f u y)
    (fun u g M hM => norm_le_of_constantTerm_eq_zero h _ g (hcusp u a b h ha hb g) M hM)
    Set.univ (fun x => Real.exp (c * ∑ i, |x i|))
    (fun u Q' hQ' _ => hgrowth u Q' hQ') N u Q hQ (fun _ _ => Set.mem_univ _)

/-- **Boundedness on the chamber.** On torus translates `torInf x * Q` of a compact set,
with `x` in a chamber and of bounded sum, every enveloping derivative of `f` is bounded. -/
theorem exists_chamber_bound (f : FiniteSmoothRationalFunctions F n)
    (hcusp : ∀ u, IsCuspidal F n (finiteSmoothEnvelopingAction F n u f).val) {c : ℝ}
    (hc : 0 ≤ c)
    (hgrowth : ∀ (u : ArchimedeanGL.EnvelopingAlgebra F n) (Q : Set (AdelicGL F n)),
      IsCompact Q → ∃ C : ℝ, ∀ x, ∀ q ∈ Q,
        ‖evaluate F n (finiteSmoothEnvelopingAction F n u f).val
            (AdelicGL.ofInfinite F n (torInf F n x) * q)‖ ≤
          C * Real.exp (c * ∑ i, |x i|))
    (u : ArchimedeanGL.EnvelopingAlgebra F n) (Q : Set (AdelicGL F n)) (hQ : IsCompact Q)
    {K R : ℝ} (hK : 0 ≤ K) :
    ∃ C : ℝ, ∀ x : Fin n → ℝ, Chamber K x → |∑ i, x i| ≤ R → ∀ q ∈ Q,
      ‖evaluate F n (finiteSmoothEnvelopingAction F n u f).val
          (AdelicGL.ofInfinite F n (torInf F n x) * q)‖ ≤ C := by
  obtain ⟨C₁, hC₁⟩ := hgrowth u Q hQ
  set B₀ : ℝ := n * (R + n * (n * (K + 2 * n * K))) with hB₀
  set N : ℕ := ⌈(n : ℝ) ^ 3 * c⌉₊ with hN
  have hblock : ∀ a : Fin n, ∃ Cb : ℝ, 0 < a.val → ∀ (x : Fin n → ℝ) (ℓ : ℝ), 0 ≤ ℓ →
      (∀ i j : Fin n, i.val < a.val → a.val ≤ j.val → x j - x i ≤ -ℓ) → ∀ q ∈ Q,
        ‖evaluate F n (finiteSmoothEnvelopingAction F n u f).val
            (AdelicGL.ofInfinite F n (torInf F n x) * q)‖ ≤
          Cb * Real.exp (-(N * ℓ)) * Real.exp (c * ∑ i, |x i|) := by
    intro a
    by_cases ha : 0 < a.val
    · have h : a.val + (n - a.val) = n := Nat.add_sub_cancel' a.isLt.le
      obtain ⟨Cb, hCb⟩ := exists_blockDecay f hcusp hgrowth u Q hQ h ha (by omega) N
      refine ⟨Cb, fun _ x ℓ hℓ hx q hq => hCb x ℓ hℓ (fun p r => hx _ _ ?_ ?_) q hq⟩
      · simp
      · simp
    · exact ⟨0, fun h => absurd h ha⟩
  choose Cb hCb using hblock
  have hE : 0 < Real.exp (c * B₀) := Real.exp_pos _
  refine ⟨|C₁| * Real.exp (c * B₀) + (∑ a, |Cb a|) * Real.exp (c * B₀),
    fun x hx hR q hq => ?_⟩
  have hS : 0 ≤ (∑ a, |Cb a|) * Real.exp (c * B₀) :=
    mul_nonneg (Finset.sum_nonneg fun a _ => abs_nonneg _) hE.le
  rcases chamber_alternative hK x hx hR with h1 | ⟨a, ha, ℓ, hℓ, hgap, h2⟩
  · calc _ ≤ C₁ * Real.exp (c * ∑ i, |x i|) := hC₁ x q hq
      _ ≤ |C₁| * Real.exp (c * B₀) :=
          mul_le_mul (le_abs_self _) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h1 hc))
            (Real.exp_pos _).le (abs_nonneg _)
      _ ≤ _ := le_add_of_nonneg_right hS
  · have hkey : -(N * ℓ) + c * ∑ i, |x i| ≤ c * B₀ := by
      have hNc : (n : ℝ) ^ 3 * c ≤ N := Nat.le_ceil _
      have h3 := mul_le_mul_of_nonneg_left h2 hc
      have h4 := mul_le_mul_of_nonneg_right hNc hℓ
      have e : c * (B₀ + (n : ℝ) ^ 3 * ℓ) = c * B₀ + (n : ℝ) ^ 3 * c * ℓ := by ring
      linarith
    have hCa : |Cb a| ≤ ∑ a, |Cb a| :=
      Finset.single_le_sum (f := fun a => |Cb a|) (fun a _ => abs_nonneg _)
        (Finset.mem_univ a)
    calc _ ≤ Cb a * Real.exp (-(N * ℓ)) * Real.exp (c * ∑ i, |x i|) :=
          hCb a ha x ℓ hℓ hgap q hq
      _ ≤ |Cb a| * Real.exp (-(N * ℓ)) * Real.exp (c * ∑ i, |x i|) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
            (Real.exp_pos _).le
      _ = |Cb a| * Real.exp (-(N * ℓ) + c * ∑ i, |x i|) := by
          rw [Real.exp_add, mul_assoc]
      _ ≤ (∑ a, |Cb a|) * Real.exp (c * B₀) :=
          mul_le_mul hCa (Real.exp_le_exp.mpr hkey) (Real.exp_pos _).le
            (Finset.sum_nonneg fun a _ => abs_nonneg _)
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg (abs_nonneg _) hE.le)

/-- **Band bound.** Every enveloping derivative of `f` is bounded on every determinant band
`lo ≤ |det| ≤ hi` with `lo > 0`. -/
theorem exists_band_bound (f : FiniteSmoothRationalFunctions F n)
    (hcusp : ∀ u, IsCuspidal F n (finiteSmoothEnvelopingAction F n u f).val) {c : ℝ}
    (hc : 0 ≤ c)
    (hgrowth : ∀ (u : ArchimedeanGL.EnvelopingAlgebra F n) (Q : Set (AdelicGL F n)),
      IsCompact Q → ∃ C : ℝ, ∀ x, ∀ q ∈ Q,
        ‖evaluate F n (finiteSmoothEnvelopingAction F n u f).val
            (AdelicGL.ofInfinite F n (torInf F n x) * q)‖ ≤
          C * Real.exp (c * ∑ i, |x i|))
    (u : ArchimedeanGL.EnvelopingAlgebra F n) {lo hi : ℝ} (hlo : 0 < lo) :
    ∃ B : ℝ, ∀ g : AdelicGL F n, lo ≤ absDet F n g → absDet F n g ≤ hi →
      ‖evaluate F n (finiteSmoothEnvelopingAction F n u f).val g‖ ≤ B := by
  obtain ⟨Q₁, K, hQ₁, hK, hdec⟩ := exists_siegelDecomposition F n
  obtain ⟨L, hL⟩ : ∃ L : ℝ, ∀ q ∈ Q₁, |Real.log (absDet F n q)| ≤ L :=
    (hQ₁.image (continuous_abs.comp ((continuous_absDet F n).log
      fun g => (absDet_pos F n g).ne'))).bddAbove.elim
      fun L hL => ⟨L, fun q hq => hL ⟨q, hq, rfl⟩⟩
  obtain ⟨C, hC⟩ := exists_chamber_bound f hcusp hc hgrowth u Q₁ hQ₁
    (R := max |Real.log lo| |Real.log hi| + L) hK
  refine ⟨C, fun g hlg hhg => ?_⟩
  obtain ⟨γr, y, q, hq, hγ, hy⟩ := hdec g
  have hRy : |∑ i, y i| ≤ max |Real.log lo| |Real.log hi| + L := by
    have h1 := abs_sum_le_of_absDet F n y q
    rw [← hγ, absDet_rational_mul] at h1
    have hl := Real.log_le_log hlo hlg
    have hh := Real.log_le_log (absDet_pos F n g) hhg
    have h2 : |Real.log (absDet F n g)| ≤ max |Real.log lo| |Real.log hi| :=
      abs_le.mpr ⟨by linarith [neg_abs_le (Real.log lo), le_max_left |Real.log lo| |Real.log hi|],
        by linarith [le_abs_self (Real.log hi), le_max_right |Real.log lo| |Real.log hi|]⟩
    linarith [hL q hq]
  have h := hC y hy hRy q hq
  rw [← hγ, evaluate_rational] at h
  exact h

end Langlands.Global.SmoothWhittakerExpansion
