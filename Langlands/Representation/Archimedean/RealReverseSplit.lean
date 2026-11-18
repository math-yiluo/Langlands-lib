import Langlands.Representation.Archimedean.RealSplitFrobenius
import Langlands.Representation.Archimedean.RealReverseTwist
import Langlands.Representation.Archimedean.RealReverseTransfer

/-!
# The transpose of an intertwiner to the reversed standard module

Let `ds` be a list of real blocks of rank `n` and `T` a `(𝔤, K)`-intertwiner from the
`O(n)`-finite functions of the real standard module of `ds` to those of `ds.reverse`. The
position characters of `split ds` (module `RealSplitFrobenius`) are those of `ds.reverse` in the
opposite order, so the pullback along the twist `g ↦ w₀ (gᵀ)⁻¹` carries the principal series of
`split ds` to the dual principal series of `ds.reverse`, and `T w` to a function `L w` of the
dual principal series of `split ds` (`realPositionCharacter_split`). This module proves
(`exists_splitTranspose`):

* for every `f` of the standard module of `split ds` there is an `O(n)`-finite `u` of the dual
  principal series of `ds` with `∫ u(κ g) w(κ) dκ = ∫ (L w)(κ gᵀ) f(κ) dκ` for all `w` and `g`;
* for every `w` there is an `O(n)`-finite `z` of the dual principal series of `ds` with
  `∫ z (D f) = ∫ (L w) f` and `∫ (L w)(κ g) f(κ) dκ = ∫ z(κ g) (D f)(κ) dκ` for all `f` and `g`,
  where `D` is the split map of `RealSplitFrobenius.exists_splitMap`.

The second item uses that `L w` satisfies the Fourier condition of the induction blocks of `ds`
(`twistLin_tail`): conjugation by `w₀` carries the rotations in the coordinates `p, p + 1` to the
inverse rotations in the coordinates `n - 2 - p, n - 1 - p`, where `ds.reverse` has the same
induction block (`realInducedBlockAt_reverse`).
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

open MeasureTheory

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

namespace RealReverseSplit

open RealJacquetFrobenius RealBlockPosition RealSplitFrobenius RealReverseTwist RealReverseTransfer
open RealBlockFourierFinite RealBlockRotation RealBlockJacquet RealPrincipalSeriesDuality
open RealStrictCharacterLanglandsQuotient PartialJacquet JacquetKernel
open Langlands.LocalFactor.Archimedean

attribute [local instance] measurableSpaceK

local instance borelSpaceK_rs (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

variable {n : ℕ}

/-! ## Positions of the split list and of the reversed list -/

theorem realRank_reverse (ds : List RealBlock) : realRank ds.reverse = realRank ds := by
  simp [realRank, List.map_reverse, List.sum_reverse]

theorem realRank_cons' (b : RealBlock) (ds : List RealBlock) :
    realRank (b :: ds) = realRank [b] + realRank ds := by
  rw [← realRank_append']
  rfl

/-- A position datum with the concatenation law that is reversed on every split block is
reversed on every split list. -/
theorem split_reverse_position {α : Type*} (P : List RealBlock → ℕ → α)
    (happ : ∀ (xs ys : List RealBlock) (i : ℕ),
      P (xs ++ ys) i = if i < realRank xs then P xs i else P ys (i - realRank xs))
    (hbase : ∀ (b : RealBlock) (l : ℕ), l < realRank [b] →
      P (splitBlock b) l = P [b] (realRank [b] - 1 - l)) :
    ∀ (ds : List RealBlock) (l : ℕ), l < realRank ds →
      P (split ds) l = P ds.reverse (realRank ds - 1 - l)
  | [], l, hl => by simp [realRank] at hl
  | b :: ds, l, hl => by
      rw [split_cons, List.reverse_cons, happ, happ, realRank_splitBlock, realRank_reverse]
      rw [realRank_cons' b ds] at hl ⊢
      by_cases h : l < realRank [b]
      · have hc : ¬(realRank [b] + realRank ds - 1 - l < realRank ds) := by omega
        simp only [h, hc, ↓reduceIte]
        rw [hbase b l h]
        congr 1
        omega
      · have hc : realRank [b] + realRank ds - 1 - l < realRank ds := by omega
        simp only [h, hc, ↓reduceIte]
        rw [split_reverse_position P happ hbase ds (l - realRank [b]) (by omega)]
        congr 1
        omega

theorem realPositionSign_splitBlock (b : RealBlock) (l : ℕ) (hl : l < realRank [b]) :
    realPositionSign (splitBlock b) l = realPositionSign [b] (realRank [b] - 1 - l) := by
  cases b with
  | character c =>
      have hl' : l < 1 := hl
      interval_cases l
      rfl
  | induced e =>
      have hl' : l < 2 := hl
      interval_cases l <;> rfl

theorem realPositionExponent_splitBlock (b : RealBlock) (l : ℕ) (hl : l < realRank [b]) :
    GramFormula.realPositionExponent (splitBlock b) l = GramFormula.realPositionExponent [b] (realRank [b] - 1 - l) := by
  cases b with
  | character c =>
      have hl' : l < 1 := hl
      interval_cases l
      rfl
  | induced e =>
      have hl' : l < 2 := hl
      interval_cases l <;> rfl

/-- **The position characters of the split list** are those of the reversed list in the
opposite order. -/
theorem realPositionCharacter_split (ds : List RealBlock) (l : ℕ) (hl : l < realRank ds) :
    realPositionCharacter (split ds) l =
      realPositionCharacter ds.reverse (realRank ds - 1 - l) := by
  funext x
  rw [realPositionCharacter_eq_charFun, realPositionCharacter_eq_charFun,
    split_reverse_position realPositionSign realPositionSign_append realPositionSign_splitBlock
      ds l hl,
    split_reverse_position GramFormula.realPositionExponent realPositionExponent_append
      realPositionExponent_splitBlock ds l hl]

theorem realPositionCharacter_inv_apply (ds : List RealBlock) (l : ℕ) (x : ℝˣ) :
    realPositionCharacter ds l x⁻¹ = (realPositionCharacter ds l x)⁻¹ := by
  rw [realPositionCharacter_eq_charFun, realPositionCharacter_eq_charFun]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← charFun_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, charFun_one]

theorem dualChar_reverse_eq {ds : List RealBlock} (hn : realRank ds = n) (j : Fin n) (z : ℝˣ) :
    dualChar (realPositionCharacter ds.reverse) j z =
      realPositionCharacter (split ds) (Fin.rev j) z⁻¹ := by
  rw [realPositionCharacter_split ds _ (by rw [hn]; exact (Fin.rev j).isLt),
    realPositionCharacter_inv_apply]
  have h : realRank ds - 1 - ((Fin.rev j : Fin n) : ℕ) = j := by
    rw [Fin.val_rev, hn]
    omega
  rw [h]
  rfl

theorem dualChar_split_eq {ds : List RealBlock} (hn : realRank ds = n) (j : Fin n) (z : ℝˣ) :
    dualChar (realPositionCharacter (split ds)) j z =
      realPositionCharacter ds.reverse (Fin.rev j) z⁻¹ := by
  change (realPositionCharacter (split ds) j z)⁻¹ = _
  rw [realPositionCharacter_split ds _ (by rw [hn]; exact j.isLt),
    realPositionCharacter_inv_apply]
  have h : realRank ds - 1 - (j : ℕ) = ((Fin.rev j : Fin n) : ℕ) := by
    rw [Fin.val_rev, hn]
    omega
  rw [h]

/-! ## Induction blocks of the reversed list -/

/-- An induction block of `ds` at the first position `p` is an induction block of `ds.reverse`
at the first position `realRank ds - 2 - p`. -/
theorem realInducedBlockAt_reverse : ∀ {ds : List RealBlock} {p : ℕ} {d : ComplexCharacterData},
    realInducedBlockAt ds p = some d →
      realInducedBlockAt ds.reverse (realRank ds - 2 - p) = some d
  | [], _, _, h => by simp [realInducedBlockAt] at h
  | .character _ :: _, 0, _, h => by simp [realInducedBlockAt] at h
  | .character c :: ds, p + 1, d, h => by
      have h' : realInducedBlockAt ds p = some d := h
      have hlt := realInducedBlockAt_lt h'
      have hr : realRank (RealBlock.character c :: ds) = realRank ds + 1 := by
        rw [realRank_cons]
        simp only [RealBlock.rank]
        omega
      rw [hr, List.reverse_cons,
        realInducedBlockAt_append_of_lt (by rw [realRank_reverse]; omega),
        show realRank ds + 1 - 2 - (p + 1) = realRank ds - 2 - p by omega]
      exact realInducedBlockAt_reverse h'
  | .induced e :: ds, 0, d, h => by
      have h' : e = d := by simpa [realInducedBlockAt] using h
      subst h'
      have hr : realRank (RealBlock.induced e :: ds) = realRank ds + 2 := by
        rw [realRank_cons]
        simp only [RealBlock.rank]
        omega
      rw [hr, List.reverse_cons,
        realInducedBlockAt_append_of_le (by rw [realRank_reverse]; omega), realRank_reverse,
        show realRank ds + 2 - 2 - 0 - realRank ds = 0 by omega]
      rfl
  | .induced _ :: _, 1, _, h => by simp [realInducedBlockAt] at h
  | .induced e :: ds, p + 2, d, h => by
      have h' : realInducedBlockAt ds p = some d := h
      have hlt := realInducedBlockAt_lt h'
      have hr : realRank (RealBlock.induced e :: ds) = realRank ds + 2 := by
        rw [realRank_cons]
        simp only [RealBlock.rank]
        omega
      rw [hr, List.reverse_cons,
        realInducedBlockAt_append_of_lt (by rw [realRank_reverse]; omega),
        show realRank ds + 2 - 2 - (p + 2) = realRank ds - 2 - p by omega]
      exact realInducedBlockAt_reverse h'

/-! ## Rotations and the twist -/

/-- `w₀ r_p(θ) = r_{n-2-p}(-θ) w₀`. -/
theorem w0GL_mul_blockRotation {p : ℕ} (hp : p + 1 < n) (θ : ℝ) :
    w0GL n * blockRotation n p θ = blockRotation n (n - 2 - p) (-θ) * w0GL n := by
  have hq : n - 2 - p + 1 < n := by omega
  have key : w0GL n * blockRotation n p θ * w0GL n = blockRotation n (n - 2 - p) (-θ) := by
    ext i j
    have hi := i.isLt
    have hj := j.isLt
    rw [Units.val_mul, Units.val_mul, w0GL_val, w0Mat_mul_mul_w0Mat_apply,
      blockRotation_apply hp, blockRotation_apply hq]
    simp only [Fin.val_rev, Fin.ext_iff, Real.sin_neg, Real.cos_neg, neg_neg]
    split_ifs <;> first | (exfalso; omega) | rfl
  calc w0GL n * blockRotation n p θ
      = w0GL n * blockRotation n p θ * w0GL n * w0GL n := by
        rw [mul_assoc _ (w0GL n), w0GL_mul_self, mul_one]
    _ = blockRotation n (n - 2 - p) (-θ) * w0GL n := by rw [key]

theorem twist_blockRotation_mul {p : ℕ} (hp : p + 1 < n) (θ : ℝ)
    (g : Langlands.GeneralLinear n ℝ) :
    RealReverseTwist.twist (blockRotation n p θ * g) =
      blockRotation n (n - 2 - p) (-θ) * RealReverseTwist.twist g := by
  rw [RealReverseTwist.twist_mul,
    RealReverseTwist.twist_of_mem (blockRotation_mem_unitaryCompact n p θ),
    w0GL_mul_blockRotation hp, mul_assoc]
  rfl

/-- The block Fourier coefficients of a twisted function. -/
theorem blockFourierCoefficient_twistLin {p : ℕ} (hp : p + 1 < n) (j : ℤ)
    (F : Langlands.GeneralLinear n ℝ → ℂ) (g : Langlands.GeneralLinear n ℝ) :
    blockFourierCoefficient n p j (twistLin n F) g =
      blockFourierCoefficient n (n - 2 - p) (-j) F (RealReverseTwist.twist g) := by
  rw [blockFourierCoefficient_eq_coeff, blockFourierCoefficient_eq_coeff]
  have e : (fun θ => twistLin n F (blockRotation n p θ * g)) =
      fun θ => (fun θ => F (blockRotation n (n - 2 - p) θ * RealReverseTwist.twist g)) (-θ) := by
    funext θ
    rw [twistLin_apply, twist_blockRotation_mul hp]
  rw [e]
  exact coeff_comp_neg (periodic_blockRotation_mul (by omega) F _) j

/-- **The tail condition of a twisted function.** The pullback along the twist of a function of
the standard module of `ds.reverse` satisfies the Fourier condition of the induction blocks of
`ds`. -/
theorem twistLin_tail {ds : List RealBlock} (hn : realRank ds = n)
    {F : Langlands.GeneralLinear n ℝ → ℂ} (hF : F ∈ realStandardModule n ds.reverse) :
    ∀ (p : ℕ) (d : ComplexCharacterData), realInducedBlockAt ds p = some d →
      ∀ j : ℤ, |j| < |d.weight| → ∀ g : Langlands.GeneralLinear n ℝ,
        blockFourierCoefficient n p j (twistLin n F) g = 0 := by
  intro p d hd j hj g
  have hp := realInducedBlockAt_lt hd
  rw [hn] at hp
  rw [blockFourierCoefficient_twistLin hp]
  have hrev := realInducedBlockAt_reverse hd
  rw [hn] at hrev
  exact hF.2 _ d hrev (-j) (by rwa [abs_neg]) _

/-! ## The dual of the split map -/

/-- **Transpose along a surjection with an `O(n)`-equivariant section.** Let `D` be an
intertwiner from the standard module of `split ds` to that of `ds` with an `O(n)`-equivariant
right inverse `Q`, and `x` an `O(n)`-finite function of the dual principal series of `split ds`
with `∫ x f = 0` on the kernel of `D`. Then there is an `O(n)`-finite `z` of the dual principal
series of `ds` with `∫ z (D f) = ∫ x f` and `∫ x(κ g) f(κ) dκ = ∫ z(κ g) (D f)(κ) dκ`. -/
theorem exists_transpose_of_section {ds : List RealBlock}
    (D : kFiniteFunctions (realStandardModule n (split ds)) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    (Q : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n (split ds)) (unitaryCompact ℝ n))
    (hD : IsRealStandardIntertwiner n (realStandardRep n ds) (realStandardLie n ds) (split ds) D)
    (hQ : ∀ (k : Matrix.unitaryGroup (Fin n) ℝ)
      (h : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)),
      Q (realStandardRep n ds k h) = realStandardRep n (split ds) k (Q h))
    (hDQ : ∀ h, D (Q h) = h)
    {x : Langlands.GeneralLinear n ℝ → ℂ}
    (hx : x ∈ kFiniteFunctions (principalSeries ℝ n (dualChar (realPositionCharacter (split ds))))
      (unitaryCompact ℝ n))
    (hxker : ∀ f, D f = 0 → ∫ κ : unitaryCompact ℝ n, x (κ : Langlands.GeneralLinear n ℝ) *
      (f : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n = 0) :
    ∃ z ∈ kFiniteFunctions (principalSeries ℝ n (dualChar (realPositionCharacter ds)))
        (unitaryCompact ℝ n),
      (∀ f : kFiniteFunctions (realStandardModule n (split ds)) (unitaryCompact ℝ n),
        ∫ κ, z (κ : Langlands.GeneralLinear n ℝ) * (D f : Langlands.GeneralLinear n ℝ → ℂ) κ
            ∂haarK n =
          ∫ κ, x (κ : Langlands.GeneralLinear n ℝ) * (f : Langlands.GeneralLinear n ℝ → ℂ) κ
            ∂haarK n) ∧
      ∀ (f : kFiniteFunctions (realStandardModule n (split ds)) (unitaryCompact ℝ n))
        (g : Langlands.GeneralLinear n ℝ),
        ∫ κ, x ((κ : Langlands.GeneralLinear n ℝ) * g) *
            (f : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n =
          ∫ κ, z ((κ : Langlands.GeneralLinear n ℝ) * g) *
            (D f : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n := by
  obtain ⟨z, hz, hzx⟩ := exists_pairing_transpose_of_rep (isSignedPower ds) Q hQ hx
  have hc : Continuous x := continuous_of_mem hx
  have hpair : ∀ f : kFiniteFunctions (realStandardModule n (split ds)) (unitaryCompact ℝ n),
      ∫ κ, z (κ : Langlands.GeneralLinear n ℝ) * (D f : Langlands.GeneralLinear n ℝ → ℂ) κ
          ∂haarK n =
        ∫ κ, x (κ : Langlands.GeneralLinear n ℝ) * (f : Langlands.GeneralLinear n ℝ → ℂ) κ
          ∂haarK n := by
    intro f
    rw [hzx (D f)]
    have h0 := hxker (f - Q (D f)) (by rw [map_sub, hDQ, sub_self])
    have hsub : ∫ κ : unitaryCompact ℝ n, x (κ : Langlands.GeneralLinear n ℝ) *
          ((f - Q (D f) : kFiniteFunctions (realStandardModule n (split ds))
            (unitaryCompact ℝ n)) : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n =
        ∫ κ, x (κ : Langlands.GeneralLinear n ℝ) * (f : Langlands.GeneralLinear n ℝ → ℂ) κ
            ∂haarK n -
          ∫ κ, x (κ : Langlands.GeneralLinear n ℝ) *
            (Q (D f) : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n := by
      simp only [Submodule.coe_sub, Pi.sub_apply, mul_sub]
      exact integral_sub (integrable_mul_of_continuous hc (continuous_coe _))
        (integrable_mul_of_continuous hc (continuous_coe _))
    rw [hsub] at h0
    exact (sub_eq_zero.mp h0).symm
  refine ⟨z, hz, hpair, fun f g => ?_⟩
  have h2 := integral_mul_transfer (isSignedPower (split ds)) (isSignedPower ds) D hD hz hx
    (fun f => (hpair f).symm) f g⁻¹
  have h1 := integral_mul_inv_swap (isSignedPower (split ds)) hx.1
    (mem_kFiniteFunctions_principalSeries f.2).1 g
  have h3 := integral_mul_inv_swap (isSignedPower ds) hz.1
    (mem_kFiniteFunctions_principalSeries (D f).2).1 g
  rw [← h1, ← h2, h3]

/-! ## The twisted transpose -/

/-- **The transpose identity.** For an intertwiner `T` from the standard module of `ds` to that
of `ds.reverse` and an `O(n)`-finite `f` of the principal series of `split ds` there is an
`O(n)`-finite `u` of the dual principal series of `ds` with
`∫ u(κ g) w(κ) dκ = ∫ (T w)(twist(κ gᵀ)) f(κ) dκ` for all `w` and `g`. -/
theorem exists_transpose_twist {ds : List RealBlock} (hn : realRank ds = n)
    (T : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n ds.reverse) (unitaryCompact ℝ n))
    (hT : IsRealStandardIntertwiner n (realStandardRep n ds.reverse)
      (realStandardLie n ds.reverse) ds T)
    {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ kFiniteFunctions (principalSeries ℝ n (realPositionCharacter (split ds)))
      (unitaryCompact ℝ n)) :
    ∃ u ∈ kFiniteFunctions (principalSeries ℝ n (dualChar (realPositionCharacter ds)))
        (unitaryCompact ℝ n),
      ∀ (w : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
        (g : Langlands.GeneralLinear n ℝ),
        ∫ κ, u ((κ : Langlands.GeneralLinear n ℝ) * g) *
            (w : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n =
          ∫ κ, twistLin n (T w : Langlands.GeneralLinear n ℝ → ℂ)
            ((κ : Langlands.GeneralLinear n ℝ) * transposeGL g) * f κ ∂haarK n := by
  have hv : twistLin n f ∈ kFiniteFunctions
      (principalSeries ℝ n (dualChar (realPositionCharacter ds.reverse))) (unitaryCompact ℝ n) :=
    twistLin_mem_kFiniteFunctions (dualChar_reverse_eq hn) hf
  obtain ⟨u, hu, huv⟩ := exists_pairing_transpose (isSignedPower ds) T hT hv
  refine ⟨u, hu, fun w g => ?_⟩
  have h1 := integral_mul_inv_eq_twist (T w : Langlands.GeneralLinear n ℝ → ℂ) (twistLin n f) g
  have h2 := integral_mul_transfer (isSignedPower ds) (isSignedPower ds.reverse) T hT hv hu huv
    w g⁻¹
  have h3 := integral_mul_inv_swap (isSignedPower ds) hu.1
    (mem_kFiniteFunctions_principalSeries w.2).1 g
  simp only [twistLin_apply, RealReverseTwist.twist_twist] at h1 h2 ⊢
  rw [← h3, ← h2, h1]

/-! ## The main theorem -/

/-- **The split transpose.** Let `ds` be a list of real blocks of rank `n` and `T` an
intertwiner from the `O(n)`-finite functions of the standard module of `ds` to those of
`ds.reverse`. Write `L w = (T w) ∘ twist`. There is a surjective intertwiner `D` from the
`O(n)`-finite functions of the standard module of `split ds` onto those of `ds` such that
* every `L w` is an `O(n)`-finite function of the dual principal series of `split ds`;
* for every `f` there is an `O(n)`-finite `u` of the dual principal series of `ds` with
  `∫ u(κ g) w(κ) dκ = ∫ (L w)(κ gᵀ) f(κ) dκ` for all `w`, `g`;
* for every `w` there is an `O(n)`-finite `z` of the dual principal series of `ds` with
  `∫ z (D f) = ∫ (L w) f` and `∫ (L w)(κ g) f(κ) dκ = ∫ z(κ g) (D f)(κ) dκ` for all `f`, `g`. -/
theorem exists_splitTranspose (ds : List RealBlock) (hn : realRank ds = n)
    (T : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n ds.reverse) (unitaryCompact ℝ n))
    (hT : IsRealStandardIntertwiner n (realStandardRep n ds.reverse)
      (realStandardLie n ds.reverse) ds T) :
    ∃ D : kFiniteFunctions (realStandardModule n (split ds)) (unitaryCompact ℝ n) →ₗ[ℂ]
        kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n),
      IsRealStandardIntertwiner n (realStandardRep n ds) (realStandardLie n ds) (split ds) D ∧
      Function.Surjective D ∧
      (∀ w : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n),
        twistLin n (T w : Langlands.GeneralLinear n ℝ → ℂ) ∈ kFiniteFunctions
          (principalSeries ℝ n (dualChar (realPositionCharacter (split ds))))
          (unitaryCompact ℝ n)) ∧
      (∀ f : kFiniteFunctions (realStandardModule n (split ds)) (unitaryCompact ℝ n),
        ∃ u ∈ kFiniteFunctions (principalSeries ℝ n (dualChar (realPositionCharacter ds)))
            (unitaryCompact ℝ n),
          ∀ (w : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
            (g : Langlands.GeneralLinear n ℝ),
            ∫ κ, u ((κ : Langlands.GeneralLinear n ℝ) * g) *
                (w : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n =
              ∫ κ, twistLin n (T w : Langlands.GeneralLinear n ℝ → ℂ)
                ((κ : Langlands.GeneralLinear n ℝ) * transposeGL g) *
                (f : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n) ∧
      ∀ w : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n),
        ∃ z ∈ kFiniteFunctions (principalSeries ℝ n (dualChar (realPositionCharacter ds)))
            (unitaryCompact ℝ n),
          (∀ f : kFiniteFunctions (realStandardModule n (split ds)) (unitaryCompact ℝ n),
            ∫ κ, z (κ : Langlands.GeneralLinear n ℝ) *
                (D f : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n =
              ∫ κ, twistLin n (T w : Langlands.GeneralLinear n ℝ → ℂ)
                (κ : Langlands.GeneralLinear n ℝ) *
                (f : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n) ∧
          ∀ (f : kFiniteFunctions (realStandardModule n (split ds)) (unitaryCompact ℝ n))
            (g : Langlands.GeneralLinear n ℝ),
            ∫ κ, twistLin n (T w : Langlands.GeneralLinear n ℝ → ℂ)
                ((κ : Langlands.GeneralLinear n ℝ) * g) *
                (f : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n =
              ∫ κ, z ((κ : Langlands.GeneralLinear n ℝ) * g) *
                (D f : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n := by
  obtain ⟨D, Q, hD, hQ, hDQ, hker⟩ := exists_splitMap ds hn
  have hL : ∀ w : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n),
      twistLin n (T w : Langlands.GeneralLinear n ℝ → ℂ) ∈ kFiniteFunctions
        (principalSeries ℝ n (dualChar (realPositionCharacter (split ds))))
        (unitaryCompact ℝ n) := fun w =>
    twistLin_mem_kFiniteFunctions (dualChar_split_eq hn)
      (mem_kFiniteFunctions_principalSeries (T w).2)
  refine ⟨D, hD, fun h => ⟨Q h, hDQ h⟩, hL,
    fun f => exists_transpose_twist hn T hT (mem_kFiniteFunctions_principalSeries f.2),
    fun w => ?_⟩
  refine exists_transpose_of_section D Q hD hQ hDQ (hL w) fun f hf => ?_
  refine hker _ (continuous_of_mem (hL w)) (hL w).2 (fun p d hd j hj k _ => ?_) f hf
  exact twistLin_tail hn (T w).2.1 p d hd j hj k

end RealReverseSplit

end Langlands.Archimedean
