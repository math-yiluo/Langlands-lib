import Langlands.Representation.Shahidi.OpenCellBaseMatrix

/-! # Values of lifted functions on the open cell of the `(1, n)` parabolic

For the lift `F` of a Levi-invariant function on the Levi of the `(1, t+2)` parabolic and a
column `y = (y', c)`, the value `F(lower(y))` is expressed through the lift of a related
Levi-invariant function on `GL_(1+(t+1))` (one satisfying an explicit relation with the first)
at `lower(y'/c)` when `c ≠ 0` and `c⁻¹` is integral, and through the lift of the restricted
function at `lower(y')` when `c` is integral. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell.Base

open Langlands.GeneralLinear Langlands.Conductor Matrix Langlands.Shahidi.OpenCell

universe u

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}

local instance ocBaseLiftTopologicalSpace : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
local instance ocBaseLiftValuativeRel : ValuativeRel K.Carrier := K.canonicalTopologicalData.valuativeRel
local instance ocBaseLiftIsNonarchimedeanLocalField : IsNonarchimedeanLocalField K.Carrier := K.canonicalTopologicalData.localField

variable {t : ℕ}

theorem blk_mem {aa : K.Carrier} {am : Fin (t + 1) → K.Carrier} {al : K.Carrier}
    {ma : Fin (t + 1) → K.Carrier} {mm : Fin (t + 1) → Fin (t + 1) → K.Carrier}
    {ml : Fin (t + 1) → K.Carrier} {la : K.Carrier} {lm : Fin (t + 1) → K.Carrier}
    {ll : K.Carrier}
    (haa : aa ∈ K.canonicalTopologicalData.Integers)
    (ham : ∀ j, am j ∈ K.canonicalTopologicalData.Integers)
    (hal : al ∈ K.canonicalTopologicalData.Integers)
    (hma : ∀ j, ma j ∈ K.canonicalTopologicalData.Integers)
    (hmm : ∀ j k, mm j k ∈ K.canonicalTopologicalData.Integers)
    (hml : ∀ j, ml j ∈ K.canonicalTopologicalData.Integers)
    (hla : la ∈ K.canonicalTopologicalData.Integers)
    (hlm : ∀ j, lm j ∈ K.canonicalTopologicalData.Integers)
    (hll : ll ∈ K.canonicalTopologicalData.Integers) (i k : Fin ((0 + 1) + ((t + 1) + 1))) :
    blk t aa am al ma mm ml la lm ll i k ∈ K.canonicalTopologicalData.Integers := by
  rcases index_cases t i with rfl | ⟨j, rfl⟩ | rfl <;>
    rcases index_cases t k with rfl | ⟨k, rfl⟩ | rfl <;>
    simp only [blk_aa, blk_am, blk_al, blk_ma, blk_mm, blk_ml, blk_la, blk_lm, blk_ll]
  exacts [haa, ham _, hal, hma _, hmm _ _, hml _, hla, hlm _, hll]

theorem delta_mem (j k : Fin (t + 1)) :
    (if j = k then (1 : K.Carrier) else 0) ∈ K.canonicalTopologicalData.Integers := by
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem kkGL_mem (c : K.Carrier) (hc : c⁻¹ ∈ K.canonicalTopologicalData.Integers) :
    kkGL (t := t) c ∈ integralSubgroup K.canonicalTopologicalData.Integers (0 + 1 + (t + 1)) := by
  refine (mem_integralSubgroup _ _ _).2 ⟨fun i k => ?_, fun i k => ?_⟩
  · exact blk_mem (zero_mem _) (fun _ => zero_mem _) (neg_mem (one_mem _)) (fun _ => zero_mem _)
      delta_mem (fun _ => zero_mem _) (one_mem _) (fun _ => zero_mem _) hc i k
  · exact blk_mem hc (fun _ => zero_mem _) (one_mem _) (fun _ => zero_mem _)
      delta_mem (fun _ => zero_mem _) (neg_mem (one_mem _)) (fun _ => zero_mem _) (zero_mem _) i k

theorem lowerLastGL_mem (c : K.Carrier) (hc : c ∈ K.canonicalTopologicalData.Integers) :
    lowerLastGL (t := t) c ∈
      integralSubgroup K.canonicalTopologicalData.Integers (0 + 1 + (t + 1)) := by
  refine (mem_integralSubgroup _ _ _).2 ⟨fun i k => ?_, fun i k => ?_⟩
  · exact blk_mem (one_mem _) (fun _ => zero_mem _) (zero_mem _) (fun _ => zero_mem _)
      delta_mem (fun _ => zero_mem _) hc (fun _ => zero_mem _) (one_mem _) i k
  · exact blk_mem (one_mem _) (fun _ => zero_mem _) (zero_mem _) (fun _ => zero_mem _)
      delta_mem (fun _ => zero_mem _) (neg_mem hc) (fun _ => zero_mem _) (one_mem _) i k

theorem embed_mem (k : Langlands.GeneralLinear ((0 + 1) + (t + 1)) K.Carrier)
    (hk : k ∈ integralSubgroup K.canonicalTopologicalData.Integers (0 + 1 + t)) :
    embed k ∈ integralSubgroup K.canonicalTopologicalData.Integers (0 + 1 + (t + 1)) := by
  obtain ⟨h1, h2⟩ := (mem_integralSubgroup _ _ _).1 hk
  refine (mem_integralSubgroup _ _ _).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · rcases index_cases t i with rfl | ⟨i, rfl⟩ | rfl <;>
      rcases index_cases t j with rfl | ⟨j, rfl⟩ | rfl <;>
      simp only [embed_aa, embed_am, embed_al, embed_ma, embed_mm, embed_ml, embed_la, embed_lm,
        embed_ll]
    exacts [h1 _ _, h1 _ _, zero_mem _, h1 _ _, h1 _ _, zero_mem _, zero_mem _, zero_mem _,
      one_mem _]
  · rw [← embed_inv]
    rcases index_cases t i with rfl | ⟨i, rfl⟩ | rfl <;>
      rcases index_cases t j with rfl | ⟨j, rfl⟩ | rfl <;>
      simp only [embed_aa, embed_am, embed_al, embed_ma, embed_mm, embed_ml, embed_la, embed_lm,
        embed_ll]
    exacts [h2 _ _, h2 _ _, zero_mem _, h2 _ _, h2 _ _, zero_mem _, zero_mem _, zero_mem _,
      one_mem _]

theorem zero_fin_one (j : Fin (0 + 1)) : j = 0 := Fin.ext (by have := j.isLt; omega)

theorem castAdd_fin_one (j : Fin (0 + 1)) : j.castAdd ((t + 1) + 1) = aI t := by
  rw [zero_fin_one j]
  rfl

theorem p0GL_mem (y : Matrix (Fin ((t + 1) + 1)) (Fin 1) K.Carrier)
    (hc : y (Fin.last (t + 1)) 0 ≠ 0) :
    p0GL y hc ∈ (liftShape 0 (t + 1)).parabolic K.Carrier := by
  rw [twoBlocks_mem_parabolic_iff]
  intro i j
  rw [castAdd_fin_one]
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · change p0Mat y (lI t) (aI t) = 0
    simp [p0Mat]
  · change p0Mat y (mI t i') (aI t) = 0
    simp [p0Mat]

theorem embed_mem_parabolic (g : Langlands.GeneralLinear ((0 + 1) + (t + 1)) K.Carrier)
    (hg : g ∈ (liftShape 0 t).parabolic K.Carrier) :
    embed g ∈ (liftShape 0 (t + 1)).parabolic K.Carrier := by
  rw [twoBlocks_mem_parabolic_iff] at hg ⊢
  intro i j
  rw [castAdd_fin_one]
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · exact embed_la g
  · change embed g (mI t i') (aI t) = 0
    rw [embed_ma]
    have := hg i' 0
    rwa [show (0 : Fin (0 + 1)).castAdd (t + 1) = Fin.castAdd (t + 1) 0 from rfl] at this

/-- The scalar matrix `x · I` in `GL_n`. -/
def scalarGL {n : ℕ} (x : K.Carrierˣ) : Langlands.GeneralLinear n K.Carrier :=
  Iwasawa.diagonalUnits (fun _ => x)

theorem liftFirst_p0GL (y : Matrix (Fin ((t + 1) + 1)) (Fin 1) K.Carrier)
    (hc : y (Fin.last (t + 1)) 0 ≠ 0) :
    liftFirst K 0 (t + 1) ⟨p0GL y hc, p0GL_mem y hc⟩ = scalarGL (Units.mk0 _ hc)⁻¹ := by
  apply Units.ext
  funext a b
  rw [liftFirst_apply, zero_fin_one a, zero_fin_one b, castAdd_fin_one]
  change p0Mat y (aI t) (aI t) = _
  simp [p0Mat, scalarGL]

theorem liftFirst_embed (g : Langlands.GeneralLinear ((0 + 1) + (t + 1)) K.Carrier)
    (hg : g ∈ (liftShape 0 t).parabolic K.Carrier) :
    liftFirst K 0 (t + 1) ⟨embed g, embed_mem_parabolic g hg⟩ = liftFirst K 0 t ⟨g, hg⟩ := by
  apply Units.ext
  funext a b
  rw [liftFirst_apply, liftFirst_apply, zero_fin_one a, zero_fin_one b, castAdd_fin_one]
  exact embed_aa g

theorem liftSecond_embed (g : Langlands.GeneralLinear ((0 + 1) + (t + 1)) K.Carrier)
    (hg : g ∈ (liftShape 0 t).parabolic K.Carrier) :
    liftSecond K 0 (t + 1) ⟨embed g, embed_mem_parabolic g hg⟩ =
      GeneralLinear.blockSum (n := t + 1) (m := 1) (liftSecond K 0 t ⟨g, hg⟩, 1) := by
  apply Units.ext
  ext a b
  rw [liftSecond_apply]
  refine Fin.lastCases ?_ (fun a' => ?_) a <;> refine Fin.lastCases ?_ (fun b' => ?_) b
  · change embed g (lI t) (lI t) = _
    rw [embed_ll, show Fin.last (t + 1) = Fin.natAdd (t + 1) (0 : Fin 1) from rfl,
      blockSum_apply_right]
    rfl
  · change embed g (lI t) (mI t b') = _
    rw [embed_lm, show Fin.last (t + 1) = Fin.natAdd (t + 1) (0 : Fin 1) from rfl,
      show b'.castSucc = Fin.castAdd 1 b' from rfl, blockSum_apply_right_left]
  · change embed g (mI t a') (lI t) = _
    rw [embed_ml, show Fin.last (t + 1) = Fin.natAdd (t + 1) (0 : Fin 1) from rfl,
      show a'.castSucc = Fin.castAdd 1 a' from rfl, blockSum_apply_left_right]
  · change embed g (mI t a') (mI t b') = _
    rw [embed_mm, show a'.castSucc = Fin.castAdd 1 a' from rfl,
      show b'.castSucc = Fin.castAdd 1 b' from rfl, blockSum_apply_left, liftSecond_apply]

/-- The column `y'/c`. -/
def quotCol (y : Matrix (Fin ((t + 1) + 1)) (Fin 1) K.Carrier) : Matrix (Fin (t + 1)) (Fin 1) K.Carrier :=
  Matrix.of fun j _ => y j.castSucc 0 * (y (Fin.last (t + 1)) 0)⁻¹

theorem liftSecond_p0GL (y : Matrix (Fin ((t + 1) + 1)) (Fin 1) K.Carrier)
    (hc : y (Fin.last (t + 1)) 0 ≠ 0) :
    liftSecond K 0 (t + 1) ⟨p0GL y hc, p0GL_mem y hc⟩ =
      upper (t + 1) 1 K.Carrier (quotCol y) *
        GeneralLinear.blockSum (n := t + 1) (m := 1) (1, scalarGL (Units.mk0 _ hc)) := by
  apply Units.ext
  ext a b
  rw [liftSecond_apply, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_castSucc]
  have hl : Fin.last (t + 1) = Fin.natAdd (t + 1) (0 : Fin 1) := rfl
  have hcs : ∀ j : Fin (t + 1), j.castSucc = Fin.castAdd 1 j := fun _ => rfl
  refine Fin.lastCases ?_ (fun a' => ?_) a <;> refine Fin.lastCases ?_ (fun b' => ?_) b
  · change p0Mat y (lI t) (lI t) = _
    simp only [p0Mat, blk_ll, hcs, hl, upper_second_first, upper_second_second,
      blockSum_apply_left_right, blockSum_apply_right, zero_mul, Finset.sum_const_zero, zero_add]
    simp [scalarGL]
  · change p0Mat y (lI t) (mI t b') = _
    simp only [p0Mat, blk_lm, hcs, hl, upper_second_first, upper_second_second,
      blockSum_apply_left, blockSum_apply_right_left]
    simp [Matrix.one_apply]
  · change p0Mat y (mI t a') (lI t) = _
    simp only [p0Mat, blk_ml, hcs, hl, upper_first_first, upper_first_second,
      blockSum_apply_left_right, blockSum_apply_right, mul_zero, Finset.sum_const_zero, zero_add]
    simp only [scalarGL, quotCol, Iwasawa.diagonalUnits_val, Matrix.diagonal_apply_eq,
      Units.val_mk0, Matrix.of_apply]
    rw [← hcs, ← hl, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  · change p0Mat y (mI t a') (mI t b') = _
    simp only [p0Mat, blk_mm, hcs, hl, upper_first_first, upper_first_second,
      blockSum_apply_left, blockSum_apply_right_left, mul_zero, add_zero]
    simp [Matrix.one_apply]

theorem blockSum_one_mem {n : ℕ} (μ : Langlands.GeneralLinear (n + 1) K.Carrier)
    (hμ : μ ∈ integralSubgroup K.canonicalTopologicalData.Integers n) :
    GeneralLinear.blockSum (n := n + 1) (m := 1) (μ, 1) ∈
      integralSubgroup K.canonicalTopologicalData.Integers (n + 1) := by
  obtain ⟨h1, h2⟩ := (mem_integralSubgroup _ _ _).1 hμ
  refine (mem_integralSubgroup _ _ _).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i <;>
      refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
    · rw [blockSum_apply_left]; exact h1 _ _
    · rw [blockSum_apply_left_right]; exact zero_mem _
    · rw [blockSum_apply_right_left]; exact zero_mem _
    · rw [blockSum_apply_right, Subsingleton.elim i' j', Units.val_one, Matrix.one_apply_eq]
      exact one_mem _
  · rw [← map_inv, Prod.inv_mk, inv_one]
    refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i <;>
      refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
    · rw [blockSum_apply_left]; exact h2 _ _
    · rw [blockSum_apply_left_right]; exact zero_mem _
    · rw [blockSum_apply_right_left]; exact zero_mem _
    · rw [blockSum_apply_right, Subsingleton.elim i' j', Units.val_one, Matrix.one_apply_eq]
      exact one_mem _

section Values

variable {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
    (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)

/-- **Value at `lower(y)` when the last entry `c` has integral inverse.** -/
theorem liftFunction_lower_of_inv_mem
    {Φ : Langlands.GeneralLinear (0 + 1) K.Carrier → Langlands.GeneralLinear ((t + 1) + 1) K.Carrier → ℂ}
    {Φ' : Langlands.GeneralLinear (0 + 1) K.Carrier → Langlands.GeneralLinear (t + 1) K.Carrier → ℂ}
    (hΦ : IsLeviInvariant Φ) (hΦ' : IsLeviInvariant Φ')
    (y : Matrix (Fin ((t + 1) + 1)) (Fin 1) K.Carrier) (hc : y (Fin.last (t + 1)) 0 ≠ 0)
    (hcI : (y (Fin.last (t + 1)) 0)⁻¹ ∈ K.canonicalTopologicalData.Integers) (χ : ℂ)
    (hrel : ∀ m₁ m₂, Φ (scalarGL (Units.mk0 _ hc)⁻¹ * m₁)
      (upper (t + 1) 1 K.Carrier (quotCol y) *
        GeneralLinear.blockSum (n := t + 1) (m := 1) (1, scalarGL (Units.mk0 _ hc)) *
        GeneralLinear.blockSum (n := t + 1) (m := 1) (m₂, 1)) = χ * Φ' m₁ m₂) :
    liftFunction hϖ Φ (lower (0 + 1) ((t + 1) + 1) K.Carrier y) =
      χ * liftFunction hϖ Φ' (lower (0 + 1) (t + 1) K.Carrier (quotCol y)) := by
  obtain ⟨g', hg', k', hk', hdec⟩ := exists_liftShape_parabolic_mul 0 t hϖ
    (lower (0 + 1) (t + 1) K.Carrier (quotCol y))
  have e : lower (0 + 1) ((t + 1) + 1) K.Carrier y =
      ((⟨p0GL y hc, p0GL_mem y hc⟩ * ⟨embed g', embed_mem_parabolic g' hg'⟩ :
        (liftShape 0 (t + 1)).parabolic K.Carrier) : Langlands.GeneralLinear _ K.Carrier) *
        (embed k' * kkGL (y (Fin.last (t + 1)) 0)) := by
    rw [lower_eq_p0GL_mul y hc]
    change _ = p0GL y hc * embed g' * (embed k' * kkGL (y (Fin.last (t + 1)) 0))
    have hq : (Matrix.of fun j (_ : Fin 1) => y j.castSucc 0 * (y (Fin.last (t + 1)) 0)⁻¹) =
        quotCol y := rfl
    rw [hq, hdec, embed_mul]
    group
  rw [e, liftFunction_parabolic_mul hϖ hΦ _ _ (mul_mem (embed_mem k' hk') (kkGL_mem _ hcI)),
    liftFirst_mul, liftSecond_mul, liftFirst_p0GL, liftSecond_p0GL, liftFirst_embed,
    liftSecond_embed, hrel, hdec, liftFunction_parabolic_mul hϖ hΦ' ⟨g', hg'⟩ k' hk']

/-- The column `y'` of the first `t + 1` entries. -/
def headCol (y : Matrix (Fin ((t + 1) + 1)) (Fin 1) K.Carrier) : Matrix (Fin (t + 1)) (Fin 1) K.Carrier :=
  Matrix.of fun j _ => y j.castSucc 0

theorem isLeviInvariant_restrict
    {Φ : Langlands.GeneralLinear (0 + 1) K.Carrier → Langlands.GeneralLinear ((t + 1) + 1) K.Carrier → ℂ}
    (hΦ : IsLeviInvariant Φ) :
    IsLeviInvariant (fun (m₁ : Langlands.GeneralLinear (0 + 1) K.Carrier)
      (m₂ : Langlands.GeneralLinear (t + 1) K.Carrier) =>
        Φ m₁ (GeneralLinear.blockSum (n := t + 1) (m := 1) (m₂, 1))) := by
  intro m₁ μ₁ m₂ μ₂ hμ₁ hμ₂
  have e : GeneralLinear.blockSum (n := t + 1) (m := 1) (m₂ * μ₂, 1) =
      GeneralLinear.blockSum (n := t + 1) (m := 1) (m₂, 1) *
        GeneralLinear.blockSum (n := t + 1) (m := 1) (μ₂, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  simp only
  rw [e, hΦ _ _ _ _ hμ₁ (blockSum_one_mem μ₂ hμ₂)]

/-- **Value at `lower(y)` when the last entry is integral.** -/
theorem liftFunction_lower_of_mem
    {Φ : Langlands.GeneralLinear (0 + 1) K.Carrier → Langlands.GeneralLinear ((t + 1) + 1) K.Carrier → ℂ}
    (hΦ : IsLeviInvariant Φ)
    (y : Matrix (Fin ((t + 1) + 1)) (Fin 1) K.Carrier)
    (hcI : y (Fin.last (t + 1)) 0 ∈ K.canonicalTopologicalData.Integers) :
    liftFunction hϖ Φ (lower (0 + 1) ((t + 1) + 1) K.Carrier y) =
      liftFunction hϖ (fun m₁ m₂ => Φ m₁ (GeneralLinear.blockSum (n := t + 1) (m := 1) (m₂, 1)))
        (lower (0 + 1) (t + 1) K.Carrier (headCol y)) := by
  obtain ⟨g', hg', k', hk', hdec⟩ := exists_liftShape_parabolic_mul 0 t hϖ
    (lower (0 + 1) (t + 1) K.Carrier (headCol y))
  have e : lower (0 + 1) ((t + 1) + 1) K.Carrier y =
      ((⟨embed g', embed_mem_parabolic g' hg'⟩ : (liftShape 0 (t + 1)).parabolic K.Carrier) :
        Langlands.GeneralLinear _ K.Carrier) *
        (embed k' * lowerLastGL (y (Fin.last (t + 1)) 0)) := by
    rw [lower_eq_embed_mul y]
    change embed (lower (0 + 1) (t + 1) K.Carrier (headCol y)) * _ = _
    rw [hdec, embed_mul, mul_assoc]
  rw [e, liftFunction_parabolic_mul hϖ hΦ _ _ (mul_mem (embed_mem k' hk') (lowerLastGL_mem _ hcI)),
    liftFirst_embed, liftSecond_embed, hdec,
    liftFunction_parabolic_mul hϖ (isLeviInvariant_restrict hΦ) ⟨g', hg'⟩ k' hk']

end Values

end Langlands.Shahidi.OpenCell.Base
