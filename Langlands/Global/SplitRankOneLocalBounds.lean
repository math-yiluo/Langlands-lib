import Langlands.Global.SplitRankOneFieldPoints

/-! # Local bounds for the binary form and its rational orbit points

Norm bounds for the binary form `ν(x) = Σ_{l ≤ m} x₀^(m-l) x₁^l w_l` over a normed field
(ultrametric and general), compatibility of the binary form with ring homomorphisms, and
the rational points of `G` carrying `e_j` to a multiple of `ν(r)` for every nonzero
rational `r`. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry Finset
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.Global.SplitRankOne

open Langlands.GroupScheme
open Langlands.GroupScheme.MatrixRepresentation

section Map

variable {K L : Type*} [Field K] [Field L] {n : Type*}

/-- The binary form commutes with ring homomorphisms applied coordinatewise. -/
theorem map_binaryForm (f : K →+* L) (m : ℕ) (w : ℕ → n → K) (X Y : K) :
    (fun a => f (binaryForm m w X Y a)) = binaryForm m (fun l a => f (w l a)) (f X) (f Y) := by
  funext a
  simp only [binaryForm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
    map_pow]

theorem map_nu (f : K →+* L) (m : ℕ) (w : ℕ → n → K) (x : Fin 2 → K) :
    (fun a => f (nu m w x a)) = nu m (fun l a => f (w l a)) (fun b => f (x b)) :=
  map_binaryForm f m w (x 0) (x 1)

end Map

section Norms

variable {K : Type*} [NormedField K] {n : Type*} [Fintype n]

theorem norm_binaryForm_term_le (m : ℕ) (w : ℕ → n → K) {B : ℝ}
    (hw : ∀ l ≤ m, ‖w l‖ ≤ B) (x : Fin 2 → K) {l : ℕ} (hl : l ∈ range (m + 1)) :
    ‖(x 0 ^ (m - l) * x 1 ^ l) • w l‖ ≤ B * ‖x‖ ^ m := by
  have hl' : l ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hl)
  rw [norm_smul, norm_mul, norm_pow, norm_pow]
  have h0 : ‖x 0‖ ≤ ‖x‖ := norm_le_pi_norm x 0
  have h1 : ‖x 1‖ ≤ ‖x‖ := norm_le_pi_norm x 1
  calc ‖x 0‖ ^ (m - l) * ‖x 1‖ ^ l * ‖w l‖ ≤ ‖x‖ ^ (m - l) * ‖x‖ ^ l * B := by
        gcongr
        exact hw l hl'
    _ = B * ‖x‖ ^ m := by rw [← pow_add, Nat.sub_add_cancel hl', mul_comm]

/-- Ultrametric bound for the binary form. -/
theorem norm_nu_le_ultra [IsUltrametricDist K] (m : ℕ) (w : ℕ → n → K) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ l ≤ m, ‖w l‖ ≤ B) (x : Fin 2 → K) :
    ‖nu m w x‖ ≤ B * ‖x‖ ^ m := by
  rw [nu, binaryForm]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg hB (pow_nonneg (norm_nonneg _) _))
    fun l hl => norm_binaryForm_term_le m w hw x hl

/-- Archimedean bound for the binary form. -/
theorem norm_nu_le (m : ℕ) (w : ℕ → n → K) {B : ℝ}
    (hw : ∀ l ≤ m, ‖w l‖ ≤ B) (x : Fin 2 → K) :
    ‖nu m w x‖ ≤ ((m + 1) * B) * ‖x‖ ^ m := by
  rw [nu, binaryForm]
  calc ‖∑ l ∈ range (m + 1), (x 0 ^ (m - l) * x 1 ^ l) • w l‖
      ≤ ∑ l ∈ range (m + 1), ‖(x 0 ^ (m - l) * x 1 ^ l) • w l‖ := norm_sum_le _ _
    _ ≤ ∑ _l ∈ range (m + 1), B * ‖x‖ ^ m :=
        sum_le_sum fun l hl => norm_binaryForm_term_le m w hw x hl
    _ = ((m + 1) * B) * ‖x‖ ^ m := by
        rw [sum_const, card_range, nsmul_eq_mul]
        push_cast
        ring

/-- An ultrametric matrix with integral entries does not increase the maximum norm. -/
theorem norm_mulVec_le_of_norm_le_one [IsUltrametricDist K] (M : Matrix n n K)
    (hM : ∀ a b, ‖M a b‖ ≤ 1) (u : n → K) : ‖M *ᵥ u‖ ≤ ‖u‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun a => ?_
  change ‖∑ b, M a b * u b‖ ≤ _
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun b _ => ?_
  rw [norm_mul]
  calc ‖M a b‖ * ‖u b‖ ≤ 1 * ‖u‖ :=
        mul_le_mul (hM a b) (norm_le_pi_norm u b) (norm_nonneg _) zero_le_one
    _ = ‖u‖ := one_mul _

end Norms

section Rational

variable {F : Type u} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {n : Type} [Fintype n] [DecidableEq n]
  {ρ : MatrixRepresentation G n} {j : n} {i : T.toGrp ⟶ G} {α : characterLattice T}

/-- **Rational orbit points.** For every nonzero rational `r`, the binary-form value `ν(r)`
is a nonzero multiple of the image of `e_j` under a rational point of `G`: a lowering point
if `r₀ ≠ 0`, and a raising point times a lowering point otherwise. -/
theorem CellData.exists_rational_orbit [Infinite F] (D : CellData ρ j i α) (r : Fin 2 → F)
    (hr : r ≠ 0) :
    ∃ (q : G.affinePoints (CommAlgCat.of F F)) (c : F), c ≠ 0 ∧
      nu D.k (wvec ρ j D.xm F) r =
        c • ((ρ.affineMatrix (CommAlgCat.of F F) q : Matrix n n F) *ᵥ
          (Pi.single j (1 : F) : n → F)) := by
  have hcurve := D.hyp.lowerMat_mulVec_single F
  by_cases h0 : r 0 = 0
  · have h1 : r 1 ≠ 0 := by
      intro h1
      apply hr
      funext a
      fin_cases a
      · exact h0
      · exact h1
    refine ⟨(gaPoint (CommAlgCat.of F F) (-1) ≫ D.xp.hom.hom) *
      (gaPoint (CommAlgCat.of F F) 1 ≫ D.xm.hom.hom), r 1 ^ D.k, pow_ne_zero _ h1, ?_⟩
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← affineMatrix_restrict,
      ← affineMatrix_restrict, ← raiseMat_eq, ← lowerMat_eq, hcurve,
      raising_mulVec_binaryForm D.k _ (lowerMat ρ D.xm F) (raiseMat ρ D.xp F) _ hcurve
        (fun s t hst => D.hyp.relation_nat F s t hst), nu, h0, ← binaryForm_smul]
    congr 1 <;> ring
  · refine ⟨gaPoint (CommAlgCat.of F F) (r 1 / r 0) ≫ D.xm.hom.hom, r 0 ^ D.k,
      pow_ne_zero _ h0, ?_⟩
    rw [← affineMatrix_restrict, ← lowerMat_eq, hcurve, nu, ← binaryForm_smul]
    congr 1
    · ring
    · field_simp

end Rational

end Langlands.Global.SplitRankOne
