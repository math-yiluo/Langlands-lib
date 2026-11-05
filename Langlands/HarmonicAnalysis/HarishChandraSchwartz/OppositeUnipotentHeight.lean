import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OppositeUnipotentDisplacement
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Heights on opposite unipotent points bounded by a weight-vector displacement -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open Langlands.GroupScheme.GeneralLinear
open scoped CategoryTheory.MonObj

namespace Langlands.HarishChandraSchwartz

section WeightBlock

variable {F : Type*} [NormedField F] {n : Type} [Fintype n] [DecidableEq n]

/-- An eigenvector of `diag(t ^ e i)` with `‖t‖ ≠ 1` is supported on one weight block. -/
theorem exists_weight_block_of_mulVec_eq_smul {e : n → ℤ} {t : Fˣ} (ht : ‖(t : F)‖ ≠ 1)
    {w : n → F} {c : F} (h : (diagonalUnits F e t : Matrix n n F) *ᵥ w = c • w) :
    ∃ m : ℤ, ∀ k, e k ≠ m → w k = 0 := by
  by_cases hex : ∃ k₀, w k₀ ≠ 0
  · obtain ⟨k₀, hk₀⟩ := hex
    refine ⟨e k₀, fun k hk => ?_⟩
    by_contra hwk
    have hcomp : ∀ k, ((t ^ e k : Fˣ) : F) * w k = c * w k := fun k => by
      have h' := congrFun h k
      rwa [coe_diagonalUnits, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h'
    have h1 : ((t ^ e k : Fˣ) : F) = c := mul_right_cancel₀ hwk (hcomp k)
    have h2 : ((t ^ e k₀ : Fˣ) : F) = c := mul_right_cancel₀ hk₀ (hcomp k₀)
    have h3 : ‖(t : F)‖ ^ e k = ‖(t : F)‖ ^ e k₀ := by
      rw [← norm_zpow, ← norm_zpow, ← Units.val_zpow_eq_zpow_val, ← Units.val_zpow_eq_zpow_val,
        h1, h2]
    exact hk (zpow_right_injective₀ (norm_pos_iff.2 t.ne_zero) ht h3)
  · simp only [not_exists, not_not] at hex
    exact ⟨0, fun k _ => hex k⟩

omit [DecidableEq n] in
/-- A square matrix acts boundedly on vectors in the sup norm. -/
theorem exists_norm_mulVec_le [IsUltrametricDist F] (A : Matrix n n F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : n → F, ‖A *ᵥ y‖ ≤ K * ‖y‖ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · refine ⟨0, le_rfl, fun y => ?_⟩
    rw [Subsingleton.elim (A *ᵥ y) 0, norm_zero, zero_mul]
  · exact ⟨entryNorm A, entryNorm_nonneg _, norm_mulVec_le A⟩

end WeightBlock

end Langlands.HarishChandraSchwartz

namespace Langlands.GroupScheme.MatrixRepresentation

section Conjugation

variable {F : Type u} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The matrix of `g` intertwines `ρ` with the conjugate representation `ρ ≫ Int(g)`. -/
theorem rationalMatrix_comp_innerIso_mulVec (ρ : MatrixRepresentation G n)
    (g : rationalPoints (groupScheme n (CommRingCat.of F))) (x : rationalPoints G) (v : n → F) :
    (rationalMatrix (ρ ≫ ((groupScheme n (CommRingCat.of F)).innerIso g).hom) x :
        Matrix n n F) *ᵥ
        ((rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) g : Matrix n n F) *ᵥ v) =
      (rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) g : Matrix n n F) *ᵥ
        ((ρ.rationalMatrix x : Matrix n n F) *ᵥ v) := by
  rw [rationalMatrix_comp_innerIso]
  simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_right]

/-- `ρ(x)` is the conjugate of the rational matrix of `ρ ≫ Int(g)` back by `g`. -/
theorem rationalMatrix_eq_conj_comp_innerIso (ρ : MatrixRepresentation G n)
    (g : rationalPoints (groupScheme n (CommRingCat.of F))) (x : rationalPoints G) :
    ρ.rationalMatrix x =
      (rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) g)⁻¹ *
        rationalMatrix (ρ ≫ ((groupScheme n (CommRingCat.of F)).innerIso g).hom) x *
        rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) g := by
  rw [rationalMatrix_comp_innerIso]
  group

/-- `v` is an eigenvector of `ρ(χ(t))` for every `t ∈ Fˣ`, where `χ` is a cocharacter of `G`
and `ρ(χ(t))` is the rational matrix of the rational point `χ(t)`. -/
def IsCocharacterEigenvector (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (ρ : MatrixRepresentation G n) (v : n → F) : Prop :=
  ∀ t : Fˣ, ∃ c : F,
    (ρ.rationalMatrix (gmRationalPoint t ≫ χ.hom.hom) : Matrix n n F) *ᵥ v = c • v

end Conjugation

section LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]

/-- **Heights on opposite unipotent points.** Let `χ` be a cocharacter of `G`, `ρ₀` a closed
representation and `ρ` a representation of `G`. Let `v` be an eigenvector of every
`ρ(χ(t))` (`IsCocharacterEigenvector`), and assume that the only point of
`Ū(F) = U(χ⁻¹)(F)` fixing `v` is `1`. Then the `ρ₀`-height of `x ∈ Ū(F)` is at most a
constant times a power of `max 1 ‖ρ(x) v‖`. -/
theorem exists_rationalMatrixNorm_le_of_weightVector
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    {N : ℕ} [Nonempty (Fin N)] (ρ₀ : MatrixRepresentation G (Fin N)) (hρ₀ : IsClosedSubgroup ρ₀)
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n) {v : n → F}
    (hv : IsCocharacterEigenvector χ ρ v)
    (hfix : ∀ x ∈ (Dynamic.unipotent (CommGroupScheme.groupHom
        (Gm.powerHom (Spec (CommRingCat.of F)) (-1)) ≫ χ)).rationalPoints,
      (ρ.rationalMatrix x : Matrix n n F) *ᵥ v = v → x = 1) :
    ∃ C : ℝ, ∃ D : ℕ, 0 < C ∧ ∀ x ∈ (Dynamic.unipotent (CommGroupScheme.groupHom
        (Gm.powerHom (Spec (CommRingCat.of F)) (-1)) ≫ χ)).rationalPoints,
      rationalMatrixNorm F ρ₀ x ≤
        C * max 1 (rationalVectorNorm F ((ρ.rationalMatrix x : Matrix n n F) *ᵥ v)) ^ D := by
  obtain ⟨g₀, e₀, hg₀⟩ := exists_innerIso_comp_eq_diagonalCocharacter F (χ ≫ ρ₀)
  obtain ⟨g, e, hg⟩ := exists_innerIso_comp_eq_diagonalCocharacter F (χ ≫ ρ)
  have hcl : IsClosedSubgroup
      (ρ₀ ≫ ((groupScheme (Fin N) (CommRingCat.of F)).innerIso g₀).hom) :=
    hρ₀.comp_iso _
  have hχ₀ : χ ≫ ρ₀ ≫ ((groupScheme (Fin N) (CommRingCat.of F)).innerIso g₀).hom =
      diagonalCocharacter (Fin N) (CommRingCat.of F) e₀ := by
    rw [← Category.assoc, hg₀]
  have hχ : χ ≫ ρ ≫ ((groupScheme n (CommRingCat.of F)).innerIso g).hom =
      diagonalCocharacter n (CommRingCat.of F) e := by
    rw [← Category.assoc, hg]
  have hfix' : ∀ x ∈ (Dynamic.unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of F)) (-1)) ≫ χ)).rationalPoints,
      (rationalMatrix (ρ ≫ ((groupScheme n (CommRingCat.of F)).innerIso g).hom) x :
          Matrix n n F) *ᵥ
          ((rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) g : Matrix n n F) *ᵥ v) =
        (rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) g : Matrix n n F) *ᵥ v →
      x = 1 := by
    intro x hx h
    rw [rationalMatrix_comp_innerIso_mulVec] at h
    exact hfix x hx (Matrix.mulVec_injective_of_isUnit (Units.isUnit _) h)
  let t : Fˣ := Units.mk0 (LocalField.uniformizer F) (LocalField.uniformizer_ne_zero F)
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  have : IsUltrametricDist F :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (LocalField.residueNormalizedAbsoluteValue_add_le_max F)
  have hq1 : (1 : ℝ) < (LocalField.residueCardinality F : ℝ) := by
    exact_mod_cast LocalField.residueCardinality_gt_one F
  have ht : ‖(t : F)‖ ≠ 1 := by
    have htn : ‖(t : F)‖ = (LocalField.residueCardinality F : ℝ)⁻¹ :=
      LocalField.residueNormalizedAbsoluteValue_of_ord_one F (LocalField.ord_uniformizer F)
    rw [htn]
    exact (inv_lt_one_of_one_lt₀ hq1).ne
  obtain ⟨c, hc⟩ := hv t
  have hdiag : (diagonalUnits F e t : Matrix n n F) *ᵥ
      ((rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) g : Matrix n n F) *ᵥ v) =
      c • ((rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) g : Matrix n n F) *ᵥ v) := by
    rw [← rationalMatrix_gmRationalPoint_comp hχ t, rationalMatrix_comp_innerIso_mulVec, hc,
      Matrix.mulVec_smul]
  obtain ⟨m, hwm⟩ := HarishChandraSchwartz.exists_weight_block_of_mulVec_eq_smul ht hdiag
  obtain ⟨C, D, hC, hb⟩ :=
    exists_rationalMatrixNorm_le_of_diagonal F χ _ hcl hχ₀ _ hχ hwm hfix'
  obtain ⟨K, hK, hKb⟩ := HarishChandraSchwartz.exists_norm_mulVec_le
    (rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) g : Matrix n n F)
  have hM₀ : 0 < HarishChandraSchwartz.glNorm
      (rationalMatrix (𝟙 (groupScheme (Fin N) (CommRingCat.of F))) g₀) :=
    zero_lt_one.trans_le (HarishChandraSchwartz.one_le_glNorm _)
  have hK1 : 0 < max 1 K := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨HarishChandraSchwartz.glNorm
      (rationalMatrix (𝟙 (groupScheme (Fin N) (CommRingCat.of F))) g₀) ^ 2 * C * max 1 K ^ D,
    D, mul_pos (mul_pos (pow_pos hM₀ 2) hC) (pow_pos hK1 D), fun x hx => ?_⟩
  have h1 : rationalMatrixNorm F ρ₀ x ≤
      HarishChandraSchwartz.glNorm
          (rationalMatrix (𝟙 (groupScheme (Fin N) (CommRingCat.of F))) g₀) ^ 2 *
        rationalMatrixNorm F
          (ρ₀ ≫ ((groupScheme (Fin N) (CommRingCat.of F)).innerIso g₀).hom) x := by
    change HarishChandraSchwartz.glNorm (ρ₀.rationalMatrix x) ≤
      HarishChandraSchwartz.glNorm
          (rationalMatrix (𝟙 (groupScheme (Fin N) (CommRingCat.of F))) g₀) ^ 2 *
        HarishChandraSchwartz.glNorm (rationalMatrix
          (ρ₀ ≫ ((groupScheme (Fin N) (CommRingCat.of F)).innerIso g₀).hom) x)
    rw [rationalMatrix_eq_conj_comp_innerIso ρ₀ g₀ x]
    refine (HarishChandraSchwartz.glNorm_mul_le _ _).trans ?_
    refine (mul_le_mul_of_nonneg_right (HarishChandraSchwartz.glNorm_mul_le _ _)
      (HarishChandraSchwartz.glNorm_nonneg _)).trans_eq ?_
    rw [HarishChandraSchwartz.glNorm_inv]
    ring
  have h2 : max 1 (rationalVectorNorm F
        ((rationalMatrix (ρ ≫ ((groupScheme n (CommRingCat.of F)).innerIso g).hom) x :
            Matrix n n F) *ᵥ
          ((rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) g : Matrix n n F) *ᵥ v))) ≤
      max 1 K * max 1 (rationalVectorNorm F ((ρ.rationalMatrix x : Matrix n n F) *ᵥ v)) := by
    change max 1 ‖(rationalMatrix (ρ ≫ ((groupScheme n (CommRingCat.of F)).innerIso g).hom) x :
            Matrix n n F) *ᵥ
          ((rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) g : Matrix n n F) *ᵥ v)‖ ≤
      max 1 K * max 1 ‖(ρ.rationalMatrix x : Matrix n n F) *ᵥ v‖
    rw [rationalMatrix_comp_innerIso_mulVec]
    refine max_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)) ?_
    exact (hKb _).trans (mul_le_mul (le_max_right _ _) (le_max_right _ _) (norm_nonneg _)
      hK1.le)
  calc rationalMatrixNorm F ρ₀ x
      ≤ HarishChandraSchwartz.glNorm
          (rationalMatrix (𝟙 (groupScheme (Fin N) (CommRingCat.of F))) g₀) ^ 2 *
        rationalMatrixNorm F
          (ρ₀ ≫ ((groupScheme (Fin N) (CommRingCat.of F)).innerIso g₀).hom) x := h1
    _ ≤ HarishChandraSchwartz.glNorm
          (rationalMatrix (𝟙 (groupScheme (Fin N) (CommRingCat.of F))) g₀) ^ 2 *
        (C * (max 1 K *
          max 1 (rationalVectorNorm F ((ρ.rationalMatrix x : Matrix n n F) *ᵥ v))) ^ D) := by
      refine mul_le_mul_of_nonneg_left ((hb x hx).trans ?_) (pow_pos hM₀ 2).le
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) h2 D) hC.le
    _ = HarishChandraSchwartz.glNorm
          (rationalMatrix (𝟙 (groupScheme (Fin N) (CommRingCat.of F))) g₀) ^ 2 * C *
          max 1 K ^ D *
        max 1 (rationalVectorNorm F ((ρ.rationalMatrix x : Matrix n n F) *ᵥ v)) ^ D := by
      rw [mul_pow]
      ring

end LocalField

end Langlands.GroupScheme.MatrixRepresentation
