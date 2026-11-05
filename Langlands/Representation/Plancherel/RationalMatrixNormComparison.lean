import Langlands.Representation.Plancherel.RationalMatrixNormComparisonStatement
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Langlands.GroupScheme.GeneralLinearPointTopology

/-! # Polynomial comparison of rational matrix norms -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.Plancherel

universe u uσ

/-- A polynomial has a uniform power bound when every variable is bounded
by the same real number greater than or equal to one. -/
theorem polynomial_evaluation_power_bound {F : Type u} [NormedField F]
    {σ : Type uσ} (p : MvPolynomial σ F) :
    ∃ (d : ℕ) (c : ℝ), 0 < c ∧
      ∀ (x : σ → F) (t : ℝ), 1 ≤ t → (∀ i, ‖x i‖ ≤ t) →
        ‖MvPolynomial.aeval x p‖ ≤ c * t ^ d := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      refine ⟨0, ‖a‖ + 1, by positivity, ?_⟩
      intro x t ht hx
      simp only [MvPolynomial.aeval_C, Algebra.algebraMap_self_apply, pow_zero, mul_one]
      linarith
  | add p q hp hq =>
      obtain ⟨d, c, hc, hp⟩ := hp
      obtain ⟨e, b, hb, hq⟩ := hq
      refine ⟨d + e, c + b, add_pos hc hb, ?_⟩
      intro x t ht hx
      calc
        ‖MvPolynomial.aeval x (p + q)‖ ≤
            ‖MvPolynomial.aeval x p‖ + ‖MvPolynomial.aeval x q‖ := by
              rw [map_add]
              exact norm_add_le _ _
        _ ≤ c * t ^ d + b * t ^ e := add_le_add (hp x t ht hx) (hq x t ht hx)
        _ ≤ c * t ^ (d + e) + b * t ^ (d + e) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (Nat.le_add_right d e)) hc.le)
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (Nat.le_add_left e d)) hb.le)
        _ = (c + b) * t ^ (d + e) := by ring
  | mul_X p i hp =>
      obtain ⟨d, c, hc, hp⟩ := hp
      refine ⟨d + 1, c, hc, ?_⟩
      intro x t ht hx
      calc
        ‖MvPolynomial.aeval x (p * MvPolynomial.X i)‖ =
            ‖MvPolynomial.aeval x p‖ * ‖x i‖ := by
              rw [map_mul, MvPolynomial.aeval_X, norm_mul]
        _ ≤ (c * t ^ d) * t :=
          mul_le_mul (hp x t ht hx) (hx i) (norm_nonneg _) (by positivity)
        _ = c * t ^ (d + 1) := by rw [pow_succ]; ring

set_option backward.isDefEq.respectTransparency false

open GroupScheme MatrixRepresentation
open Langlands.AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Identity-test matrices agree with affine-test matrices under the canonical
identity of the underlying spectrum points. -/
theorem rationalMatrix_eq_affineMatrix (ρ : MatrixRepresentation G n)
    (g : rationalPoints G) :
    ρ.rationalMatrix g = ρ.affineMatrix (CommAlgCat.of F F)
      (rationalPointEquiv F G.X g) := by
  apply Units.ext
  ext i j
  rw [rationalMatrix_apply_apply, affineMatrix_apply,
    GeneralLinear.affinePointsEquiv_entry_evaluation]
  change (Scheme.ΓSpecIso (CommRingCat.of F)).hom
      ((g.left ≫ ρ.hom.hom.left).appTop _) =
    (Scheme.ΓSpecIso (CommRingCat.of F)).hom
      (((rationalPointEquiv F G.X g).left ≫ ρ.hom.hom.left).appTop _)
  rw [rationalPointEquiv_left]
  rfl

/-- Every regular function is polynomial in the matrix and inverse-matrix
entries of a supplied closed embedding. -/
theorem exists_polynomial_regularFunction (ρ : MatrixRepresentation G n)
    (hρ : IsClosedSubgroup ρ) (a : Γ(G.X.left, ⊤)) :
    ∃ p : MvPolynomial (GeneralLinear.Coordinate n) F,
      ∀ g : rationalPoints G,
        (Scheme.ΓSpecIso (CommRingCat.of F)).hom (g.left.appTop a) =
          MvPolynomial.aeval (GeneralLinear.values (ρ.rationalMatrix g)) p := by
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have : IsAffine (GeneralLinear.groupScheme n (CommRingCat.of F)).X.left :=
    GeneralLinear.isAffine_groupScheme n (CommRingCat.of F)
  obtain ⟨b, hb⟩ :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine ρ.hom.hom.left).2 a
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective
    ((Scheme.ΓSpecIso (CommRingCat.of (GeneralLinear.CoordinateRing n F))).hom b)
  refine ⟨p, ?_⟩
  intro g
  let x := rationalPointEquiv F G.X g
  have hm := rationalMatrix_eq_affineMatrix ρ g
  have hy : x ≫ ρ.hom.hom =
      (GeneralLinear.affinePointsEquiv n (CommRingCat.of F) (CommAlgCat.of F F)).symm
        (ρ.rationalMatrix g) := by
    apply (GeneralLinear.affinePointsEquiv n (CommRingCat.of F) (CommAlgCat.of F F)).injective
    rw [MulEquiv.apply_symm_apply]
    exact hm.symm
  have h := GeneralLinear.affinePointEvaluation_map_classify n (CommRingCat.of F)
    (CommAlgCat.of F F) (ρ.rationalMatrix g) b
  rw [← GeneralLinear.affinePointsEquiv_symm_apply, ← hy] at h
  rw [← hb]
  change G.affinePointEvaluation (CommAlgCat.of F F) x
    (ρ.hom.hom.left.appTop b) = _
  rw [← GroupScheme.affinePointEvaluation_postcomp, h, ← hp]
  exact GeneralLinear.classify_quotient _ p

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Nonempty n]

/-- Regular functions on the group have power growth in a closed embedding's
actual residue-normalized matrix norm. -/
theorem regularFunction_rationalMatrixNorm_bound (ρ : MatrixRepresentation G n)
    (hρ : IsClosedSubgroup ρ) (a : Γ(G.X.left, ⊤)) :
    let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
    ∃ (d : ℕ) (c : ℝ), 0 < c ∧ ∀ g : rationalPoints G,
      ‖(Scheme.ΓSpecIso (CommRingCat.of F)).hom (g.left.appTop a)‖ ≤
        c * rationalMatrixNorm F ρ g ^ d := by
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  obtain ⟨p, hp⟩ := exists_polynomial_regularFunction ρ hρ a
  obtain ⟨d, c, hc, hbound⟩ := polynomial_evaluation_power_bound p
  refine ⟨d, c, hc, fun g => ?_⟩
  rw [hp]
  apply hbound _ _ (one_le_rationalMatrixNorm F ρ g)
  intro v
  cases v with
  | entry i j => exact HarishChandraSchwartz.norm_le_glNorm _ i j
  | inverseEntry i j => exact HarishChandraSchwartz.norm_inv_le_glNorm _ i j

/-- Power comparison with a closed source embedding, with a constant uniform
in every rational point and every entry of the target matrix and its inverse. -/
theorem rationalMatrixNormComparison : RationalMatrixNormComparisonStatement.{u} := by
  intro F _ _ _ _ G n m _ _ _ _ _ _ ρ hρ τ
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  have hentry : ∀ i j : m, ∃ (d : ℕ) (c : ℝ), 0 < c ∧ ∀ g : rationalPoints G,
      ‖(τ.rationalMatrix g : Matrix m m F) i j‖ ≤
        c * rationalMatrixNorm F ρ g ^ d := by
    intro i j
    obtain ⟨d, c, hc, hb⟩ := regularFunction_rationalMatrixNorm_bound ρ hρ
      (τ.hom.hom.left.appTop (GeneralLinear.entrySection m (CommRingCat.of F) i j))
    refine ⟨d, c, hc, fun g => ?_⟩
    rw [rationalMatrix_apply_apply]
    exact hb g
  choose d c hc he using hentry
  obtain ⟨D, hD⟩ := Finite.exists_le (fun p : m × m => d p.1 p.2)
  obtain ⟨C, hC⟩ := Finite.exists_le (fun p : m × m => c p.1 p.2)
  have hCpos : 0 < C :=
    lt_of_lt_of_le (hc (Classical.arbitrary m) (Classical.arbitrary m))
      (hC (Classical.arbitrary m, Classical.arbitrary m))
  have hentry' : ∀ (g : rationalPoints G) (i j : m),
      ‖(τ.rationalMatrix g : Matrix m m F) i j‖ ≤
        C * rationalMatrixNorm F ρ g ^ D := by
    intro g i j
    exact (he i j g).trans (mul_le_mul (hC (i, j))
      (pow_le_pow_right₀ (one_le_rationalMatrixNorm F ρ g) (hD (i, j)))
      (pow_nonneg (zero_le_one.trans (one_le_rationalMatrixNorm F ρ g)) _) hCpos.le)
  refine ⟨D, C, hCpos, fun g => ?_⟩
  apply HarishChandraSchwartz.glNorm_le (hentry' g)
  intro i j
  have hi := hentry' g⁻¹ i j
  rw [map_inv, rationalMatrixNorm_inv] at hi
  exact hi

end Langlands.Plancherel
