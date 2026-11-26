import Langlands.Shimura.Unitary.HermitianCongruence
import Langlands.Shimura.Unitary.FiniteModels
import Langlands.LinearAlgebra.HermitianDiagonalization
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.Topology.Algebra.MvPolynomial

/-! # Local matrix neighborhoods and simple symmetric spectra -/

noncomputable section

namespace Langlands.Shimura.FiniteUnitary

open _root_.Algebra _root_.Polynomial Topology

universe u v

section Coefficients

variable {F : Type u} {L : Type v} [NormedField F] [Field L] [Algebra F L]
  [TopologicalSpace L] [IsTopologicalRing L] {n : ℕ}

private theorem continuous_charpolyCoeff (i : ℕ) :
    Continuous (fun X : Matrix (Fin n) (Fin n) L => X.charpoly.coeff i) := by
  have h : (fun X : Matrix (Fin n) (Fin n) L => X.charpoly.coeff i) = fun X =>
      MvPolynomial.eval (fun ij : Fin n × Fin n => X ij.1 ij.2)
        (MvPolynomial.map (Int.castRingHom L) ((Matrix.charpoly.univ ℤ (Fin n)).coeff i)) := by
    funext X
    rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, Matrix.charpoly.univ_coeff_eval₂Hom]
    rfl
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp (continuous_pi fun ij => continuous_apply _ |>.comp
    (continuous_apply ij.1))

/-- An open condition on the coefficients of a matrix characteristic polynomial
recovers the prescribed coefficient radius on polynomials from the embedded base. -/
def matrixCoefficientNeighborhood
    (hL : IsInducing (algebraMap F L)) (f : F[X]) (hf : f.Monic) (hd : f.natDegree = n)
    (ε : ℝ) (hε : 0 < ε) :
    {U : Set (Matrix (Fin n) (Fin n) L) // IsOpen U ∧
      (∀ X, X.charpoly = f.map (algebraMap F L) → X ∈ U) ∧
      ∀ X ∈ U, ∀ g : F[X], g.Monic → g.natDegree = n → X.charpoly = g.map (algebraMap F L) →
        ∀ i, ‖g.coeff i - f.coeff i‖ < ε} := by
  classical
  have hex : Nonempty {U : Set (Matrix (Fin n) (Fin n) L) // IsOpen U ∧
      (∀ X, X.charpoly = f.map (algebraMap F L) → X ∈ U) ∧
      ∀ X ∈ U, ∀ g : F[X], g.Monic → g.natDegree = n → X.charpoly = g.map (algebraMap F L) →
        ∀ i, ‖g.coeff i - f.coeff i‖ < ε} := by
    choose U hU hpre using fun i : Fin n => hL.isOpen_iff.mp
      (Metric.isOpen_ball : IsOpen (Metric.ball (f.coeff i) ε))
    let T : Set (Matrix (Fin n) (Fin n) L) :=
      ⋂ i : Fin n, (fun X => X.charpoly.coeff i) ⁻¹' U i
    have hT : IsOpen T := isOpen_iInter_of_finite fun i => (hU i).preimage
      (continuous_charpolyCoeff i.val)
    refine ⟨⟨T, hT, ?_, ?_⟩⟩
    · intro X hX
      apply Set.mem_iInter.mpr
      intro i
      change X.charpoly.coeff i ∈ U i
      rw [hX, Polynomial.coeff_map]
      change f.coeff i ∈ (algebraMap F L) ⁻¹' U i
      rw [hpre]
      exact Metric.mem_ball_self hε
    · intro X hX g hg hgdeg hXg j
      by_cases hj : j < n
      · let i : Fin n := ⟨j, hj⟩
        have hi := Set.mem_iInter.mp hX i
        change X.charpoly.coeff j ∈ U i at hi
        rw [hXg, Polynomial.coeff_map] at hi
        change g.coeff j ∈ (algebraMap F L) ⁻¹' U i at hi
        rw [hpre] at hi
        simpa only [dist_eq_norm] using Metric.mem_ball.mp hi
      · have he : g.coeff j = f.coeff j := by
          by_cases he : j = n
          · subst j
            calc
              _ = (1 : F) := hgdeg ▸ hg.coeff_natDegree
              _ = _ := (hd ▸ hf.coeff_natDegree).symm
          · have hlt : n < j := by omega
            rw [coeff_eq_zero_of_natDegree_lt (hgdeg.symm ▸ hlt),
              coeff_eq_zero_of_natDegree_lt (hd.symm ▸ hlt)]
        rwa [he, sub_self, _root_.norm_zero]
  exact Classical.choice hex

end Coefficients

section Spectra

variable (F : Type u) [Field F] {n : ℕ}

/-- A monic polynomial with distinct base-field roots indexed by `Fin n`. -/
def distinctScalarPolynomial : F[X] := ∏ i : Fin n, (X - C (i.val : F))

theorem distinctScalarPolynomial_monic : (distinctScalarPolynomial (n := n) F).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

theorem distinctScalarPolynomial_natDegree : (distinctScalarPolynomial (n := n) F).natDegree = n := by
  unfold distinctScalarPolynomial
  rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, Nat.cast_id]

theorem distinctScalarPolynomial_splits : (distinctScalarPolynomial (n := n) F).Splits :=
  Splits.prod (fun _ _ => Splits.X_sub_C _)

theorem distinctScalarPolynomial_separable [CharZero F] :
    (distinctScalarPolynomial (n := n) F).Separable :=
  separable_prod_X_sub_C_iff.mpr (fun _ _ h => Fin.ext (Nat.cast_injective h))

variable {F} {L : Type v} [Field L] [CharZero L] [Algebra F L] (c : AlgebraInvolution F L)

local notation "M" => Matrix (Fin n) (Fin n) L
local notation "θ" => matrixTranspose c n

private def coefficientEnd : L →+* L where
  toFun := c
  map_one' := c.apply_one
  map_zero' := c.apply_zero
  map_add' := c.apply_add
  map_mul' a b := (c.apply_mul a b).trans (mul_comm _ _)

private theorem exists_symmetricMatrix (H : Mˣ) (hH : θ (H : M) = H) :
    ∃ X : M, (θ).adjoint H hH X = X ∧ X.charpoly =
      (distinctScalarPolynomial (n := n) F).map (algebraMap F L) := by
  let γ := coefficientEnd c
  have hHerm (i j : Fin n) : γ ((H : M) i j) = (H : M) j i :=
    congrArg (fun A : M => A j i) hH
  obtain ⟨P, d, hP, hD, hd, hDne⟩ :=
    Langlands.Sesquilinear.exists_congr_diagonal_of_hermitian (c := γ) two_ne_zero c.apply_apply hHerm
  let Q : Mˣ := Matrix.GeneralLinearGroup.mkOfDetNeZero (P.map γ) (by
    change (γ.mapMatrix P).det ≠ 0
    rw [← RingHom.map_det]
    exact (map_ne_zero γ).2 hP)
  let U : Mˣ := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal d) (by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hDne (Matrix.GeneralLinearGroup.det_ne_zero H) i))
  have hU : θ (U : M) = U := by
    ext i j
    by_cases hij : i = j
    · subst j
      change c (Matrix.diagonal d i i) = Matrix.diagonal d i i
      rw [Matrix.diagonal_apply_eq]
      exact hd i
    · change c (Matrix.diagonal d j i) = Matrix.diagonal d i j
      simp [Matrix.diagonal_apply_ne, hij, Ne.symm hij]
  have hQ : θ (Q : M) * (H : M) * (Q : M) = U := by
    have ht : θ (Q : M) = P.transpose := by
      ext i j
      exact c.apply_apply _
    rw [ht]
    exact hD
  let Y : M := Matrix.diagonal fun i => algebraMap F L (i.val : F)
  have hY : θ Y = Y := by
    ext i j
    by_cases hij : i = j
    · subst j
      change c (Y i i) = Y i i
      simp only [Y, Matrix.diagonal_apply_eq]
      exact c.apply_algebraMap _
    · change c (Y j i) = Y i j
      simp [Y, Matrix.diagonal_apply_ne, hij, Ne.symm hij]
  have hcomm : Commute Y (U : M) := by
    change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    simp only [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  let e := matrixBasisChange (R := F) Q
  let X := e.symm Y
  refine ⟨X, e.injective ?_, ?_⟩
  · rw [matrixBasisChange_adjoint θ H U Q hH hU hQ, show e X = Y from e.apply_symm_apply _]
    rw [AlgebraInvolution.adjoint_apply, hY, mul_assoc, hcomm.eq, ← mul_assoc,
      Units.inv_mul, one_mul]
  · change (Q.val * Y * (↑Q⁻¹ : M)).charpoly = _
    rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]
    simp [distinctScalarPolynomial, Polynomial.map_prod]

/-- For a Hermitian Gram matrix over a characteristic-zero extension field,
a self-adjoint matrix can have the prescribed distinct base-field eigenvalues. -/
def symmetricMatrixWithDistinctScalarRoots (H : Mˣ) (hH : θ (H : M) = H) :
    {X : M // (θ).adjoint H hH X = X ∧ X.charpoly =
      (distinctScalarPolynomial (n := n) F).map (algebraMap F L)} :=
  let h := exists_symmetricMatrix c H hH
  ⟨h.choose, h.choose_spec⟩

end Spectra

end Langlands.Shimura.FiniteUnitary
