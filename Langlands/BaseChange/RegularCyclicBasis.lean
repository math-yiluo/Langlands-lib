import Langlands.BaseChange.Norm
import Mathlib.Algebra.Module.PID
import Mathlib.LinearAlgebra.AnnihilatingPolynomial
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

noncomputable section

open Matrix Module Polynomial

namespace Langlands.BaseChange

universe u

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The matrix with columns `v, A v, …, A^(n-1) v`. -/
def cyclicBasisMatrix (A : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => (A ^ (j : ℕ) *ᵥ v) i

@[simp]
theorem cyclicBasisMatrix_col (A : Matrix (Fin n) (Fin n) R) (v : Fin n → R) (j : Fin n) :
    (cyclicBasisMatrix A v).col j = A ^ (j : ℕ) *ᵥ v := rfl

set_option maxHeartbeats 400000 in
private theorem minpoly_natDegree_of_separable {K : Type*} [Field K]
    (A : Matrix (Fin n) (Fin n) K) (hA : A.charpoly.Separable) :
    (minpoly K A).natDegree = n := by
  classical
  let L := AlgebraicClosure K
  let f : K →+* L := algebraMap K L
  let B := A.map f
  have hB : B.charpoly = A.charpoly.map f := Matrix.charpoly_map A f
  have sepB : B.charpoly.Separable := hB.symm ▸ hA.map
  have hroot : B.charpoly.roots ⊆ (minpoly L B).roots := by
    intro x hx
    have he : Module.End.HasEigenvalue B.toLin' x := by
      apply (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
      rw [Matrix.charpoly_toLin']
      exact (mem_roots (Matrix.charpoly_monic B).ne_zero).mp hx
    have hmp : (minpoly L B).IsRoot x := by
      rw [← Matrix.minpoly_toLin']
      exact Module.End.isRoot_of_hasEigenvalue he
    exact (mem_roots (minpoly.ne_zero B.isIntegral)).mpr hmp
  have hcard := Multiset.card_le_card ((Multiset.le_iff_subset (nodup_roots sepB)).mpr hroot)
  have hdeg : n ≤ (minpoly L B).natDegree := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin] at hcard
    exact hcard.trans (card_roots' _)
  have hdvd : minpoly L B ∣ (minpoly K A).map f := by
    let g : Matrix (Fin n) (Fin n) K →+* Matrix (Fin n) (Fin n) L := f.mapMatrix
    have hg : (algebraMap L (Matrix (Fin n) (Fin n) L)).comp f =
        g.comp (algebraMap K (Matrix (Fin n) (Fin n) K)) := by
      apply RingHom.ext
      intro a
      exact (Matrix.map_algebraMap a f (map_zero f) rfl).symm
    apply minpoly.dvd L B
    change aeval (g A) ((minpoly K A).map f) = 0
    rw [← map_aeval_eq_aeval_map hg, minpoly.aeval, map_zero]
  have hmapDegree := (minpoly.monic A.isIntegral).natDegree_map f
  apply le_antisymm
  · simpa only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] using
      natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly A) (Matrix.charpoly_monic A).ne_zero
  · rw [← hmapDegree]
    exact hdeg.trans (natDegree_le_of_dvd hdvd ((minpoly.monic A.isIntegral).map f).ne_zero)

/-- A matrix with separable characteristic polynomial has a cyclic vector over its field. -/
def RegularCyclicBasisStatement : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (A : Matrix (Fin n) (Fin n) K),
    A.charpoly.Separable → ∃ v, IsUnit (cyclicBasisMatrix A v)

theorem regularCyclicBasis : RegularCyclicBasisStatement.{u} := by
  classical
  intro K _ n A hA
  let f := A.toLin'
  obtain ⟨x, hx⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator
    (R := K[X]) (M := Module.AEval' f)
  let v := (Module.AEval'.of f).symm x
  refine ⟨v, Matrix.mulVec_injective_iff_isUnit.mp (Matrix.mulVec_injective_iff.mpr ?_)⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  let p : K[X] := ∑ i : Fin n, monomial (i : ℕ) (c i)
  have hpow (i : ℕ) : (f ^ i) v = A ^ i *ᵥ v := by
    rw [← Matrix.toLinAlgEquiv'_apply, map_pow]
    rfl
  have hsum : (aeval f p) v = 0 := by
    simpa only [p, map_sum, LinearMap.sum_apply, aeval_monomial, ← Algebra.smul_def,
      LinearMap.smul_apply, hpow, cyclicBasisMatrix_col] using hc
  have hpx : p ∈ LinearMap.ker (LinearMap.toSpanSingleton K[X] (Module.AEval' f) x) := by
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← (Module.AEval'.of f).apply_symm_apply x,
      ← Module.AEval.of_aeval_smul]
    simpa [hsum]
  rw [hx, ← Polynomial.span_minpoly_eq_annihilator, Ideal.mem_span_singleton,
    Matrix.minpoly_toLin'] at hpx
  have hp : p = 0 := by
    by_contra hp
    have hlo := natDegree_le_of_dvd hpx hp
    have hhi : p.natDegree ≤ n - 1 :=
      natDegree_sum_le_of_forall_le _ _ fun i _ =>
        (natDegree_monomial_le _).trans (Nat.le_sub_one_of_lt i.isLt)
    rw [minpoly_natDegree_of_separable A hA] at hlo
    have := j.isLt
    omega
  have hcoeff : p.coeff (j : ℕ) = c j := by
    rw [show p = ∑ i : Fin n, monomial (i : ℕ) (c i) by rfl, finsetSum_coeff]
    simp [coeff_monomial, Fin.val_inj]
  simpa [hp] using hcoeff.symm

/-- A cyclic basis extends by applying the coefficient homomorphism. -/
theorem cyclicBasisMatrix_map {S : Type*} [CommRing S] (f : R →+* S)
    (A : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    (cyclicBasisMatrix A v).map f = cyclicBasisMatrix (A.map f) (f ∘ v) := by
  ext i j
  change f ((A ^ (j : ℕ) *ᵥ v) i) = ((A.map f) ^ (j : ℕ) *ᵥ (f ∘ v)) i
  rw [RingHom.map_mulVec]
  exact congrArg (fun M : Matrix (Fin n) (Fin n) S => (M *ᵥ (f ∘ v)) i)
    (map_pow f.mapMatrix A (j : ℕ))

/-- Two matrices commuting with `A` are equal if they agree on a cyclic vector of `A`. -/
theorem eq_of_commute_mulVec_eq {A B D : Matrix (Fin n) (Fin n) R} {v : Fin n → R}
    (hv : IsUnit (cyclicBasisMatrix A v)) (hB : Commute B A) (hD : Commute D A)
    (h : B *ᵥ v = D *ᵥ v) : B = D := by
  apply hv.mul_left_inj.mp
  ext i j
  change ((B * cyclicBasisMatrix A v).col j) i = ((D * cyclicBasisMatrix A v).col j) i
  rw [col_mul_eq_mulVec_col, col_mul_eq_mulVec_col, cyclicBasisMatrix_col,
    mulVec_mulVec, mulVec_mulVec, (hB.pow_right (j : ℕ)).eq, (hD.pow_right (j : ℕ)).eq,
    ← mulVec_mulVec, ← mulVec_mulVec, h]

/-- Over a commutative ring, every matrix commuting with a cyclic matrix is a polynomial in it. -/
theorem exists_sum_pow_of_commute {A B : Matrix (Fin n) (Fin n) R} {v : Fin n → R}
    (hv : IsUnit (cyclicBasisMatrix A v)) (hB : Commute B A) :
    ∃ c : Fin n → R, B = ∑ j : Fin n, c j • A ^ (j : ℕ) := by
  let C := cyclicBasisMatrix A v
  let U := hv.unit
  have hU : (U : Matrix (Fin n) (Fin n) R) = C := hv.unit_spec
  let c := (↑(U⁻¹) : Matrix (Fin n) (Fin n) R) *ᵥ (B *ᵥ v)
  refine ⟨c, eq_of_commute_mulVec_eq hv hB (Commute.sum_left _ _ _ ?_) ?_⟩
  · intro j _
    exact ((Commute.refl A).pow_left (j : ℕ)).smul_left (c j)
  · rw [sum_mulVec]
    simp only [smul_mulVec]
    simp_rw [← cyclicBasisMatrix_col A v]
    calc
      B *ᵥ v = C *ᵥ c := by
        dsimp only [c]
        rw [← hU, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
      _ = ∑ j : Fin n, c j • C.col j := by
        ext i
        simp only [mulVec_apply_eq_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Matrix.col_apply]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The centralizer of a cyclic matrix over a commutative ring is commutative. -/
theorem commute_of_commute_cyclicBasisMatrix {A B D : Matrix (Fin n) (Fin n) R} {v : Fin n → R}
    (hv : IsUnit (cyclicBasisMatrix A v)) (hB : Commute B A) (hD : Commute D A) :
    Commute B D := by
  obtain ⟨c, rfl⟩ := exists_sum_pow_of_commute hv hB
  exact Commute.sum_left _ _ _ fun j _ => ((hD.symm.pow_left (j : ℕ))).smul_left (c j)

open Langlands.JacquetLanglands

/-- The centralizer of a regular semisimple matrix stays commutative after base change. -/
theorem commute_of_regular_baseChange {F E : Type*} [Field F] [CommRing E] [Algebra F E]
    {γ : GeneralLinear n F} (hγ : IsRegularSemisimple γ) {a b : GeneralLinear n E}
    (ha : Commute a (baseChange F E n γ)) (hb : Commute b (baseChange F E n γ)) :
    Commute a b := by
  obtain ⟨v, hv⟩ := regularCyclicBasis F n γ.val hγ
  have hvE : IsUnit (cyclicBasisMatrix (baseChange F E n γ).val (algebraMap F E ∘ v)) := by
    change IsUnit (cyclicBasisMatrix (γ.val.map (algebraMap F E)) (algebraMap F E ∘ v))
    rw [← cyclicBasisMatrix_map]
    exact hv.map (algebraMap F E).mapMatrix
  apply Units.ext
  exact (commute_of_commute_cyclicBasisMatrix hvE
    (ha.map (Units.coeHom _)) (hb.map (Units.coeHom _))).eq

/-- Column `j` gives the first `n` coefficients of `X^(j+1)` reduced modulo `p`. -/
def charpolyActionMatrix (n : ℕ) (p : R[X]) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => (X ^ ((j : ℕ) + 1) %ₘ p).coeff (i : ℕ)

/-- Cayley–Hamilton expresses the action of a matrix in cyclic-vector coordinates. -/
theorem mul_cyclicBasisMatrix (A : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    A * cyclicBasisMatrix A v = cyclicBasisMatrix A v * charpolyActionMatrix n A.charpoly := by
  nontriviality R
  ext i j
  change ((A * cyclicBasisMatrix A v).col j) i =
    ((cyclicBasisMatrix A v * charpolyActionMatrix n A.charpoly).col j) i
  rw [col_mul_eq_mulVec_col, cyclicBasisMatrix_col, mulVec_mulVec, ← pow_succ',
    col_mul_eq_mulVec_col]
  let p := (X : R[X]) ^ ((j : ℕ) + 1) %ₘ A.charpoly
  have hdeg : A.charpoly.natDegree = n := by simp
  have hne : A.charpoly ≠ 1 := by
    intro heq
    have := j.isLt
    rw [heq, natDegree_one] at hdeg
    omega
  have hp : p.natDegree < n := hdeg ▸ natDegree_modByMonic_lt _ A.charpoly_monic hne
  have hpow : A ^ ((j : ℕ) + 1) = ∑ k : Fin n, p.coeff (k : ℕ) • A ^ (k : ℕ) := by
    rw [Matrix.pow_eq_aeval_mod_charpoly]
    change aeval A p = _
    rw [aeval_eq_sum_range' hp]
    exact (Fin.sum_univ_eq_sum_range (fun k : ℕ => p.coeff k • A ^ k) n).symm
  rw [hpow, sum_mulVec]
  simp only [smul_mulVec, mulVec_apply_eq_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- Invertible cyclic bases give a conjugator for matrices with equal characteristic polynomial. -/
theorem cyclicBasis_conjugator {A B : Matrix (Fin n) (Fin n) R} {v w : Fin n → R}
    (hA : IsUnit (cyclicBasisMatrix A v)) (hB : IsUnit (cyclicBasisMatrix B w))
    (hp : A.charpoly = B.charpoly) :
    A * (↑(hA.unit * hB.unit⁻¹) : Matrix (Fin n) (Fin n) R) =
      (↑(hA.unit * hB.unit⁻¹) : Matrix (Fin n) (Fin n) R) * B := by
  apply hB.mul_left_inj.mp
  have hC : (↑(hA.unit * hB.unit⁻¹) : Matrix (Fin n) (Fin n) R) * cyclicBasisMatrix B w =
      cyclicBasisMatrix A v := by
    calc
      _ = (↑(hA.unit * hB.unit⁻¹) : Matrix (Fin n) (Fin n) R) * ↑hB.unit :=
        congrArg (fun M => ↑(hA.unit * hB.unit⁻¹) * M) hB.unit_spec.symm
      _ = _ := by
        rw [← Units.val_mul, mul_assoc, inv_mul_cancel, mul_one, hA.unit_spec]
  rw [mul_assoc A, hC, mul_cyclicBasisMatrix, hp, mul_assoc _ B, mul_cyclicBasisMatrix,
    ← mul_assoc, hC]

end Langlands.BaseChange
