import Langlands.Algebra.LieCasimir
import Langlands.Algebra.LieEnvelopingSymbol
import Langlands.Representation.Archimedean.Kostant.Center

/-! # Gelfand central elements of an enveloping algebra with an invariant form -/

noncomputable section

universe u v w

set_option autoImplicit false

namespace Langlands.Algebra.LieGelfandCentral

open Langlands.Algebra.UniversalEnveloping Langlands.Archimedean.Kostant
  Langlands.Algebra.LieEnvelopingSymbol MvPolynomial

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L]
  {I : Type w} [Fintype I] [DecidableEq I]
  (B : LinearMap.BilinForm k L) (hB : B.Nondegenerate) (b : Module.Basis I k L)

local notation "U" => UniversalEnvelopingAlgebra k L
local notation "ι" => UniversalEnvelopingAlgebra.ι k

/-- The matrix coefficient `(ad x)_{pq}` of the adjoint action in the basis `b`. -/
def adCoeff (x : L) (p q : I) : k := b.repr ⁅x, b q⁆ p

/-- The Gelfand matrix `T_{pq} = ∑_i (ad b_i)_{pq} ι(b^i)`, where `b^i` is the dual basis of `b`
for the form `B`. -/
def gelfandMatrix : Matrix I I U :=
  Matrix.of fun p q => ∑ i, adCoeff b (b i) p q • ι (B.dualBasis hB b i)

/-- The scalar matrix of `ad x` inside the matrices over `U`. -/
def adMatrix (x : L) : Matrix I I U :=
  Matrix.of fun p q => algebraMap k U (adCoeff b x p q)

/-- The entrywise commutator with a Lie generator. -/
def commMat (x : L) (A : Matrix I I U) : Matrix I I U :=
  A.map fun u => ι x * u - u * ι x

omit [DecidableEq I] in
theorem commMat_mul (x : L) (A A' : Matrix I I U) :
    commMat x (A * A') = commMat x A * A' + A * commMat x A' := by
  ext p q
  simp only [commMat, Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, Finset.mul_sum,
    Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  noncomm_ring

omit [DecidableEq I] in
theorem adCoeff_lie (x y : L) (p q : I) :
    adCoeff b ⁅x, y⁆ p q = ∑ r, (adCoeff b x p r * adCoeff b y r q - adCoeff b y p r *
      adCoeff b x r q) := by
  unfold adCoeff
  rw [lie_lie, map_sub, Finsupp.sub_apply]
  conv_lhs => rw [← b.sum_repr ⁅y, b q⁆, ← b.sum_repr ⁅x, b q⁆]
  simp only [lie_sum, lie_smul, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul, Finset.sum_sub_distrib]
  congr 1 <;> refine Finset.sum_congr rfl fun r _ => by ring

/-- **Gelfand's rule.** For an invariant nondegenerate form, the entrywise commutator of `ι x`
with the Gelfand matrix is `T R - R T`, where `R` is the scalar matrix of `ad x`. -/
theorem commMat_gelfandMatrix (hInv : ∀ x y z : L, B ⁅x, y⁆ z = B x ⁅y, z⁆) (x : L) :
    commMat x (gelfandMatrix B hB b) =
      gelfandMatrix B hB b * adMatrix b x - adMatrix b x * gelfandMatrix B hB b := by
  let d := B.dualBasis hB b
  have hcoef (i j : I) : d.repr ⁅x, d i⁆ j = -b.repr ⁅x, b j⁆ i := by
    rw [LinearMap.BilinForm.dualBasis_repr_apply,
      LieCasimir.invariant_form_skew_adjoint B hInv, LieCasimir.form_dual_left_eq_repr]
  ext p q
  have hl : ι x * gelfandMatrix B hB b p q - gelfandMatrix B hB b p q * ι x =
      ∑ i, adCoeff b (b i) p q • ι ⁅x, d i⁆ := by
    simp only [gelfandMatrix, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul,
      ← Finset.sum_sub_distrib, mul_smul_comm, smul_mul_assoc, ← smul_sub]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LieHom.map_lie, Ring.lie_def]
  have hr : ∑ i, adCoeff b (b i) p q • ι ⁅x, d i⁆ =
      -∑ j, adCoeff b ⁅x, b j⁆ p q • ι (d j) := by
    calc
      ∑ i, adCoeff b (b i) p q • ι ⁅x, d i⁆ =
          ∑ i, ∑ j, -(adCoeff b (b i) p q * b.repr ⁅x, b j⁆ i) • ι (d j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        conv_lhs => rw [← d.sum_repr ⁅x, d i⁆]
        simp only [map_sum, hcoef, neg_smul, map_neg, map_smul, Finset.smul_sum,
          smul_neg, smul_smul]
      _ = -∑ j, adCoeff b ⁅x, b j⁆ p q • ι (d j) := by
        rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_smul, ← neg_smul]
        congr 1
        rw [Finset.sum_neg_distrib, neg_inj]
        unfold adCoeff
        conv_rhs => rw [← b.sum_repr ⁅x, b j⁆]
        simp only [sum_lie, smul_lie, map_sum, map_smul, Finsupp.coe_finsetSum,
          Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
        refine Finset.sum_congr rfl fun i _ => by ring
  simp only [commMat, Matrix.map_apply, Matrix.sub_apply]
  rw [hl, hr]
  simp only [adCoeff_lie, gelfandMatrix, adMatrix, Matrix.mul_apply, Matrix.of_apply,
    Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_smul,
    ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mul_assoc, ← Algebra.commutes, ← Algebra.smul_def, ← Algebra.smul_def, smul_smul,
    smul_smul, sub_smul, neg_sub]

theorem commMat_pow (hInv : ∀ x y z : L, B ⁅x, y⁆ z = B x ⁅y, z⁆) (x : L) (n : ℕ) :
    commMat x (gelfandMatrix B hB b ^ n) =
      gelfandMatrix B hB b ^ n * adMatrix b x - adMatrix b x * gelfandMatrix B hB b ^ n := by
  induction n with
  | zero =>
    ext p q
    simp only [commMat, pow_zero, Matrix.map_apply, Matrix.one_apply, mul_one, one_mul,
      Matrix.sub_apply]
    split_ifs <;> simp
  | succ n ih =>
    rw [pow_succ, commMat_mul, ih, commMat_gelfandMatrix B hB b hInv]
    noncomm_ring

/-- Gelfand's element `C_n = tr(T^n)`. -/
def gelfand (n : ℕ) : U := Matrix.trace (gelfandMatrix B hB b ^ n)

theorem gelfand_mem_center (hInv : ∀ x y z : L, B ⁅x, y⁆ z = B x ⁅y, z⁆) (n : ℕ) :
    gelfand B hB b n ∈ Subalgebra.center k U := by
  refine mem_center_of_commute k L fun x => ?_
  unfold gelfand Matrix.trace
  rw [← sub_eq_zero, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  have h (p : I) : ι x * (gelfandMatrix B hB b ^ n).diag p -
      (gelfandMatrix B hB b ^ n).diag p * ι x = commMat x (gelfandMatrix B hB b ^ n) p p := rfl
  simp only [h, commMat_pow B hB b hInv, Matrix.sub_apply, Matrix.mul_apply,
    Finset.sum_sub_distrib, adMatrix, Matrix.of_apply]
  rw [sub_eq_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun p _ => ?_
  rw [Algebra.commutes]

theorem gelfandMatrix_mem (p q : I) : gelfandMatrix B hB b p q ∈ degreeFiltration k L 1 := by
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  simpa using generator_mem_degreeOne k L (B.dualBasis hB b i)

theorem gelfandMatrix_pow_mem (n : ℕ) (p q : I) :
    (gelfandMatrix B hB b ^ n) p q ∈ degreeFiltration k L n := by
  induction n generalizing p q with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    split_ifs
    · exact Submodule.one_le.mp (by simp)
    · exact Submodule.zero_mem _
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Submodule.sum_mem _ fun r _ =>
      mul_mem_degreeFiltration k L (ih p r) (gelfandMatrix_mem B hB b r q)

theorem gelfand_mem (n : ℕ) : gelfand B hB b n ∈ degreeFiltration k L n :=
  Submodule.sum_mem _ fun p _ => gelfandMatrix_pow_mem B hB b n p p

variable {bs : List I} (hbs : bs.Nodup) (hall : ∀ c, c ∈ bs)

/-- The symbol matrix `Ξ_{pq} = ∑_i (ad b_i)_{pq} ξ(b^i)`. -/
def symbolMatrix : Matrix I I (MvPolynomial I k) :=
  Matrix.of fun p q => ∑ i, adCoeff b (b i) p q • ξ b (B.dualBasis hB b i)

theorem symbol_gelfandMatrix_pow (n : ℕ) (p q : I) :
    symbol b hbs hall n ((gelfandMatrix B hB b ^ n) p q) = (symbolMatrix B hB b ^ n) p q := by
  induction n generalizing p q with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    split_ifs
    · exact symbol_one b hbs hall
    · simp
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply, map_sum, pow_succ, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [symbol_mul b hbs hall (gelfandMatrix_pow_mem B hB b n p r) (gelfandMatrix_mem B hB b r q),
      ih]
    congr 1
    simp only [gelfandMatrix, symbolMatrix, Matrix.of_apply, map_sum, map_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    have h := symbol_word_of_length_eq b hbs hall [B.dualBasis hB b i]
    simpa [word] using h

/-- The degree-`n` symbol of `C_n` is `tr(Ξ^n)`. -/
theorem symbol_gelfand (n : ℕ) :
    symbol b hbs hall n (gelfand B hB b n) = Matrix.trace (symbolMatrix B hB b ^ n) := by
  simp only [gelfand, Matrix.trace, Matrix.diag, map_sum, symbol_gelfandMatrix_pow]

end Langlands.Algebra.LieGelfandCentral
