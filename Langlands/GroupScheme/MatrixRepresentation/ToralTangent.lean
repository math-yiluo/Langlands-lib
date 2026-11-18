import Langlands.GroupScheme.Lie.SemisimplePrimePowerReplacement
import Langlands.GroupScheme.MatrixRepresentation.NilpotentTangentObstruction
import Mathlib.Algebra.Lie.AdjointAction.Basic
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.RingTheory.Derivation.Lie

/-! # Tangent matrices of linearly reductive groups -/

noncomputable section

universe u

open AlgebraicGeometry Polynomial Langlands.LinearAlgebra
open scoped Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

open Langlands.GroupScheme.Lie

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] {n : ℕ}

local instance : CommGroup (lieKernel G k) := lieKernelCommGroup G
local instance : Module k (Additive (lieKernel G k)) := lieKernelModule G

/-- Each tangent matrix of a finite representation of a linearly reductive
group over an algebraically closed field of nonzero characteristic acts
semisimply. -/
theorem isSemisimple_tangentMatrix_of_linearlyReductive [IsAlgClosed k]
    (p : ℕ) [CharP k p] (hp : p ≠ 0)
    (hG : ∀ d (σ : MatrixRepresentation G (Fin d)), σ.IsSemisimple)
    (ρ : MatrixRepresentation G (Fin n)) (X : lieKernel G k) :
    Module.End.IsSemisimple (Matrix.toLinAlgEquiv' (ρ.tangentMatrix k X)) := by
  classical
  let : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero k p).resolve_right hp⟩
  let M := ρ.tangentMatrix k X
  have hdep := Module.Finite.not_linearIndependent_of_infinite (R := k)
    (fun i : ℕ => M ^ (p ^ i))
  obtain ⟨c, hrel, hc⟩ := not_linearIndependent_iff_finsupp.mp hdep
  have hs : c.support.Nonempty := Finsupp.support_nonempty_iff.mpr hc
  let m := c.support.min' hs
  have hm : m ∈ c.support := Finset.min'_mem c.support hs
  have hle (i : ℕ) (hi : i ∈ c.support) : m ≤ i := Finset.min'_le _ _ hi
  choose d hd using fun i : ℕ => IsAlgClosed.exists_pow_nat_eq (c i)
    (pow_pos (Nat.pos_of_ne_zero hp) m)
  let Q := primePowerRelationPolynomial c.support d p m
  let Z : Additive (lieKernel G k) :=
    ∑ i ∈ c.support, d i • Additive.ofMul (Lie.primePowerKernel G X p (i - m))
  have hpow (r : ℕ) : ρ.tangentMatrix k (Lie.primePowerKernel G X p r) =
      ρ.tangentMatrix k X ^ (p ^ r) := ρ.tangentMatrix_primePowerKernel X p r
  have hZ : ρ.tangentMatrix k Z.toMul = aeval M Q := by
    change ρ.kernelDifferential k Z = _
    simp only [Z, Q, primePowerRelationPolynomial, map_sum, map_smul, map_pow,
      aeval_X, kernelDifferential_apply, toMul_ofMul, hpow, M]
  have hpower : (aeval M Q) ^ (p ^ m) = 0 := by
    rw [← map_pow (aeval M)]
    have heq : Q ^ (p ^ m) = primePowerRelationPolynomial c.support c p 0 := by
      simp only [Q, primePowerRelationPolynomial]
      rw [sum_pow_char_pow]
      apply Finset.sum_congr rfl
      intro i hi
      rw [smul_eq_C_mul, mul_pow, ← map_pow C, hd, ← pow_mul, ← pow_add,
        Nat.sub_add_cancel (hle i hi), Nat.sub_zero, ← smul_eq_C_mul]
    rw [heq]
    simpa only [primePowerRelationPolynomial, map_sum, map_smul, map_pow, aeval_X,
      Nat.sub_zero, Finsupp.sum] using hrel
  have hzero : aeval M Q = 0 := by
    rw [← hZ]
    exact tangentMatrix_eq_zero_of_isNilpotent_of_linearlyReductive p hp hG ρ Z.toMul
      ⟨p ^ m, hZ ▸ hpower⟩
  have hd0 : d m ≠ 0 := by
    intro h
    apply Finsupp.mem_support_iff.mp hm
    rw [← hd m, h, zero_pow (pow_ne_zero _ hp)]
  have hsep : Q.Separable := separable_primePowerRelationPolynomial _ _ _ _ hm hle hd0
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree
  change aeval (Matrix.toLinAlgEquiv' M) Q = 0
  rw [aeval_algHom_apply, hzero, map_zero]

/-- The matrix commutator of two actual tangent matrices is an actual tangent
matrix of the same representation. -/
theorem exists_tangentMatrix_eq_commutator
    (ρ : MatrixRepresentation G (Fin n)) (X Y : lieKernel G k) :
    ∃ Z : lieKernel G k, ρ.tangentMatrix k Z =
      ρ.tangentMatrix k X * ρ.tangentMatrix k Y - ρ.tangentMatrix k Y * ρ.tangentMatrix k X := by
  let A := coordinateAlgebra G
  let U := coordinateMatrix ρ
  let D := Lie.translationDerivation G
  have hcomp (x y : lieKernel G k) : (U.map (D x)).map (D y) =
      (ρ.tangentMatrix k x * ρ.tangentMatrix k y).map (algebraMap k A) * U := by
    change ((coordinateMatrix ρ).map (Lie.translationDerivation G x)).map
      (Lie.translationDerivation G y).toLinearMap = _
    rw [coordinateMatrix_translationDerivation, map_linearMap_constant_mul]
    change _ * (coordinateMatrix ρ).map (Lie.translationDerivation G y) = _
    rw [coordinateMatrix_translationDerivation, ← mul_assoc, ← Matrix.map_mul]
  let bracket : Derivation k A A := ⁅D Y, D X⁆
  have hbracket : U.map bracket = (U.map (D X)).map (D Y) - (U.map (D Y)).map (D X) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, bracket, Derivation.commutator_apply]
  have hEval (M : Matrix (Fin n) (Fin n) k) :
      (M.map (algebraMap k A) * U).map (coordinateOrigin G) = M := by
    change (M.map (algebraMap k A) * coordinateMatrix ρ).map (coordinateOrigin G) = M
    rw [Matrix.map_mul, coordinateMatrix_origin, mul_one]
    ext i j
    exact (coordinateOrigin G).commutes _
  refine ⟨Lie.kernelOfDerivation G bracket, ?_⟩
  rw [tangentMatrix_kernelOfDerivation, hbracket, hcomp, hcomp]
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
  exact congrArg₂ (· - ·)
    (congrArg (fun M => M i j) (hEval (ρ.tangentMatrix k X * ρ.tangentMatrix k Y)))
    (congrArg (fun M => M i j) (hEval (ρ.tangentMatrix k Y * ρ.tangentMatrix k X)))

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A Lie subalgebra of endomorphisms consisting of semisimple elements over an
algebraically closed field is abelian. -/
private theorem commute_of_semisimple_lieSubalgebra [IsAlgClosed k]
    (L : LieSubalgebra k (Module.End k (Fin n → k)))
    (hL : ∀ z : L, Module.End.IsSemisimple (z : Module.End k (Fin n → k)))
    (a b : L) : Commute (a : Module.End k (Fin n → k)) (b : Module.End k (Fin n → k)) := by
  have hadSem (u : L) : (LieAlgebra.ad k L u).IsSemisimple := by
    have hinv : L.toSubmodule ∈ (LieAlgebra.ad k (Module.End k (Fin n → k))
        (u : Module.End k (Fin n → k))).invtSubmodule := by
      intro v hv
      exact L.lie_mem u.property hv
    exact (LieAlgebra.ad_isSemisimple_of_isSemisimple (hL u)).restrict hinv
  have ha : LieAlgebra.ad k L a = 0 := by
    apply (hadSem a).eq_zero_iff_forall_eigenvalue.mpr
    intro μ hμ
    obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff _).mp hμ
    have hEq : ⁅a, z⁆ = μ • z := Module.End.mem_eigenspace_iff.mp hz
    let B := LieAlgebra.ad k L z
    have hBa : B a = -(μ • z) := by
      change ⁅z, a⁆ = _
      calc
        ⁅z, a⁆ = -⁅a, z⁆ := by rw [← lie_skew a z, neg_neg]
        _ = -(μ • z) := congrArg Neg.neg hEq
    have hBz : B z = 0 := lie_self z
    have h₂ : a ∈ B.genEigenspace (0 : k) (↑(2 : ℕ) : ℕ∞) := by
      rw [Module.End.mem_genEigenspace_nat]
      simp only [zero_smul, sub_zero, LinearMap.mem_ker, pow_two, Module.End.mul_apply,
        hBa, map_neg, map_smul, hBz, smul_zero, neg_zero]
    rw [(hadSem z).isFinitelySemisimple.genEigenspace_eq_eigenspace 0 (by decide)] at h₂
    have h₀ := Module.End.mem_eigenspace_iff.mp h₂
    rw [hBa, zero_smul, neg_eq_zero, smul_eq_zero] at h₀
    exact h₀.resolve_right hz0
  have hab : ⁅a, b⁆ = 0 := LinearMap.congr_fun ha b
  exact sub_eq_zero.mp (by
    simpa only [LieSubalgebra.coe_bracket, Ring.lie_def, ZeroMemClass.coe_zero] using
      congrArg Subtype.val hab)

/-- All actual tangent matrices of one finite representation of an affine
linearly reductive group commute over an algebraically closed field of
nonzero characteristic. -/
theorem commute_tangentMatrix_of_linearlyReductive [IsAlgClosed k]
    (p : ℕ) [CharP k p] (hp : p ≠ 0)
    (hG : ∀ d (σ : MatrixRepresentation G (Fin d)), σ.IsSemisimple)
    (ρ : MatrixRepresentation G (Fin n)) (X Y : lieKernel G k) :
    Commute (ρ.tangentMatrix k X) (ρ.tangentMatrix k Y) := by
  let d : Additive (lieKernel G k) →ₗ[k] Module.End k (Fin n → k) :=
    (Matrix.toLinAlgEquiv').toLinearMap.comp (ρ.kernelDifferential k)
  let L : LieSubalgebra k (Module.End k (Fin n → k)) :=
    { d.range with
      lie_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        obtain ⟨z, hz⟩ := ρ.exists_tangentMatrix_eq_commutator x.toMul y.toMul
        refine ⟨Additive.ofMul z, ?_⟩
        change Matrix.toLinAlgEquiv' (ρ.tangentMatrix k z) = ⁅d x, d y⁆
        rw [hz, Ring.lie_def, map_sub, map_mul, map_mul]
        rfl }
  have hL (z : L) : Module.End.IsSemisimple (z : Module.End k (Fin n → k)) := by
    obtain ⟨x, hx⟩ := z.property
    rw [← hx]
    exact isSemisimple_tangentMatrix_of_linearlyReductive p hp hG ρ x.toMul
  let a : L := ⟨d (Additive.ofMul X), ⟨_, rfl⟩⟩
  let b : L := ⟨d (Additive.ofMul Y), ⟨_, rfl⟩⟩
  apply Matrix.toLinAlgEquiv'.injective
  rw [map_mul, map_mul]
  exact (commute_of_semisimple_lieSubalgebra L hL a b).eq

end Langlands.GroupScheme.MatrixRepresentation
