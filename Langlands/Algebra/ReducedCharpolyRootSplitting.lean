import Langlands.Algebra.ReducedNormScalarExtension
import Mathlib.LinearAlgebra.Basis.MulOpposite
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.SimpleRing.Congr

/-! # Splitting a central simple algebra at a simple root of a reduced charpoly -/

noncomputable section

open Polynomial
open scoped TensorProduct

namespace Langlands.CentralSimple

universe u

variable {K : Type u} [Field K] (A : CSA.{u, u} K)

private theorem rootMultiplicity_pow_of_ne_zero (p : K[X]) (hp : p ≠ 0) (r : K) (n : ℕ) :
    (p ^ n).rootMultiplicity r = n * p.rootMultiplicity r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hp) hp), ih, Nat.succ_mul]

/-- A root in the ground field of multiplicity one in the reduced charpoly gives a splitting. -/
theorem isSplit_of_simple_root (a : A) (r : K)
    (hr : (reducedCharpoly K A a).rootMultiplicity r = 1) : Brauer.IsSplit A := by
  let f := Algebra.lmul K A a
  let V := f.maxGenEigenspace r
  have hchar : f.charpoly = reducedCharpoly K A a ^ reducedDegree K A := by
    rw [← charpoly_leftMulMatrix_eq_reducedCharpoly_pow K A (Module.finBasis K A)]
    exact (LinearMap.charpoly_toMatrix _ _).symm
  have hV : Module.finrank K V = reducedDegree K A := by
    change Module.finrank K (f.maxGenEigenspace r) = _
    rw [LinearMap.finrank_maxGenEigenspace_eq, hchar,
      rootMultiplicity_pow_of_ne_zero _ (reducedCharpoly_monic K A a).ne_zero, hr, mul_one]
  let : IsScalarTower K Aᵐᵒᵖ A := ⟨fun c b x => by
    change x * (c • b.unop) = c • (x * b.unop)
    exact mul_smul_comm _ _ _⟩
  let W : Submodule Aᵐᵒᵖ A := {
    carrier := V
    add_mem' := V.add_mem
    zero_mem' := V.zero_mem
    smul_mem' := by
      intro b x hx
      have hl : f - r • (1 : Module.End K A) = Algebra.lmul K A (a - algebraMap K A r) := by
        rw [map_sub, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
      change x ∈ f.maxGenEigenspace r at hx
      rw [Module.End.mem_maxGenEigenspace, hl] at hx
      obtain ⟨n, hn⟩ := hx
      change x * b.unop ∈ f.maxGenEigenspace r
      rw [Module.End.mem_maxGenEigenspace, hl]
      refine ⟨n, ?_⟩
      rw [← map_pow] at hn ⊢
      change (a - algebraMap K A r) ^ n * x = 0 at hn
      change (a - algebraMap K A r) ^ n * (x * b.unop) = 0
      rw [← mul_assoc, hn, zero_mul] }
  have hW : Module.finrank K W = reducedDegree K A := hV
  let : Nontrivial W := Module.nontrivial_of_finrank_pos (hW.symm ▸ reducedDegree_pos K A)
  let ρ : Aᵐᵒᵖ →ₐ[K] Module.End K W := Algebra.lsmul K K W
  have hinj : Function.Injective ρ := ρ.toRingHom.injective
  have hdim : Module.finrank K Aᵐᵒᵖ = Module.finrank K (Module.End K W) := by
    rw [MulOpposite.finrank, Module.finrank_linearMap, hW, finrank_eq_reducedDegree_mul_self]
  have hsurj : Function.Surjective ρ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := K) (V := Aᵐᵒᵖ)
      (V₂ := Module.End K W) (f := ρ.toLinearMap) hdim).mp hinj
  let e := (AlgEquiv.ofBijective ρ ⟨hinj, hsurj⟩).trans
    (LinearMap.toMatrixAlgEquiv (Module.finBasis K W))
  exact ⟨Module.finrank K W, hW.symm ▸ reducedDegree_pos K A, ⟨
    (AlgEquiv.opOp K A).trans (e.op.trans
      (Matrix.transposeAlgEquiv (R := K) (m := Fin (Module.finrank K W)) (α := K)).symm)⟩⟩

/-- A field extension containing a root of a separable reduced charpoly splits the algebra. -/
theorem isSplit_baseChange_of_isRoot (E : Type u) [Field E] [Algebra K E] (a : A)
    (hsep : (reducedCharpoly K A a).Separable) (r : E)
    (hr : IsRoot ((reducedCharpoly K A a).map (algebraMap K E)) r) :
    Brauer.IsSplit (Brauer.baseChange E A) := by
  apply isSplit_of_simple_root (Brauer.baseChange E A) (1 ⊗ₜ[K] a) r
  rw [reducedCharpoly_baseChange]
  have hs : ((reducedCharpoly K A a).map (algebraMap K E)).Separable := hsep.map
  exact le_antisymm (rootMultiplicity_le_one_of_separable hs r)
    ((rootMultiplicity_pos hs.ne_zero).mpr hr)

/-- Adjoining an irreducible factor of a separable reduced charpoly splits the algebra. -/
theorem isSplit_baseChange_adjoinRoot_factor (a : A) (hsep : (reducedCharpoly K A a).Separable)
    (p : K[X]) [Fact (Irreducible p)] (hp : p ∣ reducedCharpoly K A a) :
    Brauer.IsSplit (Brauer.baseChange (AdjoinRoot p) A) := by
  apply isSplit_baseChange_of_isRoot A (AdjoinRoot p) a hsep (AdjoinRoot.root p)
  rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def, AdjoinRoot.aeval_eq]
  exact AdjoinRoot.mk_eq_zero.mpr hp

/-- The factor-field splitting condition is necessary for a separable reduced charpoly. -/
def ReducedCharpolyRootSplittingStatement : Prop :=
  ∀ (K : Type u) [Field K] (A : CSA.{u, u} K) (a : A),
    (reducedCharpoly K A a).Separable →
    ∀ (p : K[X]) [Fact (Irreducible p)], p ∣ reducedCharpoly K A a →
      Brauer.IsSplit (Brauer.baseChange (AdjoinRoot p) A)

/-- Necessity in the factor-field criterion. -/
theorem reducedCharpolyRootSplitting : ReducedCharpolyRootSplittingStatement.{u} := by
  intro K _ A a hsep p _ hp
  exact isSplit_baseChange_adjoinRoot_factor A a hsep p hp

end Langlands.CentralSimple
