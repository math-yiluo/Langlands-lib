import Langlands.ClassFieldTheory.Local.LocalDivisionSplittingDegree

/-! # Embedding a splitting field of reduced degree in the division algebra -/

noncomputable section

namespace Langlands.CentralDivision

open Module
open Langlands.Brauer
open scoped TensorProduct

universe u

variable (K D L : Type u) [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
  [Field L] [Algebra K L] [FiniteDimensional K L]
  (hdegree : Module.finrank K L = CentralSimple.reducedDegree K D)

include hdegree in
private theorem nonempty_embedding_of_split
    (hSplit : IsSplit (baseChange L (divisionAlgebraCSA K D))) :
    Nonempty (L →ₐ[K] D) := by
  obtain ⟨m, _, ⟨c⟩⟩ := hSplit
  change (L ⊗[K] D) ≃ₐ[L] Matrix (Fin m) (Fin m) L at c
  have hdim := c.toLinearEquiv.finrank_eq
  rw [Module.finrank_baseChange, Module.finrank_matrix, Fintype.card_fin,
    Module.finrank_self, mul_one, CentralSimple.finrank_eq_reducedDegree_mul_self] at hdim
  have hm : CentralSimple.reducedDegree K D = m := Nat.mul_self_inj.mp hdim
  let W := Fin m → L
  let f : D →ₐ[K] Module.End L W :=
    ((c.trans Matrix.toLinAlgEquiv').restrictScalars K).toAlgHom.comp
      Algebra.TensorProduct.includeRight
  let : Module D W := Module.compHom W f.toRingHom
  let : IsScalarTower K D W := ⟨fun a d x => by
    change f (a • d) x = a • f d x
    rw [map_smul]
    rfl⟩
  let : FiniteDimensional D W := Module.Finite.of_restrictScalars_finite K D W
  have hW : Module.finrank K W = Module.finrank K D := by
    rw [← Module.finrank_mul_finrank K L W, hdegree,
      CentralSimple.finrank_eq_reducedDegree_mul_self K D]
    change CentralSimple.reducedDegree K D * Module.finrank L (Fin m → L) =
      CentralSimple.reducedDegree K D * CentralSimple.reducedDegree K D
    rw [Module.finrank_fin_fun, hm]
  have hW₁ : Module.finrank D W = 1 := by
    apply Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := K) (M := D))
    rw [Module.finrank_mul_finrank K D W, hW, mul_one]
  obtain ⟨e⟩ := nonempty_linearEquiv_of_finrank_eq_one hW₁
  have hcomm (a : L) (d : D) (x : W) : d • (a • x) = a • (d • x) := (f d).map_smul a x
  let w : W := e 1
  let ι : L → D := fun a => e.symm (a • w)
  have he_ι (a : L) : e (ι a) = a • w := e.apply_symm_apply _
  have he_mul (x y : D) : e (x * y) = x • e y := e.map_smul x y
  refine ⟨{ toFun := ι
            map_one' := ?_
            map_mul' := ?_
            map_zero' := ?_
            map_add' := ?_
            commutes' := ?_ }⟩
  · apply e.injective
    rw [he_ι, one_smul]
  · intro a b
    apply e.injective
    rw [he_ι, he_mul, he_ι, hcomm]
    have hw : ι a • w = a • w := by
      rw [← he_mul, mul_one, he_ι]
    rw [hw, ← mul_smul, mul_comm b a]
  · apply e.injective
    rw [he_ι, zero_smul, map_zero]
  · intro a b
    apply e.injective
    rw [he_ι, map_add, he_ι, he_ι, add_smul]
  · intro a
    apply e.injective
    rw [he_ι, IsScalarTower.algebraMap_smul L]
    change a • e (1 : D) = e (algebraMap K D a)
    rw [← IsScalarTower.algebraMap_smul D, ← he_mul, mul_one]

/-- A splitting extension of degree equal to the reduced degree embeds in
the original division algebra. The embedding comes from scalar multiplication
on the rank-one division module defined by the splitting chart. -/
def embeddingOfSplitOfReducedDegree
    (hSplit : IsSplit (baseChange L (divisionAlgebraCSA K D))) : L →ₐ[K] D :=
  (nonempty_embedding_of_split K D L hdegree hSplit).some

end Langlands.CentralDivision
