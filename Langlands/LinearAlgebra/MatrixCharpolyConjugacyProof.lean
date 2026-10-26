import Langlands.LinearAlgebra.MatrixCharpolyConjugacyStatement
import Langlands.LinearAlgebra.MatrixAEvalConjugacyProof
import Langlands.LinearAlgebra.PolynomialModuleBoundedCyclicDecompositionProof
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

namespace Langlands

universe uK

/-- Finitely many matrix conjugacy classes have a prescribed characteristic
polynomial, over any field. -/
theorem matrixCharpolyFiniteConjugacy :
    MatrixCharpolyFiniteConjugacyStatement.{uK} := by
  classical
  intro K _ n c
  by_cases hc : c = 0
  · refine ⟨∅, ?_⟩
    intro x hx
    exact False.elim (x.charpoly_monic.ne_zero (hx.trans hc))
  let D := {q : Polynomial K // q.Monic ∧ q ∣ c}
  let : Fintype D := Polynomial.fintypeSubtypeMonicDvd c hc
  let Code := (m : Fin (n + 1)) × (Fin m.val → D)
  let Model (a : Code) := (i : Fin a.1.val) → Polynomial K ⧸ Ideal.span {(a.2 i).val}
  let Realized := {a : Code // ∃ y : Matrix (Fin n) (Fin n) K,
    y.charpoly = c ∧ Nonempty (Module.AEval' y.mulVecLin ≃ₗ[Polynomial K] Model a)}
  let : Fintype Realized := Fintype.ofFinite Realized
  let rep (a : Realized) : Matrix (Fin n) (Fin n) K := a.property.choose
  refine ⟨Finset.univ.image rep, ?_⟩
  intro x hx
  have hann : Polynomial.aeval x.mulVecLin c = 0 := by
    rw [← hx, ← Matrix.charpoly_mulVecLin]
    exact LinearMap.aeval_self_charpoly _
  obtain ⟨m, q, hm, hq, ⟨e⟩⟩ :=
    polynomialModuleBoundedCyclicDecomposition K (Fin n → K) x.mulVecLin c hc hann
  have hmn : m ≤ n := by simpa only [Module.finrank_fin_fun] using hm
  let a : Code := ⟨⟨m, Nat.lt_succ_of_le hmn⟩, fun i => ⟨q i, hq i⟩⟩
  have he : Nonempty (Module.AEval' x.mulVecLin ≃ₗ[Polynomial K] Model a) := ⟨e⟩
  let r : Realized := ⟨a, x, hx, he⟩
  refine ⟨rep r, Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩, ?_⟩
  obtain ⟨ey⟩ := r.property.choose_spec.2
  exact matrixAEvalConjugacy K n x (rep r) (e.trans ey.symm)

end Langlands
