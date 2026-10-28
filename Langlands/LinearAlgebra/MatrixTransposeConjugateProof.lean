import Langlands.LinearAlgebra.MatrixTransposeConjugateStatement
import Langlands.LinearAlgebra.CyclicQuotientPairingProof
import Mathlib.Algebra.Module.PID
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.AnnihilatingPolynomial
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Charpoly.Basic

/-!
# Every square matrix over a field is conjugate to its transpose

The polynomial-module structure theorem transports cyclic quotient pairings to
an invariant nondegenerate bilinear form. Its Gram matrix gives the conjugator.
-/

namespace Langlands

open Polynomial
open _root_.LinearMap (BilinForm)
open scoped DirectSum

universe uK uV uI

private def productPairing {K : Type uK} [Field K] {ι : Type uI} [Fintype ι]
    {M : ι → Type uV} [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    (B : ∀ i, BilinForm K (M i)) : BilinForm K (∀ i, M i) :=
  ∑ i, (B i).comp (LinearMap.proj i) (LinearMap.proj i)

private theorem productPairing_apply {K : Type uK} [Field K] {ι : Type uI} [Fintype ι]
    {M : ι → Type uV} [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    (B : ∀ i, BilinForm K (M i)) (u v : ∀ i, M i) :
    productPairing B u v = ∑ i, B i (u i) (v i) := by
  simp [productPairing, BilinForm.comp_apply]

private theorem productPairing_nondegenerate {K : Type uK} [Field K]
    {ι : Type uI} [Fintype ι] {M : ι → Type uV}
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    (B : ∀ i, BilinForm K (M i)) (hB : ∀ i, (B i).Nondegenerate) :
    (productPairing B).Nondegenerate := by
  classical
  constructor
  · intro u hu
    funext i
    apply (hB i).1
    intro v
    have h := hu (Pi.single i v)
    rw [productPairing_apply, Finset.sum_eq_single i] at h
    · simpa using h
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp
  · intro v hv
    funext i
    apply (hB i).2
    intro u
    have h := hv (Pi.single i u)
    rw [productPairing_apply, Finset.sum_eq_single i] at h
    · simpa using h
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp

private theorem pairing_of_cyclic_pairings {K : Type uK} [Field K]
    (hcyclic : ∀ (q : K[X]), q ≠ 0 → ∃ B : BilinForm K (AdjoinRoot q),
      B.IsSymm ∧ B.Nondegenerate ∧ ∀ a u v, B (a * u) v = B u (a * v))
    {M : Type uV} [AddCommGroup M] [Module K M] [Module K[X] M]
    [IsScalarTower K K[X] M] [Module.Finite K[X] M]
    (hM : Module.IsTorsion K[X] M) :
    ∃ B : BilinForm K M, B.Nondegenerate ∧
      ∀ u v, B ((X : K[X]) • u) v = B u ((X : K[X]) • v) := by
  classical
  obtain ⟨ι, inst, p, hp, e, ⟨E⟩⟩ := Module.equiv_directSum_of_isTorsion hM
  let Q : ι → Type uK := fun i => K[X] ⧸ K[X] ∙ p i ^ e i
  have hc : ∀ i, ∃ B : BilinForm K (Q i),
      B.IsSymm ∧ B.Nondegenerate ∧ ∀ a u v, B (a * u) v = B u (a * v) := by
    intro i
    exact hcyclic (p i ^ e i) (pow_ne_zero _ (hp i).ne_zero)
  choose B hsym hnd hbal using hc
  let Fp : M ≃ₗ[K[X]] (∀ i, Q i) := E.trans (DFinsupp.linearEquivFunOnFintype (R := K[X]))
  let F : M ≃ₗ[K] (∀ i, Q i) := Fp.restrictScalars K
  let C : BilinForm K M := (productPairing B).comp F.toLinearMap F.toLinearMap
  refine ⟨C, ?_, ?_⟩
  · constructor
    · intro u hu
      apply F.injective
      rw [map_zero]
      apply (productPairing_nondegenerate B hnd).1
      intro v
      obtain ⟨v, rfl⟩ := F.surjective v
      exact hu v
    · intro v hv
      apply F.injective
      rw [map_zero]
      apply (productPairing_nondegenerate B hnd).2
      intro u
      obtain ⟨u, rfl⟩ := F.surjective u
      exact hv u
  · intro u v
    change productPairing B (Fp ((X : K[X]) • u)) (Fp v) =
      productPairing B (Fp u) (Fp ((X : K[X]) • v))
    rw [Fp.map_smul, Fp.map_smul, productPairing_apply, productPairing_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact hbal i (Ideal.Quotient.mk _ X) (Fp u i) (Fp v i)

private theorem endomorphism_pairing_of_cyclic_pairings {K : Type uK} [Field K]
    (hcyclic : ∀ (q : K[X]), q ≠ 0 → ∃ B : BilinForm K (AdjoinRoot q),
      B.IsSymm ∧ B.Nondegenerate ∧ ∀ a u v, B (a * u) v = B u (a * v))
    {V : Type uV} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) :
    ∃ B : BilinForm K V, B.Nondegenerate ∧ ∀ u v, B (f u) v = B u (f v) := by
  classical
  have hT : Module.IsTorsion K[X] (Module.AEval' f) := by
    intro u
    refine ⟨⟨f.charpoly, mem_nonZeroDivisors_of_ne_zero f.charpoly_monic.ne_zero⟩, ?_⟩
    change (aeval f f.charpoly) ((Module.AEval'.of f).symm u) = 0
    rw [f.aeval_self_charpoly]
    rfl
  obtain ⟨B, hB, hf⟩ := pairing_of_cyclic_pairings hcyclic hT
  let F := Module.AEval'.of f
  let C : BilinForm K V := B.comp F.toLinearMap F.toLinearMap
  refine ⟨C, ?_, ?_⟩
  · constructor
    · intro u hu
      apply F.injective
      rw [map_zero]
      apply hB.1
      intro v
      obtain ⟨v, rfl⟩ := F.surjective v
      exact hu v
    · intro v hv
      apply F.injective
      rw [map_zero]
      apply hB.2
      intro u
      obtain ⟨u, rfl⟩ := F.surjective u
      exact hv u
  · intro u v
    change B (F (f u)) (F v) = B (F u) (F (f v))
    rw [← Module.AEval'.X_smul_of, ← Module.AEval'.X_smul_of]
    exact hf (F u) (F v)

private theorem conjugate_of_pairing {K : Type uK} [Field K] (n : ℕ)
    (x : Matrix (Fin n) (Fin n) K) (B : BilinForm K (Fin n → K))
    (hB : B.Nondegenerate)
    (hself : ∀ u v, B (x.mulVecLin u) v = B u (x.mulVecLin v)) :
    ∃ g : Matrix.GeneralLinearGroup (Fin n) K,
      (g : Matrix (Fin n) (Fin n) K) * x * ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = x.transpose := by
  have hdet : B.toMatrix'.det ≠ 0 :=
    Matrix.nondegenerate_iff_det_ne_zero.mp
      (BilinForm.nondegenerate_toMatrix'_iff.mpr hB)
  let g := Matrix.GeneralLinearGroup.mkOfDetNeZero B.toMatrix' hdet
  have hcomp : B.compLeft x.mulVecLin = B.compRight x.mulVecLin := by
    exact BilinForm.ext hself
  have hmul : x.transpose * B.toMatrix' = B.toMatrix' * x := by
    have hx : LinearMap.toMatrix' x.mulVecLin = x := LinearMap.toMatrix'_toLin' x
    have h := congrArg BilinForm.toMatrix' hcomp
    simpa only [BilinForm.toMatrix'_compLeft, BilinForm.toMatrix'_compRight,
      hx] using h
  refine ⟨g, ?_⟩
  change B.toMatrix' * x * ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = x.transpose
  rw [← hmul, mul_assoc]
  change x.transpose * ((g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) = x.transpose
  rw [Units.mul_inv, mul_one]

/-- Assemble transpose conjugacy from balanced pairings on cyclic quotients. -/
theorem matrixTransposeConjugate_of_cyclic_pairings
    (hcyclic : CyclicQuotientPairingStatement.{uK}) :
    MatrixTransposeConjugateStatement.{uK} := by
  intro K _ n x
  obtain ⟨B, hB, hf⟩ := endomorphism_pairing_of_cyclic_pairings (hcyclic K) x.mulVecLin
  exact conjugate_of_pairing n x B hB hf

/-- Every square matrix over any field is conjugate to its transpose. -/
theorem matrixTransposeConjugate : MatrixTransposeConjugateStatement.{uK} :=
  matrixTransposeConjugate_of_cyclic_pairings cyclicQuotientPairing

end Langlands
