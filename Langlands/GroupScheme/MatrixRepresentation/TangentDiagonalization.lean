import Langlands.GroupScheme.MatrixRepresentation.ToralTangent
import Langlands.GroupScheme.Reductive.CharZeroSemisimplicity.NilpotentIdeal
import Mathlib.LinearAlgebra.Eigenspace.Pi

/-! # Simultaneous diagonalization of actual tangent matrices -/

noncomputable section

universe u

open AlgebraicGeometry Module
open scoped Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] {n : ℕ}

/-- A single basis consists of eigenvectors for all actual tangent matrices
of a finite representation of a positive-characteristic linearly reductive group. -/
theorem exists_tangentEigenbasis_of_linearlyReductive
    (p : ℕ) [CharP k p] (hp : p ≠ 0)
    (hG : ∀ d (σ : MatrixRepresentation G (Fin d)), σ.IsSemisimple)
    (ρ : MatrixRepresentation G (Fin n)) :
    ∃ b : Basis (Fin n) k (Fin n → k), ∀ (X : lieKernel G k) (j : Fin n),
      ∃ c : k, Matrix.toLin' (ρ.tangentMatrix k X) (b j) = c • b j := by
  classical
  let f (X : lieKernel G k) : Module.End k (Fin n → k) :=
    Matrix.toLinAlgEquiv' (ρ.tangentMatrix k X)
  have hcomm : Pairwise fun X Y => Commute (f X) (f Y) := fun X Y _ =>
    (commute_tangentMatrix_of_linearlyReductive p hp hG ρ X Y).map Matrix.toLinAlgEquiv'
  have hsem (X : lieKernel G k) : (f X).IsSemisimple :=
    isSemisimple_tangentMatrix_of_linearlyReductive p hp hG ρ X
  have hmax (X : lieKernel G k) : ⨆ μ : k, (f X).maxGenEigenspace μ = ⊤ := by
    simp_rw [(hsem X).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace]
    exact (hsem X).iSup_eigenspace_eq_top
  have hspan := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    f hcomm hmax
  simp_rw [(hsem _).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at hspan
  let s : Set (Fin n → k) := ⋃ χ : lieKernel G k → k, ↑(⨅ X, (f X).eigenspace (χ X))
  have hs : Submodule.span k s = ⊤ := by
    simpa only [s, Submodule.span_iUnion, Submodule.span_eq] using hspan
  obtain ⟨t, ht, hts, hindep⟩ := exists_linearIndependent k s
  let b : Basis t k (Fin n → k) := Basis.mk hindep (by
    rw [Subtype.range_coe_subtype]
    change ⊤ ≤ Submodule.span k t
    rw [hts, hs])
  let e := b.indexEquiv (Pi.basisFun k (Fin n))
  refine ⟨b.reindex e, ?_⟩
  intro X j
  rw [Basis.reindex_apply, Basis.mk_apply]
  have hv : (↑(e.symm j) : Fin n → k) ∈ s := ht (e.symm j).property
  obtain ⟨χ, hχ⟩ := Set.mem_iUnion.mp hv
  exact ⟨χ X, Module.End.mem_eigenspace_iff.mp ((iInf_le (fun Z => (f Z).eigenspace (χ Z)) X) hχ)⟩

/-- Conjugation by the basis-coordinate point makes every actual tangent matrix diagonal. -/
theorem exists_conjugate_tangentMatrix_diagonal_of_linearlyReductive
    (p : ℕ) [CharP k p] (hp : p ≠ 0)
    (hG : ∀ d (σ : MatrixRepresentation G (Fin d)), σ.IsSemisimple)
    (ρ : MatrixRepresentation G (Fin n)) :
    ∃ b : Basis (Fin n) k (Fin n → k), ∀ (X : lieKernel G k) (i j : Fin n), i ≠ j →
      (ρ.conjugate (basisCoordinatePoint b)).tangentMatrix k X i j = 0 := by
  obtain ⟨b, hb⟩ := exists_tangentEigenbasis_of_linearlyReductive p hp hG ρ
  refine ⟨b, fun X i j hij => ?_⟩
  obtain ⟨c, hc⟩ := hb X j
  rw [conjugate_basisCoordinatePoint_tangentMatrix_apply, hc, map_smul, Basis.repr_self,
    Finsupp.smul_apply, Finsupp.single_eq_of_ne hij, smul_zero]

end Langlands.GroupScheme.MatrixRepresentation
