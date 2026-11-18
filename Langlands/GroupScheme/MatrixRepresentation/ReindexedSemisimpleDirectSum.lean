import Langlands.GroupScheme.MatrixRepresentation.SemisimpleDirectSum
import Langlands.GroupScheme.Chevalley.RepresentationExtension

/-! # Semisimplicity of reindexed direct sums of actual representations -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

section SimpleRange

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The image of an injective intertwiner from a simple representation is a
nonzero simple stable subspace of its target. -/
theorem Intertwines.simple_range {ρ : MatrixRepresentation G n}
    {σ : MatrixRepresentation G m} {C : Matrix m n k}
    (hC : Intertwines ρ σ C) (hi : Function.Injective C.mulVecLin)
    (hn : Nontrivial (n → k))
    (hs : ∀ V : Submodule k (n → k), ρ.IsStableSubspace V → V = ⊥ ∨ V = ⊤) :
    σ.IsStableSubspace (LinearMap.range C.mulVecLin) ∧
      LinearMap.range C.mulVecLin ≠ ⊥ ∧
      ∀ U : Submodule k (m → k), σ.IsStableSubspace U →
        U ≤ LinearMap.range C.mulVecLin → U = ⊥ ∨ U = LinearMap.range C.mulVecLin :=
  IsIrreducible.isSimpleStableSubspace_range (ρ := ρ) ⟨hn, hs⟩ hC hi

end SimpleRange

section DirectSum

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {I : Type} [Fintype I] [DecidableEq I] {n : I → Type}
  [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]

/-- The coordinate injection of a block into a finite direct sum. -/
def blockInclusion (i : I) : Matrix (Σ j, n j) (n i) k :=
  fun s a => if s = ⟨i, a⟩ then 1 else 0

omit [Fintype I] in
/-- A coordinate injection gives the prescribed vector on its own block. -/
theorem blockInclusion_mulVec (i : I) (v : n i → k) (a : n i) :
    (blockInclusion (k := k) (n := n) i *ᵥ v) ⟨i, a⟩ = v a := by
  simp [blockInclusion, Matrix.mulVec, dotProduct]

omit [Fintype I] in
/-- Coordinate injection is injective. -/
theorem blockInclusion_injective (i : I) :
    Function.Injective (blockInclusion (k := k) (n := n) i).mulVecLin := by
  intro v w h
  funext a
  have h' := congrFun h ⟨i, a⟩
  simpa only [Matrix.mulVecLin_apply, blockInclusion_mulVec] using h'

/-- The block injections intertwine the actual affine actions. -/
theorem intertwines_blockInclusion (ρ : ∀ i, MatrixRepresentation G (n i)) (i : I) :
    Intertwines (ρ i) (directSum ρ) (blockInclusion (k := k) (n := n) i) := by
  intro A x
  rw [directSum_affineMatrix_val]
  ext ⟨t, a⟩ b
  by_cases hti : t = i
  · subst t
    simp [Matrix.mul_apply, blockInclusion]
  · simp [Matrix.mul_apply, blockInclusion,
      Matrix.blockDiagonal'_apply, hti]

variable {J : Type} [Fintype J] [DecidableEq J]

omit [Fintype I] [Fintype J] in
/-- Reindexed block injections contain each reindexed coordinate basis vector. -/
theorem reindex_blockInclusion_mulVec_single (e : (Σ i, n i) ≃ J) (i : I) (a : n i) :
    (Matrix.reindex e (Equiv.refl (n i)) (blockInclusion (k := k) (n := n) i)).mulVecLin
      (Pi.single a 1) = Pi.single (e ⟨i, a⟩) 1 := by
  ext q
  by_cases hq : q = e ⟨i, a⟩
  · subst q
    simp [blockInclusion]
  · have hq' : e.symm q ≠ ⟨i, a⟩ := by
      intro hh
      apply hq
      simpa only [Equiv.apply_symm_apply] using congrArg e hh
    simp [blockInclusion, hq, hq']

/-- A finite direct sum of nonzero simple actual representations is semisimple
after any finite coordinate reindexing. -/
theorem semisimple_reindex_directSum (ρ : ∀ i, MatrixRepresentation G (n i))
    (hs : ∀ i, Nontrivial (n i → k) ∧
      ∀ V : Submodule k (n i → k), (ρ i).IsStableSubspace V → V = ⊥ ∨ V = ⊤)
    (e : (Σ i, n i) ≃ J) :
    sSup {W : Submodule k (J → k) |
      (Chevalley.reindexRepresentation e (CommRingCat.of k) (directSum ρ)).IsStableSubspace W ∧
        W ≠ ⊥ ∧ ∀ U : Submodule k (J → k),
          (Chevalley.reindexRepresentation e (CommRingCat.of k) (directSum ρ)).IsStableSubspace U →
            U ≤ W → U = ⊥ ∨ U = W} = ⊤ := by
  let σ := Chevalley.reindexRepresentation e (CommRingCat.of k) (directSum ρ)
  let C := fun i => Matrix.reindex e (Equiv.refl (n i))
    (blockInclusion (k := k) (n := n) i)
  have hC (i : I) : Intertwines (ρ i) σ (C i) :=
    Chevalley.intertwines_reindex_target e (ρ i) (directSum ρ)
      (blockInclusion i) (intertwines_blockInclusion ρ i)
  have hi (i : I) : Function.Injective (C i).mulVecLin :=
    Chevalley.reindexMatrix_injective (Equiv.refl (n i)) e
      (blockInclusion i) (blockInclusion_injective i)
  have hle (i : I) : LinearMap.range (C i).mulVecLin ≤
      sSup {W : Submodule k (J → k) | σ.IsStableSubspace W ∧ W ≠ ⊥ ∧
        ∀ U : Submodule k (J → k), σ.IsStableSubspace U → U ≤ W → U = ⊥ ∨ U = W} :=
    le_sSup ((hC i).simple_range (hi i) (hs i).1 (hs i).2)
  apply top_unique
  intro v _
  have hv : v = ∑ j : J, v j • (Pi.single j (1 : k) : J → k) := by
    funext j
    simp [Pi.single_apply]
  rw [hv]
  apply Submodule.sum_mem
  intro j _
  obtain ⟨⟨i, a⟩, rfl⟩ := e.surjective j
  apply Submodule.smul_mem
  apply hle i
  exact ⟨Pi.single a 1, reindex_blockInclusion_mulVec_single e i a⟩

end DirectSum

end Langlands.GroupScheme.MatrixRepresentation
