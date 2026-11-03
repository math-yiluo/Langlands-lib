import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SigmaProduct
import Langlands.Group.GL.Blocks

/-! # Lemma II.3.1 for the standard block parabolic subgroups of `GL_n`

For `G = GL_n(F)` with its standard embedding `τ = id` and an ordered block shape `B` of
`n`, the Levi subgroup `B.leviSubgroup F` (block diagonal matrices) and the unipotent radical
`B.unipotentSubgroup F` (block upper unitriangular matrices) of the Library's module
`Langlands.Group.GL.Blocks` have the block form required by
`sigmaProductBound_height`. Hence Waldspurger's Lemma II.3.1 holds for them, with
`σ = log ‖·‖` the height of `Height`.
-/

noncomputable section

namespace Langlands.HarishChandraSchwartz

open Langlands.GeneralLinear

universe v

variable {F : Type v} [NormedField F] {n : ℕ} (B : BlockShape n)

theorem glBlock_indexEquiv (p : B.Index) : B.coordinateBlock (B.indexEquiv p) = p.1 := by
  simp [BlockShape.coordinateBlock]

/-- The elements of the block diagonal Levi subgroup are block diagonal. -/
theorem isBlockDiagonal_of_mem_leviSubgroup {m : GeneralLinear n F}
    (hm : m ∈ B.leviSubgroup F) :
    IsBlockDiagonal (B.coordinateBlock) (m : Matrix (Fin n) (Fin n) F) := by
  obtain ⟨m', rfl⟩ := hm
  intro i j hij
  obtain ⟨⟨p, a⟩, rfl⟩ := B.indexEquiv.surjective i
  obtain ⟨⟨q, b⟩, rfl⟩ := B.indexEquiv.surjective j
  rw [glBlock_indexEquiv, glBlock_indexEquiv] at hij
  exact B.leviEmbedding_apply_ne F m' a b hij

/-- The elements of the block unipotent radical are block upper unitriangular. -/
theorem isBlockUnipotent_of_mem_unipotentSubgroup {u : GeneralLinear n F}
    (hu : u ∈ B.unipotentSubgroup F) :
    IsBlockUnipotent (B.coordinateBlock) (u : Matrix (Fin n) (Fin n) F) := by
  rw [B.mem_unipotentSubgroup_iff F] at hu
  obtain ⟨hpar, hdiag⟩ := hu
  intro i j hji
  obtain ⟨⟨p, a⟩, rfl⟩ := B.indexEquiv.surjective i
  obtain ⟨⟨q, b⟩, rfl⟩ := B.indexEquiv.surjective j
  rw [glBlock_indexEquiv, glBlock_indexEquiv] at hji
  rcases hji.lt_or_eq with hlt | heq
  · have h0 : u (B.index p a) (B.index q b) = 0 := (B.mem_parabolic_iff F u).mp hpar p q a b hlt
    have hne : B.indexEquiv ⟨p, a⟩ ≠ B.indexEquiv ⟨q, b⟩ := by
      intro h
      have := congrArg Sigma.fst (B.indexEquiv.injective h)
      exact absurd this (ne_of_gt hlt)
    rw [ite_eq_right_iff.mpr (fun h => absurd h hne)]
    exact h0
  · subst heq
    have h1 := hdiag q a b
    change u (B.indexEquiv ⟨q, a⟩) (B.indexEquiv ⟨q, b⟩) = _ at h1
    rw [h1]
    by_cases hab : a = b
    · rw [ite_eq_left_iff.mpr (fun h => absurd hab h),
        ite_eq_left_iff.mpr (fun h => absurd (congrArg (fun x => B.indexEquiv ⟨q, x⟩) hab) h)]
    · have hne : B.indexEquiv ⟨q, a⟩ ≠ B.indexEquiv ⟨q, b⟩ := by
        intro h
        have := B.indexEquiv.injective h
        exact hab (by simpa using this)
      rw [ite_eq_right_iff.mpr (fun h => absurd h hab),
        ite_eq_right_iff.mpr (fun h => absurd h hne)]

variable [IsUltrametricDist F] [NeZero n]

/-- Waldspurger, Lemma II.3.1, for the standard block parabolic `P = M U` of `GL_n(F)` and
the height of the standard embedding: `SigmaProductBound (B.leviSubgroup F)
(B.unipotentSubgroup F) (height (MonoidHom.id _))`. -/
theorem sigmaProductBound_glBlock :
    SigmaProductBound (B.leviSubgroup F) (B.unipotentSubgroup F)
      (height (MonoidHom.id (GeneralLinear n F))) := by
  refine sigmaProductBound_height (MonoidHom.id _) 1 (B.coordinateBlock) (fun m hm => ?_)
    (fun u hu => ?_)
  · simpa using isBlockDiagonal_of_mem_leviSubgroup B hm
  · simpa using isBlockUnipotent_of_mem_unipotentSubgroup B hu

end Langlands.HarishChandraSchwartz
