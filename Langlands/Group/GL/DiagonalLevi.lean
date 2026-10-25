import Langlands.Group.GL.SingletonBlocks
import Langlands.Group.GL.Maps
import Langlands.Representation.Exponents.ParabolicPair

/-! Actual diagonal units inside every block Levi and permutation transport. -/
noncomputable section

namespace Langlands.GeneralLinear.BlockShape

universe uR
variable {n : ℕ} (R : Type uR) [CommRing R]

@[simp] theorem singletons_blockScalar_apply (a : Fin n → Rˣ) (i j : Fin n) :
    (singletons n).blockScalar R a i j = if i = j then (a i : R) else 0 := by
  change ((singletons n).leviEmbedding R (singletonLevi R a)).val i j = _
  rw [leviEmbedding_singletonLevi_val, Matrix.diagonal_apply]

variable (B : BlockShape n)

/-- The coordinate diagonal matrix, separated into the actual standard Levi blocks. -/
def diagonalLevi : (Fin n → Rˣ) →* B.Levi R where
  toFun a i := (singletons (B.size i)).blockScalar R (fun j => a (B.index i j))
  map_one' := by funext i; exact map_one _
  map_mul' a b := by funext i; exact map_mul _ _ _

/-- Embedding the blockwise diagonal coordinates recovers the ambient diagonal matrix. -/
theorem leviEmbedding_diagonalLevi (a : Fin n → Rˣ) :
    B.leviEmbedding R (B.diagonalLevi R a) = (singletons n).blockScalar R a := by
  apply Units.ext
  ext x y
  obtain ⟨⟨i, r⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, s⟩, rfl⟩ := B.indexEquiv.surjective y
  change B.leviEmbedding R (B.diagonalLevi R a) (B.index i r) (B.index j s) = _
  by_cases hij : i = j
  · subst j
    rw [leviEmbedding_apply_same]
    change (singletons (B.size i)).blockScalar R (fun k => a (B.index i k)) r s = _
    change ((singletons (B.size i)).leviEmbedding R
      (singletonLevi R (fun k => a (B.index i k)))).val r s =
      ((singletons n).leviEmbedding R (singletonLevi R a)).val (B.index i r) (B.index i s)
    rw [leviEmbedding_singletonLevi_val, leviEmbedding_singletonLevi_val]
    simp only [Matrix.diagonal_apply, (B.index i).injective.eq_iff]
  · rw [leviEmbedding_apply_ne _ _ _ _ _ hij]
    change 0 =
      ((singletons n).leviEmbedding R (singletonLevi R a)).val (B.index i r) (B.index j s)
    rw [leviEmbedding_singletonLevi_val, Matrix.diagonal_apply]
    have hne : B.index i r ≠ B.index j s := by
      intro h
      exact hij (congrArg Sigma.fst (B.indexEquiv.injective h))
    simp only [hne, ite_false]

/-- The actual fixed diagonal torus lies in every standard embedded Levi. -/
theorem singletonSplitComponent_le_leviSubgroup :
    (Exponents.ConjugateBlockPair.standard (R := R) (singletons n)).splitComponent ≤
      B.leviSubgroup R := by
  rintro x ⟨a, rfl⟩
  refine ⟨B.diagonalLevi R a, ?_⟩
  change B.leviEmbedding R (B.diagonalLevi R a) =
    (Exponents.ConjugateBlockPair.standard (R := R) (singletons n)).scalarMap a
  rw [Exponents.ConjugateBlockPair.standard_scalarMap]
  exact B.leviEmbedding_diagonalLevi R a

/-- A permutation transports the actual diagonal tuple by its inverse index map. -/
theorem permutation_conj_singletons_blockScalar (w : Equiv.Perm (Fin n))
    (a : Fin n → Rˣ) :
    permutation n R w * (singletons n).blockScalar R a * (permutation n R w)⁻¹ =
      (singletons n).blockScalar R (fun i => a (w⁻¹ i)) := by
  apply Units.ext
  ext i j
  rw [permutation_conjugate_entry]
  change ((singletons n).leviEmbedding R (singletonLevi R a)).val (w⁻¹ i) (w⁻¹ j) =
    ((singletons n).leviEmbedding R (singletonLevi R (fun k => a (w⁻¹ k)))).val i j
  rw [leviEmbedding_singletonLevi_val, leviEmbedding_singletonLevi_val]
  simp only [Matrix.diagonal_apply, Equiv.Perm.inv_def, w.symm.injective.eq_iff]

/-- Every permutation matrix normalizes the actual singleton-block split component. -/
theorem permutation_mem_singletonSplitComponent_normalizer (w : Equiv.Perm (Fin n)) :
    permutation n R w ∈ Subgroup.normalizer
      ((Exponents.ConjugateBlockPair.standard (R := R) (singletons n)).splitComponent :
        Set (GeneralLinear n R)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply le_antisymm
  · rintro _ ⟨x, ⟨a, rfl⟩, rfl⟩
    refine ⟨fun i => a (w⁻¹ i), ?_⟩
    change (Exponents.ConjugateBlockPair.standard (R := R) (singletons n)).scalarMap
      (fun i => a (w⁻¹ i)) = permutation n R w *
      (Exponents.ConjugateBlockPair.standard (R := R) (singletons n)).scalarMap a *
        (permutation n R w)⁻¹
    rw [Exponents.ConjugateBlockPair.standard_scalarMap]
    exact (permutation_conj_singletons_blockScalar R w a).symm
  · rintro _ ⟨a, rfl⟩
    refine ⟨(singletons n).blockScalar R (fun i => a (w i)), ?_, ?_⟩
    · refine ⟨fun i => a (w i), ?_⟩
      change (Exponents.ConjugateBlockPair.standard (R := R) (singletons n)).scalarMap
        (fun i => a (w i)) = _
      rw [Exponents.ConjugateBlockPair.standard_scalarMap]
      rfl
    change permutation n R w * _ * (permutation n R w)⁻¹ = _
    rw [permutation_conj_singletons_blockScalar]
    simp only [Exponents.ConjugateBlockPair.standard_scalarMap, Equiv.Perm.inv_def, Equiv.apply_symm_apply]
    rfl

end Langlands.GeneralLinear.BlockShape
