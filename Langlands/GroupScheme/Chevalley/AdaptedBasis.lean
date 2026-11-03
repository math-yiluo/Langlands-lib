import Langlands.GroupScheme.Chevalley.ExteriorLine
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Finite bases adapted to a subspace -/

noncomputable section

open Module

namespace Langlands.GroupScheme.Chevalley

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]
  [Module.Finite K M]

/-- A finite-dimensional vector space has a finite basis in which any chosen subspace
is spanned by an increasing selection of basis vectors. -/
theorem exists_adapted_basis (W : Submodule K M) :
    ∃ (N d : ℕ) (b : Basis (Fin N) K M) (s : Fin d ↪o Fin N),
      W = coordinateSpan b s.toEmbedding := by
  classical
  obtain ⟨U, hU⟩ := W.exists_isCompl
  let d := Module.finrank K W
  let c := Module.finrank K U
  let w := Module.finBasis K W
  let u := Module.finBasis K U
  let b : Basis (Fin (d + c)) K M :=
    ((w.prod u).map (W.prodEquivOfIsCompl U hU)).reindex finSumFinEquiv
  let s : Fin d ↪o Fin (d + c) := Fin.castAddOrderEmb c
  have hb (i : Fin d) : b (s i) = (w i : M) := by
    simp only [b, Basis.reindex_apply, Basis.map_apply]
    change W.prodEquivOfIsCompl U hU
      ((w.prod u) (finSumFinEquiv.symm (Fin.castAdd c i))) = _
    rw [finSumFinEquiv_symm_apply_castAdd]
    simp [Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
  refine ⟨d + c, d, b, s, le_antisymm ?_ ?_⟩
  · intro x hx
    have hsum := congrArg Subtype.val (w.sum_repr (⟨x, hx⟩ : W))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
    rw [← hsum]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (hb i ▸ Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change b (s i) ∈ W
    rw [hb]
    exact (w i).2

omit [Module.Finite K M] in
/-- The adapted basis can be expressed in an arbitrary ambient vector space while only
the containing subspace is finite dimensional. -/
theorem exists_adapted_subspace_basis (V W : Submodule K M) [Module.Finite K V]
    (hWV : W ≤ V) :
    ∃ (N d : ℕ) (b : Basis (Fin N) K V) (s : Fin d ↪o Fin N),
      W = Submodule.span K (Set.range fun i : Fin d => (b (s i) : M)) := by
  let P := W.comap V.subtype
  obtain ⟨N, d, b, s, hP⟩ := exists_adapted_basis P
  refine ⟨N, d, b, s, ?_⟩
  have hmap : W = P.map V.subtype := by
    ext x
    constructor
    · intro hx
      exact ⟨⟨x, hWV hx⟩, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  rw [hmap, hP, coordinateSpan, Submodule.map_span, ← Set.range_comp]
  rfl

end Langlands.GroupScheme.Chevalley
