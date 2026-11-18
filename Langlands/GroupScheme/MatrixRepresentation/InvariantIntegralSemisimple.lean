import Langlands.GroupScheme.MatrixRepresentation.StableComplements
import Langlands.GroupScheme.MatrixRepresentation.InvariantIntegralSplitting

/-! # Invariant integration and sums of actual simple subrepresentations -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Every nonzero stable subspace contains a nonzero simple stable subspace. -/
theorem exists_minimal_nonzero_stableSubspace_le
    (ρ : MatrixRepresentation G n) {U : Submodule k (n → k)}
    (hU : ρ.IsStableSubspace U) (hU0 : U ≠ ⊥) :
    ∃ V : Submodule k (n → k), ρ.IsStableSubspace V ∧ V ≠ ⊥ ∧ V ≤ U ∧
      ∀ W : Submodule k (n → k), ρ.IsStableSubspace W → W ≤ V →
        W = ⊥ ∨ W = V := by
  classical
  let P : ℕ → Prop := fun d =>
    ∃ V : Submodule k (n → k),
      ρ.IsStableSubspace V ∧ V ≠ ⊥ ∧ V ≤ U ∧ Module.finrank k V = d
  have hP : ∃ d, P d := ⟨_, U, hU, hU0, le_rfl, rfl⟩
  obtain ⟨V, hV, hV0, hVU, hdim⟩ := Nat.find_spec hP
  refine ⟨V, hV, hV0, hVU, ?_⟩
  intro W hW hWV
  by_cases hW0 : W = ⊥
  · exact Or.inl hW0
  · right
    apply Submodule.eq_of_le_of_finrank_le hWV
    rw [hdim]
    exact Nat.find_min' hP ⟨W, hW, hW0, hWV.trans hVU, rfl⟩

/-- Stable complements imply the sum-of-simple-subspaces definition of
semisimplicity in finite dimension. -/
theorem isSemisimple_of_stable_complements (ρ : MatrixRepresentation G n)
    (hcomp : ∀ W : Submodule k (n → k), ρ.IsStableSubspace W →
      ∃ U : Submodule k (n → k), ρ.IsStableSubspace U ∧ IsCompl W U) :
    ρ.IsSemisimple := by
  let S : Set (Submodule k (n → k)) :=
    {W | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
      ∀ U : Submodule k (n → k), ρ.IsStableSubspace U → U ≤ W → U = ⊥ ∨ U = W}
  have hS : ρ.IsStableSubspace (sSup S) :=
    IsStableSubspace.sSup (fun W hW => hW.1)
  obtain ⟨U, hU, hSU⟩ := hcomp (sSup S) hS
  have hU0 : U = ⊥ := by
    by_contra hU0
    obtain ⟨V, hV, hV0, hVU, hmin⟩ :=
      exists_minimal_nonzero_stableSubspace_le ρ hU hU0
    have hVS : V ≤ sSup S := le_sSup (show V ∈ S from ⟨hV, hV0, hmin⟩)
    apply hV0
    exact bot_unique ((le_inf hVS hVU).trans_eq hSU.inf_eq_bot)
  have h := hSU.sup_eq_top
  rw [hU0, sup_bot_eq] at h
  exact h

/-- A normalized invariant coordinate integral makes every finite coordinate
representation semisimple on the original ground field. -/
theorem isSemisimple_of_invariantIntegral [IsAffineHom G.X.hom]
    (ρ : MatrixRepresentation G n) (I : CoordinateIntegration.InvariantIntegral G) :
    ρ.IsSemisimple :=
  isSemisimple_of_stable_complements ρ
    (fun _ hW => hW.exists_stable_complement I)

end Langlands.GroupScheme.MatrixRepresentation
