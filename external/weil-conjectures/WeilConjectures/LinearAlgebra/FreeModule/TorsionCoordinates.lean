/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Coordinates of a finitely generated module modulo torsion

Let `M` be a finitely generated module over a principal ideal domain `R`. Then `M / torsion` is
free of some rank `r`; lifting a basis gives `b₁, …, bᵣ ∈ M` and coordinate functionals
`c₁, …, cᵣ : M → R` such that `m - ∑ cᵢ(m) bᵢ` lies in the torsion submodule, which is killed
by a single nonzero `d ∈ R`. When `R` is a topological ring and `M` carries the module topology,
the coordinates are continuous (`IsModuleTopology.exists_coord_smul_sub_sum_eq_zero`).
-/

@[expose] public section

open Module

namespace IsModuleTopology

variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M]
  [Module R M] [Module.Finite R M] [TopologicalSpace R] [IsTopologicalRing R]
  [TopologicalSpace M] [IsModuleTopology R M]

/-- **Coordinates modulo torsion**: a finitely generated module `M` over a principal ideal
domain has elements `b₁, …, bᵣ`, a basis modulo torsion, and continuous linear coordinates
`c₁, …, cᵣ` such that `d • (m - ∑ cᵢ(m) • bᵢ) = 0` for all `m` and a fixed nonzero `d`. -/
theorem exists_coord_smul_sub_sum_eq_zero :
    ∃ (b : Fin (finrank R (M ⧸ Submodule.torsion R M)) → M)
      (c : Fin (finrank R (M ⧸ Submodule.torsion R M)) → C(M, R)) (d : R),
      LinearIndependent R ((Submodule.torsion R M).mkQ ∘ b) ∧ d ≠ 0 ∧
      ∀ m : M, d • (m - ∑ i, c i m • b i) = 0 := by
  let N := Submodule.torsion R M
  let B := Module.finBasis R (M ⧸ N)
  choose b hb using fun i ↦ Submodule.Quotient.mk_surjective N (B i)
  let c (i : Fin _) : C(M, R) :=
    ⟨B.coord i ∘ₗ N.mkQ, continuous_of_linearMap (B.coord i ∘ₗ N.mkQ)⟩
  obtain ⟨d, hdN, hd⟩ := Submodule.annihilator_top_inter_nonZeroDivisors
    (Submodule.torsion_isTorsion (R := R) (M := M))
  refine ⟨b, c, d, ?_, nonZeroDivisors.ne_zero hd, fun m ↦ ?_⟩
  · convert B.linearIndependent
    ext i
    exact hb i
  have hmem : m - ∑ i, c i m • b i ∈ N := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]
    simp only [map_smul, Submodule.mkQ_apply, hb]
    rw [sub_eq_zero]
    exact (B.sum_repr (Submodule.Quotient.mk m)).symm
  have := Submodule.mem_annihilator.1 hdN ⟨_, hmem⟩ Submodule.mem_top
  exact congrArg Subtype.val this

end IsModuleTopology
