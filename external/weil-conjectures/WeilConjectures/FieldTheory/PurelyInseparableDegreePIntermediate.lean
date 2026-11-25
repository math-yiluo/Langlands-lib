/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.FieldTheory.PurelyInseparablePthRootTower

/-!
# A degree-p final step in a finite purely inseparable extension

Source: Stacks Project, More on Algebra, Tag 07PR, proof, induction paragraph;
Fields, Tags 09HI and 09G9.
(blueprint: lem-weil-pbc-finite-purely-inseparable-degree-p-intermediate)
-/

@[expose] public section

universe u v

namespace IsPurelyInseparable

/-- A nontrivial finite purely inseparable extension in positive characteristic has a
degree-`p` final step obtained by adjoining a `p`th root.
Source: Stacks Project, Tag 07PR, proof, induction paragraph, with Tags 09HI and 09G9.
(blueprint: lem-weil-pbc-finite-purely-inseparable-degree-p-intermediate)

Proof: use the pth-root tower of Tag 09HI
(`lem-weil-pbc-purely-inseparable-pth-root-tower`). Its length is positive because a
length-zero tower has degree one. Take M to be its penultimate field and z its last
generator. The last step gives L = M(z), z^p in M, and [L:M] = p. The field M is a
finite-dimensional K-subspace of L. Every element of M has a p-power in K, since it is
an element of L; thus M/K is finite purely inseparable
(`def-weil-pbc-finite-purely-inseparable-extension`). Degree multiplicativity, Tag 09G9
(`lem-weil-pbc-field-degree-multiplicativity`), gives [L:K] = p[M:K]. Since p >= 2
and [M:K] >= 1, this is strictly greater than [M:K]. -/
theorem exists_degree_p_intermediate (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [Module.Finite K L] [IsPurelyInseparable K L]
    (p : ℕ) [CharP K p] (hp : 0 < p) (hdeg : 1 < Module.finrank K L) :
    ∃ (M : IntermediateField K L) (z : L),
      Module.Finite K M ∧ IsPurelyInseparable K M ∧
      Module.finrank K M < Module.finrank K L ∧
      IntermediateField.adjoin M ({z} : Set L) = ⊤ ∧
      (∃ f : M, z ^ p = (f : L)) ∧ Module.finrank M L = p := by
  set_option linter.style.haveILetI false in
  letI : Fact (Nat.Prime p) :=
    ⟨(CharP.char_is_prime_or_zero K p).resolve_right hp.ne'⟩
  obtain ⟨n, α, _, _, _, _, hfinal⟩ := exists_pth_root_tower K L p
  have hne : (⊥ : IntermediateField K L) ≠ ⊤ := by
    intro h
    have hfin : Module.finrank K L = 1 := by
      calc
        Module.finrank K L = Module.finrank (⊥ : IntermediateField K L) L :=
          (IntermediateField.finrank_bot' (F := K) (E := L)).symm
        _ = Module.finrank (⊤ : IntermediateField K L) L :=
          congrArg (fun (M : IntermediateField K L) =>
            Module.finrank M L) h
        _ = 1 := IntermediateField.finrank_top (F := K) (E := L)
    omega
  obtain ⟨M, z, hn, hM_eq, hz, htop, hMfin, hMpi, hlt, hadj, hdegM, hf, _⟩ := hfinal hne
  refine ⟨M, z, hMfin, hMpi, hlt, ?_, ?_, hdegM⟩
  · apply top_unique
    intro x hx
    exact hadj x
  · obtain ⟨f, hf⟩ := hf
    refine ⟨f, ?_⟩
    exact hf.symm

end IsPurelyInseparable
