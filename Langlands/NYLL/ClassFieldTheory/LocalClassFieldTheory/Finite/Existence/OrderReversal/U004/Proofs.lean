import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups.U004.Proofs
/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 471, 14 November 2026: prove M402.004
(`exists_uniformizerPrincipalSubgroup_le_normSubgroup`, OrderReversal.lean,
lines 129–164 at fbd320cd8b1b06487c58227e92eb135794267709) against the
published target `exists_uniformizerPrincipalSubgroup_le_normSubgroupStatement`.
Prefix the namespace with Langlands.NYLL and give the theorem the published
closed statement as its type. The source's finite-index exponent (the index
of the norm subgroup, obtained from the Artin isomorphism
`abelianizationEquivNormQuotient`) is replaced by the degree `[L : K]`,
because the norm of `algebraMap K L ϖ` is `ϖ ^ [L : K]`. The principal-unit
bound uses the published openness theorem M257.007 and the canonical
M289.004 theorem `LocalFieldTheory.exists_fieldPrincipalUnits_le_of_isOpen`.
Integrator consolidated the former internal copy with this source API.
LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.OrderReversal.U004.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity.U007.Proofs
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Standard subgroups inside finite abelian norm subgroups (M402.004)

For a finite abelian extension `L/K` of a nonarchimedean local field and any
unit `ϖ` of `K`, the norm subgroup `N_{L/K}(Lˣ)` contains `⟨ϖ ^ d⟩ Uⁿ` with
`d = [L : K]` and some `n ≥ 1`: the power `ϖ ^ [L : K]` is the norm of `ϖ`
itself, and the norm subgroup is open, hence contains a deep principal-unit
group.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open LocalFieldTheory

/-- For a prescribed unit `ϖ`, the norm subgroup of a finite abelian
extension contains a standard subgroup `⟨ϖᵈ⟩ Uⁿ` for some positive
integers `d` and `n`; here `d = [L : K]`. -/
theorem exists_uniformizerPrincipalSubgroup_le_normSubgroup :
    exists_uniformizerPrincipalSubgroup_le_normSubgroupStatement := by
  intro K L _ _ _ _ _ _ _ _ ϖ
  obtain ⟨n, hn, hUn⟩ :=
    LocalFieldTheory.exists_fieldPrincipalUnits_le_of_isOpen K
      (localNormSubgroup K L) (localNormSubgroup_isOpen K L)
  refine ⟨Module.finrank K L, n, Module.finrank_pos, hn, ?_⟩
  apply sup_le
  · rw [Subgroup.zpowers_le]
    refine ⟨Units.map (algebraMap K L).toMonoidHom ϖ, ?_⟩
    ext
    simp only [normUnits, RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe,
      Algebra.norm_algebraMap, Units.val_pow_eq_pow_val]
  · exact hUn

end Langlands.NYLL.LocalClassFieldTheory
