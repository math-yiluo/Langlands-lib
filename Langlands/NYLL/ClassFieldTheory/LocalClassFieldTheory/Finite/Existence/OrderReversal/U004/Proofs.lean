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
bound uses the published openness theorem M257.007 and a helper lemma in
`Langlands.NYLL.PortInternal.M402.D004`, adapted from the source proofs of
M289.003–004 (StandardOpenSubgroups.lean, lines 43–93) and of
`exists_maximalIdeal_pow_subset_nhds_zero` (PrincipalUnitQuotients.lean,
lines 160–185), merged into one proof over neighborhoods of zero in K.
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

namespace Langlands.NYLL.PortInternal.M402.D004

open Langlands.NYLL.LocalFieldTheory ValuativeRel
open scoped ValuativeRel

universe u

/-- Every open subgroup of the unit group of a nonarchimedean local field
contains a positive principal-unit group. This is the content of source
M289.003–004, proved here directly from the valuative neighborhood basis
of zero in `K`. -/
theorem exists_fieldPrincipalUnits_le_of_isOpen
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : Subgroup Kˣ) (hH : IsOpen (H : Set Kˣ)) :
    ∃ n : Nat, 1 ≤ n ∧ fieldPrincipalUnits K n ≤ H := by
  obtain ⟨V, hVopen, hV⟩ := Units.isEmbedding_val₀.isOpen_iff.mp hH
  have hOneV : (1 : K) ∈ V := by
    have h1 : (1 : Kˣ) ∈ Units.val ⁻¹' V := hV.symm ▸ H.one_mem
    exact h1
  have hs : {x : K | x + 1 ∈ V} ∈ nhds (0 : K) := by
    apply (hVopen.preimage (continuous_id.add continuous_const)).mem_nhds
    simpa only [Set.mem_preimage, Pi.add_apply, id_eq, zero_add] using hOneV
  obtain ⟨γ, -, hγ⟩ := (IsValuativeTopology.hasBasis_nhds_zero K).mem_iff.mp hs
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨N, hN⟩ := exists_pow_lt₀
    (Valuation.integer.v_irreducible_lt_one (v := valuation K) hϖ) γ
  refine ⟨N + 1, Nat.succ_pos N, ?_⟩
  rintro x ⟨u, hu, rfl⟩
  have hu1 : ((u : 𝒪[K]) - 1) ∈ ((𝓂[K] ^ N : Ideal 𝒪[K]) : Set 𝒪[K]) :=
    Ideal.pow_le_pow_right (Nat.le_succ N) hu
  rw [Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (v := valuation K) hϖ N] at hu1
  have hlt : valuation K ((((u : 𝒪[K]) - 1 : 𝒪[K]) : K)) < γ := lt_of_le_of_lt hu1 hN
  have hmem := hγ hlt
  have huV : ((u : 𝒪[K]) : K) ∈ V := by
    simpa only [AddSubgroupClass.coe_sub, OneMemClass.coe_one, Set.mem_ofPred_eq,
      sub_add_cancel] using hmem
  have : (Units.map (algebraMap 𝒪[K] K).toMonoidHom u) ∈ Units.val ⁻¹' V := huV
  rw [hV] at this
  exact this

end Langlands.NYLL.PortInternal.M402.D004

namespace Langlands.NYLL.LocalClassFieldTheory

open LocalFieldTheory

/-- For a prescribed unit `ϖ`, the norm subgroup of a finite abelian
extension contains a standard subgroup `⟨ϖᵈ⟩ Uⁿ` for some positive
integers `d` and `n`; here `d = [L : K]`. -/
theorem exists_uniformizerPrincipalSubgroup_le_normSubgroup :
    exists_uniformizerPrincipalSubgroup_le_normSubgroupStatement := by
  intro K L _ _ _ _ _ _ _ _ ϖ
  obtain ⟨n, hn, hUn⟩ :=
    PortInternal.M402.D004.exists_fieldPrincipalUnits_le_of_isOpen K
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
