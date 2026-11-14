# Standard subgroups inside finite abelian norm subgroups: exact proof (M402.004)

This module proves the published proposition
`Langlands.NYLL.LocalClassFieldTheory.exists_uniformizerPrincipalSubgroup_le_normSubgroupStatement`
by the theorem
`Langlands.NYLL.LocalClassFieldTheory.exists_uniformizerPrincipalSubgroup_le_normSubgroup`.
It also contains one auxiliary lemma,
`Langlands.NYLL.PortInternal.M402.D004.exists_fieldPrincipalUnits_le_of_isOpen`.

## Target and exact type

The target is the closed proposition of
`OrderReversal/U004/Statements.lean` (unchanged by this contribution):

```lean
∀ (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsAbelianGalois K L]
  [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (ϖ : Kˣ),
  ∃ d n : Nat, 0 < d ∧ 1 ≤ n ∧
    LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ d n ≤
      localNormSubgroup K L
```

The theorem's declared type is exactly the constant
`exists_uniformizerPrincipalSubgroup_le_normSubgroupStatement`; the proof
introduces its eleven binders in order with `intro K L _ _ _ _ _ _ _ _ ϖ`.
Both fields are therefore in `Type` (universe zero) as in the target, the
theorem has no universe parameters, and no hypothesis is added: `ϖ` is an
arbitrary unit of `K` (not assumed to be a uniformizer), and `L` carries no
valuation, topology or local-field structure.

Mathematically: for a finite abelian Galois extension `L/K` of a
nonarchimedean local field `K` and any `ϖ ∈ Kˣ`, the norm subgroup
`N_{L/K}(Lˣ)` contains `⟨ϖ ^ d⟩ · Uⁿ_K` for some `d ≥ 1` and `n ≥ 1`. The
proof gives the explicit exponent `d = [L : K] = Module.finrank K L`; `n` is
obtained from openness of the norm subgroup and is not explicit.

The objects are the published ones: `uniformizerPrincipalSubgroup K ϖ d n` is
`Subgroup.zpowers (ϖ ^ d) ⊔ fieldPrincipalUnits K n`;
`fieldPrincipalUnits K n` is the image in `Kˣ`, under
`Units.map (algebraMap 𝒪[K] K).toMonoidHom`, of
`principalUnits K n = {u ∈ 𝒪[K]ˣ | u - 1 ∈ 𝓂[K] ^ n}`; and
`localNormSubgroup K L` is the range of `normUnits K L = Units.map (Algebra.norm K)`.

## Implemented proof

### Auxiliary lemma: open subgroups contain principal units

```lean
theorem Langlands.NYLL.PortInternal.M402.D004.exists_fieldPrincipalUnits_le_of_isOpen
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : Subgroup Kˣ) (hH : IsOpen (H : Set Kˣ)) :
    ∃ n : Nat, 1 ≤ n ∧ fieldPrincipalUnits K n ≤ H
```

Here `Kˣ` carries Mathlib's units topology. The proof (Lean lines 57–80):

1. `Units.isEmbedding_val₀` says `Units.val : Kˣ → K` is a topological
   embedding (its hypothesis `ContinuousInv₀ K` comes from Mathlib's instance
   `IsNonarchimedeanLocalField.instIsTopologicalDivisionRing`). Hence
   `H = Units.val ⁻¹' V` for an open `V ⊆ K`, and `1 ∈ V` since `1 ∈ H`.
2. The set `{x : K | x + 1 ∈ V}` is the preimage of `V` under the continuous
   map `x ↦ x + 1`, so it is open and contains `0`; it is a neighbourhood of
   `0` in `K`.
3. Mathlib's `IsValuativeTopology.hasBasis_nhds_zero K` (the valuative
   topology is part of `IsNonarchimedeanLocalField`) gives a unit `γ` of the
   value group with `{x | valuation K x < γ} ⊆ {x | x + 1 ∈ V}`.
4. `𝒪[K]` is a discrete valuation ring (Mathlib instance
   `IsNonarchimedeanLocalField.instIsDiscreteValuationRing…`), so it has an
   irreducible `ϖ` with `valuation K ϖ < 1`
   (`Valuation.integer.v_irreducible_lt_one`). The value group with zero is
   `MulArchimedean` (instance `ValuativeRel.instMulArchimedeanValueGroupWithZeroOfIsRankLeOne`,
   via Mathlib's rank-at-most-one instance for local fields), so
   `exists_pow_lt₀` gives `N` with `valuation K ϖ ^ N < γ`.
5. Take `n = N + 1 ≥ 1`. If `u ∈ principalUnits K (N + 1)`, then
   `u - 1 ∈ 𝓂[K] ^ (N + 1) ⊆ 𝓂[K] ^ N` (`Ideal.pow_le_pow_right`), and
   Mathlib's `Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow` rewrites
   this as `valuation K (u - 1) ≤ valuation K ϖ ^ N < γ`. By step 3,
   `(u - 1) + 1 = u ∈ V` (the `simpa only` normalizes the subring coercions
   and uses `sub_add_cancel`), so the image unit of `u` in `Kˣ` lies in
   `Units.val ⁻¹' V = H`.

The index `N + 1` rather than `N` is taken only to obtain `1 ≤ n`.

### Main theorem

```lean
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
```

1. The published M257.007 theorem
   `Langlands.NYLL.LocalClassFieldTheory.localNormSubgroup_isOpen K L`
   (type `localNormSubgroup_isOpenStatement K L`, which unfolds to
   `IsOpen (localNormSubgroup K L : Set Kˣ)`) needs `[IsGalois K L]`; this is
   supplied by the parent projection of `IsAbelianGalois K L`, which extends
   `IsGalois K L`. The auxiliary lemma applied to `H = localNormSubgroup K L`
   (its universe `u` instantiated at `0`) gives `n ≥ 1` with `fieldPrincipalUnits K n ≤ localNormSubgroup K L`.
2. The exponent is `d = Module.finrank K L`, positive by
   `Module.finrank_pos` (`L` is a nontrivial finite-dimensional `K`-space).
3. By `sup_le`, it suffices to bound both pieces of
   `zpowers (ϖ ^ d) ⊔ fieldPrincipalUnits K n`. For the first,
   `Subgroup.zpowers_le` reduces to `ϖ ^ d ∈ localNormSubgroup K L`, i.e. to a
   preimage under `normUnits K L`. The witness is the unit
   `algebraMap K L ϖ` of `L`: equality of units is checked on values (`ext`),
   and `Algebra.norm_algebraMap` (`Algebra.norm K (algebraMap K L x) =
   x ^ Module.finrank K L`, valid since `L` is a free `K`-module) together
   with `Units.val_pow_eq_pow_val` closes it. The second piece is step 1.

## Dependencies

Direct imports:

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.OrderReversal.U004.Statements`
  (the unchanged target, which also brings `uniformizerPrincipalSubgroup`,
  `fieldPrincipalUnits`, `principalUnits`, `localNormSubgroup` and `normUnits`);
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity.U007.Proofs`
  (the published exact proof of `localNormSubgroup_isOpen`);
- Mathlib's `GroupTheory.ArchimedeanDensely` (`exists_pow_lt₀`),
  `RingTheory.DiscreteValuationRing.Basic`
  (`Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow`) and
  `Topology.Algebra.GroupWithZero` (`Units.isEmbedding_val₀`).

No instance, axiom or hypothesis is introduced, and neither the target pair
nor anything it imports is modified. A development check reported the axioms
of the main theorem as `propext`, `Classical.choice` and `Quot.sound` only.

## Source correspondence and change of route

Source: Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, read from the retained
snapshot registered as `external-lean-reuse-snapshots-2026-10-21`
(attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`).

| Source (path under `Nyll/`, SHA-256 of whole file) | Lines | Adapted here |
| --- | --- | --- |
| `ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/OrderReversal.lean` (`173d6575…8e971ba06`) | 129–164: docstring, signature and proof of `exists_uniformizerPrincipalSubgroup_le_normSubgroup` | main theorem, same adapted name; type is the published Statement |
| `ValuedFieldTheory/LocalField/NonarchimedeanLocalField/StandardOpenSubgroups.lean` (`9cf6baf5…07097d7d`) | 43–84 (M289.003 `exists_fieldPrincipalUnits_subset_of_mem_nhds`), 86–93 (M289.004 `exists_fieldPrincipalUnits_le_of_isOpen`) | auxiliary lemma (open-subgroup form only) |
| `ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean` (`6147c661…66a0977c83`) | 160–185 (`exists_maximalIdeal_pow_subset_nhds_zero`) | inlined into the auxiliary lemma |

The full hashes are
`173d65750c2a18cc233fcc94d9fde94e88c7a42709cfb9c27e50bae8e971ba06`,
`9cf6baf50519f650504762782a5aed12500479b911fc1ac4db9a138207097d7d` and
`6147c6613cd0176ace8787d7c65a3026d23bd5e23dc3282902d5ea66a0977c83`.
The unit is M402.004 of the
[public partition](../../../../../../../../notes/reuse/nyll-public-port/m385-m408.md#m402).

**Exponent `d`.** The source proves that `Kˣ ⧸ localNormSubgroup K L` is
finite by transporting finiteness of `Gal(L/K)` along the source's Artin
isomorphism `abelianizationEquivNormQuotient` (local reciprocity), takes
`d` to be the index of the norm subgroup, and uses `Subgroup.pow_index_mem`.
This proof instead takes `d = [L : K]` and exhibits `ϖ ^ [L : K]` as the norm
of `algebraMap K L ϖ`. This needs no reciprocity, finiteness of the norm
quotient, or finite-index argument; it is valid for every finite extension.

**Exponent `n`.** Like the source, the proof applies openness of the norm
subgroup (source `localNormSubgroup_isOpen`, here the published M257.007
proof, whose own route differs from the source's) and the fact that open
subgroups of `Kˣ` contain some `Uⁿ_K`, `n ≥ 1`. The latter is source M289.004,
whose published target
`Langlands.NYLL.LocalFieldTheory.exists_fieldPrincipalUnits_le_of_isOpenStatement`
had no proof in the Library when this was written (its owner is Task 6171).
The auxiliary lemma therefore proves the same proposition here, under an
internal name in `Langlands.NYLL.PortInternal.M402.D004` so that it cannot
collide with the future exact M289.004 theorem; it does not discharge that
target. Its proof follows the source's M289.003 argument (open set in `K`
pulled back through the embedding of units, shifted neighbourhood of zero,
then `N + 1`), with two changes: the source passes to a neighbourhood of zero
in `𝒪[K]` and calls `exists_maximalIdeal_pow_subset_nhds_zero`, whereas here
the neighbourhood is taken in `K` and that lemma's argument (valuative basis
of zero, an irreducible, `exists_pow_lt₀`, and the description of `𝓂[K] ^ N`
by valuations) is inlined; and the source's
`mem_principalUnits_iff` and `integerUnitsToFieldUnits` are replaced by the
definitional unfoldings of the published `principalUnits` and
`fieldPrincipalUnits`.

Other changes: the namespace is prefixed with `Langlands.NYLL`; the theorem's
type is the published closed Statement, so its binders are introduced by
`intro`; `ℕ` is written `Nat`; the source imports are replaced by the
modules listed above; and the docstring says "prescribed unit" (as the
target does), since `ϖ` carries no hypothesis.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, followed by Worker 471's dated
modification record. The unchanged
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are retained in
`licenses/NYLL/`, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

Environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Development compilation is
separate from acceptance.

This proof covers only M402.004. The other order-reversal units
(M402.001–003 and M402.005) and the exact M289.003–004 theorems are separate
obligations.
