# NYLL M165.004: the coset restriction map to embeddings is injective

`Langlands.NYLL.PortInternal.M165.d004` proves exactly
`Langlands.NYLL.PortInternal.M165.d004Statement K Ω E`. Its binders are those
of the target, in the same order and with the same binder kinds: explicit
`(K Ω : Type)`, instance-implicit `[Field K] [Field Ω] [Algebra K Ω]
[IsGalois K Ω]`, and explicit `(E : IntermediateField K Ω)`. No separable
closedness, finiteness or separability of `E / K` is assumed.

The target says that the published map
`Langlands.NYLL.LocalClassFieldTheory.baseFixingCosetToAlgHom K Ω E` is
injective. That map sends the left coset `σ · Gal(Ω / E)` of an element `σ` of
the subgroup `(closedFixingSubgroup K Ω ⊥).toSubgroup` of `Gal(Ω / K)` to the
`K`-algebra map `σ|_E : E →ₐ[K] Ω`. So two left cosets with the same
restriction to `E` are equal.

## Implemented proof

1. Take cosets `q`, `r` with equal images. Rewriting with `Quotient.out_eq`
   replaces them by the cosets of chosen representatives `σ := q.out` and
   `τ := r.out`, in the hypothesis and in the goal.
2. `Quotient.sound'` and `QuotientGroup.leftRel_apply` reduce the goal to
   `σ⁻¹ * τ ∈ extensionSubgroup (closedFixingSubgroup K Ω ⊥)
   (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)`.
3. The published `extensionSubgroup` is an abbreviation for
   `(closedFixingSubgroup K Ω E).toSubgroup.subgroupOf
   (closedFixingSubgroup K Ω ⊥).toSubgroup`, so Mathlib's
   `Subgroup.mem_subgroupOf` turns the goal into membership of the underlying
   automorphism in `(closedFixingSubgroup K Ω E).toSubgroup`. By `change`,
   this is `σ.1⁻¹ * τ.1 ∈ E.fixingSubgroup`.
4. `IntermediateField.mem_fixingSubgroup_iff` asks that `σ⁻¹ (τ x) = x` for
   every `x ∈ E`. Evaluating the hypothesis at `y := ⟨x, hx⟩ : E` and
   unfolding the map by `change` gives `σ x = τ x`. Rewriting `τ x` as `σ x`
   leaves `σ⁻¹ (σ x) = x`, which `simp` closes.

The theorem depends only on the target module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.Initial.Statements`
(and through it the published `Definitions` module and the published
`extensionSubgroup`, `closedFixingSubgroup` and `fixingSubgroupLeBase`) and on
Mathlib: `Quotient.out_eq`, `Quotient.sound'`, `QuotientGroup.leftRel_apply`,
`Subgroup.mem_subgroupOf`, `IntermediateField.mem_fixingSubgroup_iff` and the
`simp` set. No other Library result and no helper declaration is used.

In approved environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) the module compiled with
zero errors and zero warnings. Inspection of the theorem reports no level
parameters and only the axioms `propext`, `Classical.choice` and
`Quot.sound`. This development check is not acceptance.

## Source correspondence and modification record

Adapted by Worker 368 on 14 November 2026 from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean`
(SHA-256 `477273f35f3c5945fe5ccb5cb38e4527f2656e8f3f2ef85451aef32c639e4106`):
the private theorem `LocalClassFieldTheory.baseFixingCosetToAlgHom_injective`
at lines 119–139 (`omit [IsSepClosed Ω] in` at line 119, statement at lines
120–121), with the section variables at lines 36–37 and 41. The registered source is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Original declaration | Adapted declaration |
| --- | --- |
| private `LocalClassFieldTheory.baseFixingCosetToAlgHom_injective` (M165.004) | `Langlands.NYLL.PortInternal.M165.d004` (this proof) |
| `KummerTheory.mem_extensionSubgroup_iff` (inventory M022.001; `Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianAssembly.lean`, lines 33–38, proved by `Iff.rfl`; used at source lines 126–129) | not ported; replaced by Mathlib's `Subgroup.mem_subgroupOf` |

Modifications:

- the private theorem is published under the name reserved by the port plan,
  `Langlands.NYLL.PortInternal.M165.d004`, declared with `_root_` inside
  `namespace Langlands.NYLL.LocalClassFieldTheory` so that
  `baseFixingCosetToAlgHom` and `closedFixingSubgroup` (through
  `open RamificationTheory`) resolve to the published definitions;
- the section variables that the source theorem takes (all except the
  omitted `[IsSepClosed Ω]`) are written as explicit binders, and its
  conclusion is expressed as the published target `d004Statement K Ω E`,
  which unfolds to the source conclusion
  `Function.Injective (baseFixingCosetToAlgHom K Ω E)`, so `intro q r hqr`
  applies directly;
- the source step `apply (mem_extensionSubgroup_iff … ((Quotient.out q)⁻¹ *
  Quotient.out r)).2` uses the NYLL lemma `KummerTheory.mem_extensionSubgroup_iff`
  (opened in the source by `open RamificationTheory KummerTheory`), which is
  not published in the Library. It is replaced by
  `apply (Subgroup.mem_subgroupOf).2`. This is the same membership criterion,
  because the published `extensionSubgroup` is an abbreviation for
  `Subgroup.subgroupOf`; the goal after the step is the same, and the
  following `change` is unchanged;
- the NYLL imports are replaced by the published target module; the source's
  `open LocalFieldTheory`, `ClassFormation`, `KummerTheory` and
  `BigOperators` are dropped, keeping `open RamificationTheory
  CyclicCohomology` as in the published `Definitions` module;
- a docstring is added; the rest of the tactic proof is unchanged.

The original copyright and author header is retained. The file remains under
Apache-2.0; the license and notice are the published `licenses/NYLL/LICENSE`
(SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE`
(SHA-256 `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`),
reused unchanged. This support proof discharges no host class-formation,
cohomology or reciprocity target.
