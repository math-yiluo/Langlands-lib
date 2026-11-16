# NYLL M298.017: finite-quotient cardinal rigidity

Worker 261, 16 November 2026.

## Source and attribution

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean`,
M298.017, lines 377–414 (theorem at 382), with namespace scaffolding at
23–34 and local instances at 36–46. The source file SHA-256 is
`0bc99c03d0936ca803d6497174ef17999b76789381f183f525a9f098eac7fd83`.
The registered sources are `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

The original copyright, author and Apache-2.0 header is retained.
The retained license and notice are `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Exact theorem

The source theorem
`ClassFormation.FiniteAbelianSubextension.eq_of_le_of_extensionQuotient_card_eq`
is adapted to
`Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.eq_of_le_of_extensionQuotient_card_eq`.
Its type is the published
`Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.eq_of_le_of_extensionQuotient_card_eqStatement`
applied to its complete source telescope:

```lean
{G : Type u} [Group G] [TopologicalSpace G] {K : ClosedSubgroup G}
{L₁ L₂ : FiniteAbelianSubextension K} (h₁₂ : L₁ ≤ L₂)
(hcard : Nat.card L₂.extensionQuotient = Nat.card L₁.extensionQuotient)
```

The statement unfolds to `L₁ = L₂`. The arbitrary universe `u`, binder
order and binder kinds are preserved. The order denotes field inclusion,
which is reverse inclusion of the representing closed subgroups:
`L₁ ≤ L₂` means `L₂.field.toSubgroup ≤ L₁.field.toSubgroup`.
The cardinalities concern the actual finite Galois quotient types.
No topological-group or class-formation hypothesis is needed.

## Implemented proof

Set `r := restriction h₁₂`. The published theorem
`abstractReciprocityRestriction_surjective` and the surjectivity of the two
quotient comparison equivalences show that `r` is surjective.
Since its source is finite, Mathlib's
`Nat.bijective_iff_surjective_and_card` and `hcard` show that `r` is
bijective.

Order antisymmetry reduces equality to the remaining subgroup inclusion.
For `g ∈ L₁.field`, regard `g` as `k ∈ K` using `L₁.below`.
The published `restriction_mk` sends the class of `k` for `L₂` to its
class for `L₁`. That latter class is `1`, by
`extensionQuotientMk_apply`, `QuotientGroup.eq_one_iff` and
`mem_extensionSubgroup_iff`. Injectivity of `r` then makes the class
for `L₂` equal to `1` as well. Passing through its comparison
equivalence and applying the same membership criterion gives
`g ∈ L₂.field`. This is the reverse inclusion required by the
field-inclusion order.

## Published dependencies and scope

The imports supply the unchanged target and restriction definition, and
these exact proof declarations:

- M298.010 `FiniteAbelianSubextension.restriction_mk`, from
  `FiniteAbelianClassification.Restriction.U010.Proofs`.
- M075.007 `ClassFormation.abstractReciprocityRestriction_surjective`,
  from `Core.Restriction.U007.Proofs`.
- M296.011 `FiniteAbelianSubextension.extensionQuotientMk_apply`,
  from `FiniteAbelianSubextension.U011.Proofs`.
- M022.001 `KummerTheory.mem_extensionSubgroup_iff`, from
  `KummerAbelianAssembly.U001.U001.Proofs`.

All adapted declaration names above have the prefix `Langlands.NYLL`.
Both source quotient instances are installed inside
`namespace FiniteAbelianSubextension` with `attribute [local instance]`
under the published names `Langlands.NYLL.PortInternal.M298.d001`
and `Langlands.NYLL.PortInternal.M298.d002`. Their instance attributes
end at the namespace boundary.

## Modifications

The module extracts only M298.017, prefixes its namespace with
`Langlands.NYLL`, replaces the original broad imports by the target
and the four proof imports listed above, replaces the docstring with
a short description, and uses the published proposition as its result
type. The initial `change L₁ = L₂` exposes that proposition's body.
Every following tactic line is unchanged from source lines 388–414.
The unused section variables are omitted: the source theorem's own
`{G : Type*}` and `{K : ClosedSubgroup G}` shadow them. An explicit
`universe u` gives that same arbitrary universe a name.
The `noncomputable section` and both source `open` namespaces are kept,
and the source local instance scope is restored with the attributes
described above. No existing statement or imported module is edited.
