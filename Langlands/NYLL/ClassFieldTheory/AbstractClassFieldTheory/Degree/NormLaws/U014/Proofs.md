# NYLL M026.014: finiteness of relative coset spaces in a tower

`Langlands.NYLL.ClassFormation.relativeTowerQuotientFinite` proves the published
proposition `Langlands.NYLL.ClassFormation.relativeTowerQuotientFiniteStatement`
of module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Statements`.

## Statement

The parameters are, in order, implicit `G : Type u_1`, instances `[Group G]` and
`[TopologicalSpace G]`, explicit `K L M : ClosedSubgroup G`,
`hML : M.toSubgroup ≤ L.toSubgroup` and `hLK : L.toSubgroup ≤ K.toSubgroup`, and
the two instance hypotheses
`[Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]` and
`[Finite (L.toSubgroup ⧸ extensionSubgroup L M hML)]`. The type of the theorem is
exactly `relativeTowerQuotientFiniteStatement K L M hML hLK`, which unfolds to

```lean
Finite (K.toSubgroup ⧸ extensionSubgroup K M (hML.trans hLK))
```

In words: in a tower `M ≤ L ≤ K` of closed subgroups, if `G_L` has finite index
in `G_K` and `G_M` has finite index in `G_L` (as relative subgroups), then
`G_M` has finite index in `G_K`.

## Implemented proof

The proof is the unchanged source term

```lean
Finite.of_equiv
  ((K.toSubgroup ⧸ extensionSubgroup K L hLK) ×
    (L.toSubgroup ⧸ extensionSubgroup L M hML))
  (Subgroup.quotientTowerEquiv hML hLK).symm
```

Inside the namespace `Langlands.NYLL.ClassFormation`, the name
`Subgroup.quotientTowerEquiv` resolves to the published
`Langlands.NYLL.Subgroup.quotientTowerEquiv` (module
`Langlands.NYLL.GaloisCohomology.GroupTheory.QuotientTower`, a port of the NYLL
source `Nyll/GaloisCohomology/GroupTheory/QuotientTower.lean`). For subgroups
`M ≤ L ≤ K` of `G` it is an equivalence
`(K ⧸ M.subgroupOf K) ≃ (K ⧸ L.subgroupOf K) × (L ⧸ M.subgroupOf L)`. The
published `extensionSubgroup K L hLK` (M004.002,
`Langlands.NYLL.CyclicCohomology.extensionSubgroup`) is an `abbrev` whose body is
`L.toSubgroup.subgroupOf K.toSubgroup`, so the domain and codomain of that
equivalence, applied to `M.toSubgroup ≤ L.toSubgroup ≤ K.toSubgroup`, unify with
the quotients in the statement without any `show` or `change`. The inverse
equivalence transports Mathlib's product instance
`Finite ((K ⧸ G_L) × (L ⧸ G_M))`, built from the two instance hypotheses, to the
target quotient by `Finite.of_equiv`. The expected type
`relativeTowerQuotientFiniteStatement K L M hML hLK` is a definition that the
elaborator unfolds by definitional unfolding when checking the term.

The only direct import is `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Statements`, which transitively provides
`extensionSubgroup`, `ClosedSubgroup` and `Langlands.NYLL.Subgroup.quotientTowerEquiv`.
The module opens `CyclicCohomology` for the name `extensionSubgroup`. The proof
uses no other published NYLL declaration and no data from the
`NormLaws.Definitions` module. The kernel axioms reported by inspection are
`propext`, `Classical.choice` and `Quot.sound`.

## Source correspondence and modifications

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, pinned
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean`, SHA-256
`985cb864c6b3360e38bf22dbea58d22685eb1146537166fcc8f5ca89821dd44f`, retained
under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Its registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

Unit M026.014 is the theorem `ClassFormation.relativeTowerQuotientFinite`:
docstring line 315, statement lines 316–324 and proof lines 325–328. Worker 5014
extracts it into this focused module, prefixes the namespace with
`Langlands.NYLL`, replaces the source imports by the published statement module,
and writes the conclusion as the published target applied to the parameters. The
docstring, the parameter telescope (names, binder kinds and order, including the
two `Finite` instance binders) and the proof term are the source ones. The
source's enclosing `noncomputable section`, `open scoped` lines and section
variables are not needed by this theorem (it binds its own `G`) and are omitted.

This is an abstract subgroup-level fact of the NYLL abstract-field model. It
discharges no host class-formation, cup, transfer, Tate or reciprocity target.

## Attribution

The original copyright, author and Apache-2.0 header is retained verbatim, and
the Lean module docstring records the modifications. The existing Library files
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are preserved unchanged; their
SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
