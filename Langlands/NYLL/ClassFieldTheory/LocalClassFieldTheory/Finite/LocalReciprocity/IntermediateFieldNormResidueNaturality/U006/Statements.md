# Abelianization of an isomorphism onto a commutative group: statement target

`Langlands.NYLL.PortInternal.M260.d006Statement` is the proposition that
abelianizing a group isomorphism `q : G ≃* H` onto a commutative group, then
identifying `Abelianization H` with `H`, sends the class of `x` to `q x`. In
Lean:

```lean
def d006Statement
    {G H : Type*} [Group G] [CommGroup H]
    (q : G ≃* H) (x : G) : Prop :=
  (Abelianization.equivOfComm (H := H)).symm
      (q.abelianizationCongr (Abelianization.of x)) =
    q x
```

This is the statement of source unit M260.006, a private helper lemma. Defining
the proposition does not prove it.

## Parameters and meaning

The declaration has two universe parameters, one for `G` and one for `H`, from
the two `Type*` binders. Inspection shows them as `u_1` and `u_2`. They are
independent and not restricted to `Type 0`. The parameters are:

| Binder | Kind | Meaning |
| --- | --- | --- |
| `G` | implicit, `Type u_1` | Source group |
| `H` | implicit, `Type u_2` | Target group |
| `[Group G]` | instance-implicit | Group structure on `G` |
| `[CommGroup H]` | instance-implicit | Commutative group structure on `H` |
| `q : G ≃* H` | explicit | Multiplicative isomorphism |
| `x : G` | explicit | Element whose class is evaluated |

The definitions involved are Mathlib's, from the approved file
`Mathlib/GroupTheory/Abelianization/Defs.lean`:

- `Abelianization.of : G →* Abelianization G` sends an element to its class
  modulo the commutator subgroup.
- `MulEquiv.abelianizationCongr` (line 150) turns `q` into the isomorphism
  `Abelianization G ≃* Abelianization H`, induced by functoriality.
- `Abelianization.equivOfComm` (line 185) is the canonical isomorphism
  `H ≃* Abelianization H` for a commutative group `H`. Its forward map is
  `Abelianization.of` and its inverse is `Abelianization.lift (MonoidHom.id H)`.
  The statement applies this inverse.

So the equation says that the two maps `G → H` agree at `x`:

- the abelianized isomorphism followed by the canonical inverse;
- `q` itself.

The statement involves no fields, Galois groups, topology or local-field
structure.

## Original source and declaration map

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/IntermediateFieldNormResidueNaturality.lean`.
The private theorem's statement is at lines 140–145 and its proof at 145–149.
The file's SHA-256 is
`0198546411975a802c5ea2441572ced6b9a7fcfa28a7a23a7bfdbf5e806a9ffb`. The source
statement reads:

```lean
private theorem commGroup_abelianizationCongr_of
    {G H : Type*} [Group G] [CommGroup H]
    (q : G ≃* H) (x : G) :
    (Abelianization.equivOfComm (H := H)).symm
        (q.abelianizationCongr (Abelianization.of x)) =
      q x := by
```

The theorem sits in `section IntermediateRestriction`. Lines 136–138 of that
section declare the variables `(K : Type) [Field K] [ValuativeRel K]
[TopologicalSpace K] [IsNonarchimedeanLocalField K]`. The theorem's statement
does not mention `K`. Under Lean 4's rule for theorem statements, unmentioned
section variables, and instances depending only on them, are therefore not
parameters of the source theorem. The adapted proposition accordingly has
exactly the six binders above. The file-level `universe u v` declaration
(line 36) is likewise unused here.

The retained original is in the project literature folder
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Original declaration | Adapted declaration |
| --- | --- |
| Private `LocalClassFieldTheory.commGroup_abelianizationCongr_of` (M260.006) | `Langlands.NYLL.PortInternal.M260.d006Statement` |

Row M260.006 of the published partition
[`notes/reuse/nyll-public-port/m259-m262.md`](../../../../../../../../notes/reuse/nyll-public-port/m259-m262.md)
reserves the internal name `Langlands.NYLL.PortInternal.M260.d006` for this
private source theorem. Section 3 of
[`notes/reuse/nyll-public-port-plan.md`](../../../../../../../../notes/reuse/nyll-public-port-plan.md)
adds `Statement` for a theorem's target. This is a fresh implementation name,
not the source's mangled private kernel name. Making the target public lets the
later proof be shared by the M260 restriction units. No NYLL erratum for this
module was found in the current Library's `notes/`.

## Imports and modification record

The only direct import is `Mathlib.GroupTheory.Abelianization.Defs`, which
defines every name the statement uses. The source module also imports it. The
source's other imports (NYLL `IntrinsicAbsoluteData`, `Main`,
`IntermediateFieldRestriction` and `Mathlib.FieldTheory.Galois.Abelian`) are not
needed for this statement and are dropped. No external NYLL module is imported.

The adaptation makes four changes:

- it moves the private theorem's telescope and conclusion into the public
  Prop-valued definition above, keeping binder order, binder kinds, binder
  names and the conclusion unchanged;
- it omits the source proof, the `private` modifier and every other declaration
  of the module;
- it puts the definition in the namespace `Langlands.NYLL.PortInternal.M260`;
- it keeps the `noncomputable section`, which has no effect on a proposition.

The Lean header records these changes with Worker 30's dated modification note.

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection reports a definition
whose type ends in `Prop` (`statement_returns_prop: true`), with level
parameters `u_1, u_2` and only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. This development check is not independent
acceptance.

## Boundary and license

This file defines the proposition only. The proof, named
`Langlands.NYLL.PortInternal.M260.d006`, needs a separate proof task once this
target is in the Library. The source proof composes
`abelianizationCongr_of` (Mathlib line 162) with `MulEquiv.symm_apply_apply`.

The Lean file keeps the original copyright and author header unchanged:
Copyright (c) 2026 Naganori Yamaguchi; Authors: Naganori Yamaguchi (assisted
by OpenAI Codex). It remains under Apache-2.0. The already-published
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are reused unchanged and
included through `repository_paths`. Their SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. Worker 30
adapted this unit directly from the pinned original; no other project worker
supplied code.
