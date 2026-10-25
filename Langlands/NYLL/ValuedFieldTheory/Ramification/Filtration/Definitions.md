# Natural-ceiling subgroup step filtration

This module adapts only NYLL source unit M291.001. Its sole declaration is
`Langlands.NYLL.RamificationTheory.natCeilStepFiltration`.

## Interface and meaning

The complete interface is

```lean
{G : Type u} [Group G] (F : ℕ → Subgroup G) (t : ℝ) : Subgroup G
```

The definition returns exactly `F (Nat.ceil t)`. The group universe `u` is
arbitrary, `F` is any natural-indexed subgroup family, and `t` is any real
number. There are no field, normality, finiteness, monotonicity or positivity
hypotheses. The word “filtration” in the name does not impose antitonicity.

`Nat.ceil` is Mathlib's least natural number at least its argument. In
particular its nonpositive-input convention is zero, as expressed by Mathlib's
`Nat.ceil_eq_zero`; thus the expression selects `F 0` at every nonpositive
real argument. This describes the existing ceiling convention, rather than
adding an evaluation theorem to this module. No antitonicity, jump, right-limit,
ramification or reciprocity result is declared here.

## Original source and correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/Filtration.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/Ramification/Filtration.lean>).
The complete original file was read. The namespace and group context are at
lines 19–24, the docstring at 26–28 and the selected definition at 29–31.
The original file SHA-256 is
`585f24ad9e20460024c2d756ede77b13f03e88bad1f0126603c8fac01b8dbb1f`.
Its registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

| Original declaration | Adapted declaration |
| --- | --- |
| `RamificationTheory.natCeilStepFiltration` | `Langlands.NYLL.RamificationTheory.natCeilStepFiltration` |

Worker 22 extracted the one definition, prefixed its namespace with
`Langlands.NYLL`, replaced the anonymous universe in `Type*` by an explicit
`u`, moved the section parameters into the declaration and clarified the
docstring. The source expression `F ⌈t⌉₊` is written `F (Nat.ceil t)`, using
exactly the definition behind that notation. The noncomputable section and
all three original imports are retained. No compatibility patch or other
worker's adapted Lean draft was reused.

## Reuse and dependencies

The direct imports are exactly:

- `Mathlib.Algebra.Group.Subgroup.Lattice`
- `Mathlib.Algebra.Order.Floor.Ring`
- `Mathlib.Algebra.Order.Archimedean.Real.Basic`

The implementation reuses Mathlib's `Subgroup` and `Nat.ceil` directly, with
no NYLL dependencies or new instances. Exact-name and ceiling/subgroup searches
in the current Library and approved Mathlib found no existing definition with
this general interface. The Library's specialized ceiling uses in unit-filtration
reciprocity statements and ramification-break comparisons do not define an
arbitrary-family extension.

In particular, `Langlands.Ramification.Padic.lowerRamificationGroupReal` in
`Langlands/LocalFactor/Ramification/Herbrand/Finite.lean` uses `Int.ceil`
and the concrete integer-indexed p-adic lower groups. Its group, family and
negative-index convention differ; it is not an alias for this definition.

Development checking uses approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) through the project's Lean service.
The selected import set is the original three-module set, not a claim of
minimality or a build claim about the rest of NYLL.

## Attribution and scope

The original copyright and author header is preserved. The unchanged Apache-2.0
license and NOTICE are already retained in `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
The source path has no specific entry in NOTICE or the retained third-party
attribution tables. No source-specific project or Library erratum was found.

The later source definitions `natCeilStepFiltrationAfter` and
`IsNatCeilStepFiltrationJump` and all source theorems are outside this module.
This generic definition supplies no Artin map, principal-unit theorem or
filtered local reciprocity construction.
