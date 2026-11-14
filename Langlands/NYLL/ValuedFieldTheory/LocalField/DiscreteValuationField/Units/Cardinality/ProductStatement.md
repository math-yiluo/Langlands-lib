# NYLL M120.074: iterated subquotient cardinality target

For an antitone subgroup filtration `U` of an arbitrary group `G`, normality of
every filtration level, finiteness of every subquotient `U^i/U^j`, and natural
numbers `l` and `r`, the cardinality of the iterated subquotient `U^l/U^(l+r)`
equals the product over `i < r` of the cardinalities of the adjacent graded
pieces `U^(l+i)/U^(l+i+1)`.

## Original source

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Units.lean`,
M120.074: docstring at lines 916–917, declaration name at line 918, telescope
at lines 919–921, proposition at lines 922–924, and original proof from
`:= by` at the end of line 924 through line 951. (The task contract cites the
signature as lines 918–925 and the proof as ending at 949; in the pinned file
line 925 is the proof's first tactic `induction r with`, and the proof's last
`calc` step ends at line 951.) The shared source context is lines 18–36:
`namespace LocalFieldTheory` (line 18), `universe u v` (line 20),
`open scoped BigOperators` (line 22), the namespaces `DiscreteValuationField`
(line 24) and `AntitoneSubgroupFiltration` (line 34), and
`variable {G : Type u} [Group G] (U : AntitoneSubgroupFiltration G)` (line 36).
The source file SHA-256 is
`30ce59edb8590e15afdaaef8d9551282e240c576f09be0ad55d12b09e9e4d807`.

The readable original is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Registered source `external-lean-reuse-snapshots-2026-10-21` has fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
has fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The original declaration is the theorem
`LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.card_principalUnitSubquotient_eq_prod_gradedPiece`.
Its adapted target is
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.card_principalUnitSubquotient_eq_prod_gradedPieceStatement`
in module
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Units.Cardinality.ProductStatement`.

## Exact statement and shared objects

The full telescope is, in order, `{G : Type u}`, `[Group G]`,
`(U : AntitoneSubgroupFiltration G)` (from the source `variable` line),
then `(_hN : ∀ i : ℕ, (U.principalUnitSubgroup i).Normal)`,
`[∀ i j : ℕ, Finite (U.principalUnitSubquotient i j)]` and `(l r : ℕ)`
(source lines 919–921). Binder kinds and order are those of the source. The
target lives in universe `u`, and the source's unused universe declaration `v`
is retained.

The proposition is exactly the source conclusion (lines 922–924):
`Nat.card (U.principalUnitSubquotient l (l + r)) =
∏ i ∈ Finset.range r, Nat.card (U.principalUnitGradedPiece (l + i))`.
For `r = 0` the right side is the empty product `1`.

The proposition uses the published objects, without duplicates:

- `AntitoneSubgroupFiltration` and its accessor `principalUnitSubgroup`
  (source M120.001–002), from
  `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Units.Filtration`;
- `principalUnitSubquotient` (source M120.028), from
  `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Units.Subquotient`;
- `principalUnitGradedPiece` (source M120.038), from
  `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Units.GradedPiece`.

`principalUnitSubquotient m n` is the type
`U^m ⧸ (U^n).subgroupOf U^m`, and `principalUnitGradedPiece n` is
`principalUnitSubquotient n (n + 1)`. Neither type needs a normality instance,
and neither does `Finite` or `Nat.card`. Hence the proposition does not refer to
the normality proof `_hN`; it is nevertheless retained as an explicit binder
because the source theorem has it, and the source proof uses it (`let := hN …`)
to supply the normality instances its lemmas need. The finiteness instance
family is likewise retained exactly as in the source.

This source result is generic group theory. It asserts no intrinsic
valued-field or principal-unit semantics for an arbitrary filtration.

## Modifications, attribution and proof boundary

Worker 299 drafted and Worker 475 finalized this adaptation. The changes are:

- the source namespace is prefixed by `Langlands.NYLL`;
- the theorem is replaced by a `Prop`-valued `def` with suffix `Statement`
  whose body is the source conclusion;
- the source context `variable {G : Type u} [Group G] (U : …)` is written as
  explicit leading binders of the definition, with unchanged kinds and order;
- the source hypothesis name `hN` is renamed `_hN`, because the proposition
  does not use it; its type, position and explicitness are unchanged;
- the source imports (three Mathlib modules) are replaced by the published
  `Units.GradedPiece` module, whose import chain through `Units.Subquotient`
  and `Units.Filtration` retains all three;
- a new docstring and a module comment describe the target and these changes.

No other parameter, hypothesis or instance is changed, and no theorem, instance
or helper declaration is added. This file states M120.074; it does not publish
a proof. The source proof (lines 924–951) inducts on `r` using source lemmas
`card_principalUnitSubquotient_self`, `card_principalUnitSubquotient_eq_mul_of_le`
and `card_principalUnitSubquotient_succ_eq_gradedPiece`; a separate proof task
must prove this exact published proposition and document its own route.

The original copyright and author header is retained verbatim. The existing
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) retain
the Apache-2.0 license and attribution.
