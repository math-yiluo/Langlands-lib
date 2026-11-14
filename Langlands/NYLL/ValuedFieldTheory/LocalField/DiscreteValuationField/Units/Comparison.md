# NYLL M120: principal-unit quotient comparison equivalences

This module adapts two group equivalences for a generic antitone subgroup
filtration `U` of a group `G`, with levels `U^k = U.principalUnitSubgroup k`.
For `m ≤ n`:

- `principalUnitSubquotientEquivClassInQuotientOfLe` identifies the actual
  subquotient `U^m/U^n` with the image of `U^m` in `G ⧸ U^n` (a first
  isomorphism theorem construction);
- `quotientModuloPrincipalUnitClassEquivQuotientOfLe` identifies
  `(G ⧸ U^n) ⧸ (image of U^m)` with `G ⧸ U^m` (a third isomorphism theorem
  construction).

## Exact source correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Units.lean` (M120).
The original file SHA-256 is
`30ce59edb8590e15afdaaef8d9551282e240c576f09be0ad55d12b09e9e4d807`.
The readable original is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Units.lean`
under registered source `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Unit | Original declaration | Source declaration lines | Adapted declaration |
| --- | --- | --- | --- |
| M120.051 | `LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitSubquotientEquivClassInQuotientOfLe` | 539–549 | `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitSubquotientEquivClassInQuotientOfLe` |
| M120.083 | `LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.quotientModuloPrincipalUnitClassEquivQuotientOfLe` | 1076–1085 | `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.quotientModuloPrincipalUnitClassEquivQuotientOfLe` |

Both original docstrings (lines 538 and 1074–1075) are retained verbatim, and
both declarations remain `noncomputable def`s. The shared source context is
`universe u v` and
`variable {G : Type u} [Group G] (U : AntitoneSubgroupFiltration G)` inside
`LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration`; the
adapted file keeps this context under the `Langlands.NYLL` prefix, together with
the source's `open scoped BigOperators`.

## Complete telescopes

- `principalUnitSubquotientEquivClassInQuotientOfLe`:
  `{G : Type u} [Group G] (U : AntitoneSubgroupFiltration G) {m n : ℕ}
  (hmn : m ≤ n) [(U.principalUnitSubgroup n).Normal]`, of type
  `U.principalUnitSubquotient m n ≃* U.principalUnitSubgroupClassInQuotient m n`.
- `quotientModuloPrincipalUnitClassEquivQuotientOfLe`:
  `{G : Type u} [Group G] (U : AntitoneSubgroupFiltration G) {m n : ℕ}
  (hmn : m ≤ n) [(U.principalUnitSubgroup n).Normal]
  [(U.principalUnitSubgroup m).Normal]`, of type
  `(G ⧸ U.principalUnitSubgroup n) ⧸ U.principalUnitSubgroupClassInQuotient m n
  ≃* G ⧸ U.principalUnitSubgroup m`.

Both have the single universe parameter `u`. The groups are the actual
published objects: `principalUnitSubquotient m n` is the quotient of `U^m` by
`(U^n).subgroupOf U^m`, and `principalUnitSubgroupClassInQuotient m n` is the
subgroup `Subgroup.map (QuotientGroup.mk' U^n) U^m` of `G ⧸ U^n`. The normality
instance on this image used by the second quotient is the published instance
`principalUnitSubgroupClassInQuotient_normal`, which needs both normality
instances.

## Implemented constructions

**First isomorphism (M120.051).** Let
`f : U^m →* G ⧸ U^n` be `(QuotientGroup.mk' U^n).comp (U^m).subtype`, the class
in `G ⧸ U^n` of an element of `U^m`. Two local facts are proved inside the
definition:

- `f.ker = (U^n).subgroupOf U^m`: after `MonoidHom.mem_ker` and
  `Subgroup.mem_subgroupOf`, the condition is `QuotientGroup.mk' U^n x = 1`,
  which is `QuotientGroup.eq_one_iff`;
- `f.range = U.principalUnitSubgroupClassInQuotient m n`: by extensionality, an
  element of the range is the class of `(x : G)` with `x ∈ U^m`, and conversely
  the class of `x ∈ U^m` is `f ⟨x, hx⟩`, both by `rfl`.

The equivalence is the composite of the published identity equivalence
`principalUnitSubquotientConcreteEquiv m n`, Mathlib's
`QuotientGroup.quotientMulEquivOfEq` along the reversed kernel equation,
`QuotientGroup.quotientKerEquivRange f`, and `MulEquiv.subgroupCongr` along the
range equation. This is exactly the source chain of four equivalences.

The kernel calculation does not use `m ≤ n`; as in the source, where the
helpers receiving `hmn` ignore it, the parameter `hmn` is kept only to preserve
the source binder telescope. The declaration is preceded by
`set_option linter.unusedVariables false in` so that the binder keeps its
source name `hmn` without an unused-variable warning.

**Third isomorphism (M120.083).** The equivalence is Mathlib's
`QuotientGroup.quotientQuotientEquivQuotient (U^n) (U^m) (U.antitone hmn)`,
whose third argument is the inclusion `U^n ≤ U^m`. Mathlib's statement uses
`Subgroup.map (QuotientGroup.mk' U^n) U^m` as the subgroup of `G ⧸ U^n`, which is
definitionally the published `principalUnitSubgroupClassInQuotient m n`, so the
declared type is accepted as written.

## Representative formulas

The file contains two `example`s, checked by `rfl` at every build; they add no
declarations, and no separate theorem target is published for them:

- source M120.052 (lines 556–565): for `x : U^m`, the first equivalence applied
  to `U.principalUnitSubquotientMk m n x`, coerced to `G ⧸ U^n`, is
  `QuotientGroup.mk' U^n (x : G)`;
- source M120.085 (lines 1117–1127): for `x : G`, the second equivalence applied
  to `QuotientGroup.mk' (U.principalUnitSubgroupClassInQuotient m n)
  (QuotientGroup.mk' U^n x)` is `QuotientGroup.mk' U^m x`.

So the equivalences agree with the source maps on subgroup representatives and
on double-quotient representatives.

## Modifications

Worker 477 made these changes:

- the namespace is prefixed by `Langlands.NYLL`;
- the three original Mathlib imports are replaced by the published
  `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Units.Subquotient`,
  which imports them through its filtration module;
- the source helper `principalUnitSubgroupToQuotient` (M120.047, lines
  498–502) and the theorems `principalUnitSubgroupToQuotient_ker_eq` (M120.049,
  lines 516–524) and `principalUnitSubgroupToQuotient_range_eq_classInQuotient`
  (M120.050, lines 527–536) are not published; the same homomorphism and the
  same two equations appear as a local `let` and two local `have`s in the
  definition body. The kernel proof uses `change` where the source rewrites with
  the evaluation lemma M120.048. No helper declaration is added, so these
  source names stay free for a later port;
- the source theorem `principalUnitSubgroup_antitone` (M120.004, lines 48–50),
  whose proof is `U.antitone h`, is replaced in M120.083 by the published
  structure field `U.antitone hmn`;
- the scoped `set_option linter.unusedVariables false in` described above is
  added to M120.051;
- a module comment records these changes.

Worker 298's unreviewed shared draft `GenericComparisonProbe.lean` (revision 15
of the shared drafts of Task 5888) used the same construction route and was
read before writing this module; Worker 477 wrote this file.

The Library and Mathlib were searched before porting; no equivalent
declaration for these filtration objects exists, and the constructions reuse
Mathlib's isomorphism-theorem equivalences directly. No instance is declared.

## Attribution and scope

The original copyright and author header is retained verbatim: copyright 2026
Naganori Yamaguchi, Apache-2.0, author Naganori Yamaguchi (assisted by OpenAI
Codex). The existing Library files `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are retained unchanged; their SHA-256 values are
respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

These are data declarations with embedded construction proofs. No separate
source theorem, proposition target or proof artifact is asserted, and no
valued-field, reciprocity or class-formation result is claimed.
