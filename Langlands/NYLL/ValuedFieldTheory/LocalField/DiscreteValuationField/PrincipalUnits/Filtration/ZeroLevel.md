# NYLL M225.008: the zero-level proof

For a complete discrete valuation field, the level-zero principal-unit
subgroup is the whole unit group of its valuation ring.

## Target and implemented proof

The theorem
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top`
has type
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_topStatement F`,
with `{K : Type u} [Field K]` and explicit
`F : Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.{u,v} K`.
Its target is exactly the equality `higherPrincipalUnitGroup F 0 = ⊤`.

The proof unfolds the statement wrapper and applies subgroup
extensionality. Membership in the left side reduces to
`(u : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ 0`.
Simplification replaces the zeroth power by the top ideal and proves
membership there and in the top subgroup. This is the original
extensionality and simplification route, with no appeal to
M225.002–.007.

## Provenance and modifications

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnits/Filtration.lean`,
M225.008, declaration at line 175, equality at line 176, and proof
at lines 177–178. Its parameters come from lines 40 and 85.
The source file SHA-256 is
`26c1fdb63f9766b4dd8e6f43e2c7c0d97593a3afb0df2e9d5b8a129d0f5ed4bb`.
Registered source `external-lean-reuse-snapshots-2026-10-21` has fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

Worker 311 extracted a focused module, added the `Langlands.NYLL`
namespace prefix, imported the target, and expressed the theorem's type
using that proposition. It unfolds the added wrapper before the original
proof. The source theorem's `simp` attribute, universes and parameters
are retained. Unused source opens and the noncomputable section are
omitted. The module comment and docstring are new.
No additional definition, helper theorem or global instance is introduced.
Worker 474 submitted the Lean file unchanged and added the following
section to this Markdown.

## Effect of the retained `simp` attribute

Because the theorem's type is the `Prop`-valued wrapper
`zero_eq_topStatement F`, rather than the bare equation, the retained
`simp` attribute does not act as the source rewrite rule
`higherPrincipalUnitGroup F 0 = ⊤`: `simp` does not unfold the wrapper
when it registers the lemma. In a development check,
`simp only [higherPrincipalUnitGroup.zero_eq_top, Subgroup.mem_top]`
and plain `simp` both made no progress on the goal
`x ∈ higherPrincipalUnitGroup F 0`. The mathematical content is
unaffected: the term `higherPrincipalUnitGroup.zero_eq_top F` checks
against the type `higherPrincipalUnitGroup F 0 = ⊤` by unfolding the
definition, so a consumer can rewrite with
`show higherPrincipalUnitGroup F 0 = ⊤ from higherPrincipalUnitGroup.zero_eq_top F`.

The original copyright and author header is retained, with the
Apache-2.0 license and attribution in the existing
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
