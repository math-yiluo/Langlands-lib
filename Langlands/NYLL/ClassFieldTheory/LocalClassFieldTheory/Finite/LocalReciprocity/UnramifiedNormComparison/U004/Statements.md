# NYLL M267.004: canonical comparison proposition target

`Langlands.NYLL.LocalClassFieldTheory.normQuotientToUnramifiedNormQuotient_surjectiveStatement`
is the closed proposition target for source unit M267.004.
The named comparison homomorphism from the actual norm quotient to the valuation-divisibility quotient is surjective.

The map is the named
`Langlands.NYLL.LocalClassFieldTheory.normQuotientToUnramifiedNormQuotient`,
imported from `UnramifiedNormComparison.U002.Definitions`. Its domain is the
actual `NormQuotient K L`, and its codomain is
`Kˣ ⧸ unramifiedNormSubgroup K (Module.finrank K L)`. No existentially supplied
map or assumed conclusion is part of the proposition. This module defines
the target; the original proof is a separate obligation.

## Scope and parameters

The definition quantifies over the original `K L : Type`, so it has no
universe parameters. It retains all fifteen instance arguments in source
lines 34–44: field, valuation relation, topology and nonarchimedean-local-field
structure on each field; an algebra structure, finite dimensionality and
Galoisness; extension of the valuation; the actual integral-closure and
finite-module structures on `𝒪[L]` over `𝒪[K]`; and the published
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L`.
The M267.003 computation additionally quantifies over `x : Kˣ`; the other
two comparison targets have no unit argument. The source's hypotheses are
neither weakened nor strengthened, and no global instance is introduced.

The only explicit import is the canonical map's focused module. It supplies
all the named quotient objects and the unramifiedness class through its
published dependencies. Their contents are reused by Lean name.

## Source correspondence and modifications

Original declaration: `LocalClassFieldTheory.normQuotientToUnramifiedNormQuotient_surjective` at lines 81–92
(statement lines 82–84) of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormComparison.lean` at commit
`fbd320cd8b1b06487c58227e92eb135794267709`. The complete file SHA-256 is
`a955313b05e5cdeb8bd4e9c6c76e466c956fe7231bb6fd90f4945a57e564ad26`.
The readable pinned copy is in registration
`external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`),
under `n-yamaguchi-0729--ClassFieldTheory/source/`; the attribution supplement
is `nyll-classfieldtheory-fbd320cd-supplement`.

Worker 205 made these changes on 16 November 2026:

1. Prefix the source namespace with `Langlands.NYLL` and append `Statement`
   to the declaration name.
2. Turn the theorem conclusion into a `def` returning `Prop`, universally
   quantifying the unchanged source telescope. Retain the source docstring.
3. Omit the source proof and any simp attribute; the exact theorem and its
   attributes belong to the focused proof successor.
4. Replace the broad source imports by the adapted M267.002 data module and
   omit unrelated source declarations and the noncomputable section.
5. Retain the original copyright and author header, add the dated modification
   record and a focused module docstring, and write this explanation.

The retained Apache-2.0 license and attribution notices are
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
