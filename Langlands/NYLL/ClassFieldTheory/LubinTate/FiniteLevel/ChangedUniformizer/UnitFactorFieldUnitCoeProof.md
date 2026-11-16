# Unit-factor field-unit coercion proof

The theorem
`Langlands.NYLL.LubinTate.standardLubinTateUnitFactorFieldUnit_coe`
proves exactly the existing Library proposition
`Langlands.NYLL.LubinTate.standardLubinTateUnitFactorFieldUnit_coeStatement.{u, v}`.
Its sole import is the published statement module. The proposition universally
quantifies over `{K : Type u} [Field K]`, an explicit
`F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K`,
and `a : F.valuationSubringˣ`. It states

```lean
(Langlands.NYLL.LubinTate.standardLubinTateUnitFactorFieldUnit F a : K) =
  (a : F.valuationSubring)
```

The right-hand side is coerced further into `K`. The universes `u` and `v`
remain independent. There is no uniformizer, finite level or additional premise.
The statement and its published dependencies are reused unchanged.

## Implemented proof and simplification

The proof introduces the universally quantified field, field instance, chosen
local-field package and valuation-subring unit. It then applies Mathlib's
`ValuationSubring.coe_unitGroupMulEquiv_symm_apply` to that unit and the
inferred valuation subring.

The published M391.007 definition
`Langlands.NYLL.LubinTate.standardLubinTateUnitFactorFieldUnit F a`
applies the published M388.001 homomorphism
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.valuationSubringUnitsToFieldUnits`
to `F.toCompleteDVF` and `a`. For the actual chosen valuation subring `A`,
that homomorphism is
`A.unitGroup.subtype.comp A.unitGroupMulEquiv.symm.toMonoidHom`.
Consequently, its underlying field value is definitionally
`((A.unitGroupMulEquiv.symm a : Kˣ) : K)`. Mathlib's formula identifies
this value with the underlying field value of `a`; the proof needs no explicit
rewrites or auxiliary theorem.

The original M388.002 wrapper
`LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply`,
in `ValuationSubringUnitMap.lean`, lines 40–49, performs precisely this reduction
and invokes the same Mathlib theorem. The present proof uses that Mathlib
theorem directly; it introduces no duplicate M388.002 declaration.
In the approved Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, the formula is at
`Mathlib/RingTheory/Valuation/ValuationSubring.lean:514–515` and is proved by
`rfl`. Its inverse equivalence is defined at lines 499–507.

The source's coercion simplification behavior is retained through a private
`@[simp]` theorem, `standardLubinTateUnitFactorFieldUnit_coe_apply`. Its type
displays the source telescope and equality directly, and its proof is just
the exact closed-target theorem applied to `F` and `a`. This is a specialization
of the same assertion, not another source unit or prerequisite.

Putting `@[simp]` on the exact closed-target theorem alone registers the closed
proposition as true; it does not expose the equality for rewriting. The private
specialization registers the original coercion rewrite while the public theorem
keeps exactly the required statement type. No reducibility attribute on the
published statement is changed.

## Source correspondence and adaptations

The original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ChangedUniformizer.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ChangedUniformizer.lean>),
commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`, M391.008, lines 113–118.
The full file was read, including the universe and field context at
lines 43–49 and M391.007 at lines 105–109. Its SHA-256 is
`684df6d32cebe6a70087c9d6e4c9d70ae6913407f3c6d1ee2d70a6c975b912f7`.
The complete original `ValuationSubringUnitMap.lean` was also read; its
SHA-256 is `13e51b4e4cae7b9132808332f696efef9d971020781da19ca56c93249cf32084`.
These pinned sources are registered as
`external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`).
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement` (content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

| Source unit | Adapted theorem |
| --- | --- |
| M391.008, `LubinTate.standardLubinTateUnitFactorFieldUnit_coe` | `Langlands.NYLL.LubinTate.standardLubinTateUnitFactorFieldUnit_coe` |

Worker 328 made the following adaptations on 16 November 2026:

1. Extract only M391.008, prefix its namespace with `Langlands.NYLL`, and
   give its theorem exactly the existing closed statement type. Introduce the
   unchanged source telescope inside the proof; rename the bound unit to `a`.
2. Replace the twelve source imports with the focused statement import. Reuse
   the actual local-field package and the published M391.007/M388.001 maps.
3. Replace the source call to M388.002 by its underlying Mathlib theorem as
   explained above, following Worker 309's supplied and previously checked
   proof recipe. Worker 309 is credited as a coauthor of this adaptation.
4. Preserve the source's `@[simp]` behavior on the private specialization
   described above. Omit the unnecessary surrounding `noncomputable section`,
   replace the broad module overview with focused documentation, and add
   the modification notice and this proof correspondence.

The original 2026 copyright, Apache-2.0 and authorship header is retained
verbatim: Naganori Yamaguchi (assisted by OpenAI Codex). Existing
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained unchanged.
Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Verification scope

Development checks use environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0, and the Mathlib
commit above. The focused check inspects the exact theorem declaration.
A separate private example checks that `simp` uses the registered private
specialization to rewrite the coercion after importing this proof module.
Combined development check `8cc26e45-6c18-4518-a9c7-7fc254ca1840` passed with
zero errors or warnings. Its simplifier diagnostic names only that private
specialization; declaration inspection retains independent `u v` and reports
only `propext`, `Classical.choice` and `Quot.sound`.
Compilation is development evidence; independent semantic review and
Library publication are separate requirements.
