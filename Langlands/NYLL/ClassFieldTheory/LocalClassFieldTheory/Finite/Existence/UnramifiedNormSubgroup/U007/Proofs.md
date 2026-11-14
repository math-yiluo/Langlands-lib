# Evaluation of the multiplicative valuation modulo degree

`Langlands.NYLL.LocalClassFieldTheory.valuationModDegreeMulHom_apply`
proves exactly the published proposition
`Langlands.NYLL.LocalClassFieldTheory.valuationModDegreeMulHom_applyStatement`
at arbitrary universe `u`.

For every `K : Type u` with `[Field K] [ValuativeRel K] [TopologicalSpace K]`
and `[IsNonarchimedeanLocalField K]`, every `n : Nat`, and every `x : Kˣ`,
the theorem identifies `valuationModDegreeMulHom K n x` with
`Multiplicative.ofAdd` of the integer
`LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x)`
cast to `ZMod n`. No restriction on `n` is imposed, so this includes `n = 0`.

## Implemented proof

The proof introduces the field, its four instance parameters, the modulus,
and the unit from the closed statement, then uses `rfl`. The published
`valuationModDegreeMulHom` is `AddMonoidHom.toMultiplicativeRight` of
`valuationModDegree`; the latter is the composition of `Int.castAddHom`
with the published `valuationMap`. Evaluation of those constructions
reduces definitionally to the displayed expression, including the
`Additive.ofMul` and `Multiplicative.ofAdd` tags.

The only import is the published
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.MultiplicativeStatements`.
The target and its imported data are reused unchanged. No helper declaration
or instance is introduced. The original `simp` attribute is retained.

## Source correspondence and attribution

This adapts M266.007, source theorem
`LocalClassFieldTheory.valuationModDegreeMulHom_apply`, lines 78–83 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`
in Naganori Yamaguchi's ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`. The source theorem uses `rfl`.
The original header and relevant source definitions and theorems through
line 125 were read. The source file SHA-256 is
`ed3c13cfacb92012fb235f48817d5f23a043588ef78d7b2ed2e7ef4afa533b12`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the source
path above. No applicable project errata entry was found.

Worker 530 extracted this theorem, prefixed its namespace with
`Langlands.NYLL`, replaced the original imports with the focused published
target, and stated its type as that exact closed proposition. Introducing
the proposition's telescope recovers the source formula with its original
universe, parameter order, and hypotheses; the equality proof remains `rfl`.
No earlier adaptation or another worker's draft proof was reused.

The original copyright and author header is retained with a modification
record. The Apache-2.0 license and notices are already published in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

## Validation

The focused Lean-service check in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled this module with zero errors
and warnings. Declaration inspection confirmed theorem kind, universe
parameter `u`, and only the standard assumptions `propext`, `Classical.choice`,
and `Quot.sound`. Independent semantic review and exact-target validation
remain requirements for publication.
