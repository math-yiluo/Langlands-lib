# Galois ambient units and intermediate-field unit inclusion

This module extracts M088.001–002 from Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean#L31-L45),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The enclosing
`noncomputable section` is at line 31 and the shared parameter declaration
at line 33. The first declaration, including its docstring, occupies
lines 35–38; the second occupies lines 40–45. The complete original file
has SHA-256
`392d08ca1431117423181ba326721905cc060686d340ba471b6838f85dd3ebfc`.

The registered source is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The public inventory is `notes/reuse/nyll-public-port/m073-m096.md`,
section M088; that inventory records no patch10 change for this module.
No applicable NYLL or Yamaguchi erratum was found in the Library errata
lookup.

## Complete interfaces and mathematical meaning

With namespace `Langlands.NYLL.LocalClassFieldTheory` open, the full
interfaces and literal bodies are:

```lean
abbrev galoisAmbientUnitsRep
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] :
    Rep ℤ (Gal(Ω / K)) :=
  Rep.ofAlgebraAutOnUnits K Ω

noncomputable def intermediateFieldUnitsToGaloisAmbient
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    (E : IntermediateField K Ω) :
    Additive Eˣ →+ Additive Ωˣ :=
  MonoidHom.toAdditive (Units.map E.val.toRingHom)
```

Both field parameters are explicit and lie in universe zero, exactly as
the source's `Type` binders specify. In each declaration the two field
instances precede the algebra instance. The second declaration additionally
takes the explicit intermediate field `E` after those instances. There are
no universe parameters and no Galois, finiteness, valuation, topology,
local-field or characteristic assumptions. In particular, the source's
`variable [IsGalois K Ω]` at line 55 is outside this extraction.

`galoisAmbientUnitsRep K Ω` is the bundled integral representation of
`Gal(Ω/K) = Ω ≃ₐ[K] Ω` on `Additive Ωˣ`. It directly reuses Mathlib's
`Rep.ofAlgebraAutOnUnits` from
`Mathlib/RepresentationTheory/Rep/Basic.lean`, lines 388–391.
An automorphism acts on a unit by applying the automorphism to its value
and inverse; `Additive` writes the commutative unit group additively.
Thus this is an algebraic group representation; its definition supplies
no topological continuity assertion.

`intermediateFieldUnitsToGaloisAmbient K Ω E` is the additive homomorphism
obtained from the inclusion `E.val : E →ₐ[K] Ω`. Its value at
`Additive.ofMul x`, for `x : Eˣ`, is definitionally
`Additive.ofMul (Units.map E.val.toRingHom x)`. `Units.map` supplies the
multiplicative homomorphism and its laws, and `MonoidHom.toAdditive`
transports that homomorphism to the additive type tags. These existing
Mathlib constructors are used directly; this module adds no replacement
unit group, representation structure or instance.

## Source-to-public declaration map

| Unit | Source declaration | Public declaration |
| --- | --- | --- |
| M088.001, lines 35–38 | `LocalClassFieldTheory.galoisAmbientUnitsRep` | `Langlands.NYLL.LocalClassFieldTheory.galoisAmbientUnitsRep` |
| M088.002, lines 40–45 | `LocalClassFieldTheory.intermediateFieldUnitsToGaloisAmbient` | `Langlands.NYLL.LocalClassFieldTheory.intermediateFieldUnitsToGaloisAmbient` |

This is the complete map for the extracted unit. The source's application
theorem at lines 47–53, fixed-subgroup theorems and later equivalences are
outside its scope. They require separate statement and proof publications.
These two data definitions establish no host class-formation, cup, Tate,
transfer or cohomological reciprocity target.

## Modification and import record

Worker 169 made the following changes on 12 November 2026:

1. Move the extracted pair from the original module to
   `Langlands/NYLL/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField/Initial/Definitions.lean`
   and prefix its enclosing `LocalClassFieldTheory` namespace with
   `Langlands.NYLL`.
2. Retain the original copyright and author header verbatim. Replace the
   original whole-file module documentation at lines 11–23 with documentation
   for this initial pair and an explicit modification notice.
3. Remove the original imports at lines 7–8,
   `Nyll.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup`
   (M087) and `Nyll.GaloisCohomology.Kummer.Abstract.KummerDelta` (M023).
   Neither declaration uses either module's constants. Import
   `Mathlib.FieldTheory.Galois.Notation` directly for `Gal(Ω/K)` and
   `Mathlib.FieldTheory.IntermediateField.Basic` for intermediate fields
   and their inclusion homomorphisms. Retain the original line-9 import
   `Mathlib.RepresentationTheory.Rep.Basic`.
4. Remove the line-27 namespace openings
   `RamificationTheory KummerTheory CyclicCohomology`, which the extracted
   definitions do not use. Retain the `noncomputable section` and close it
   immediately after the extracted pair.

The original shared parameter declaration, both declaration docstrings,
the `abbrev`/`def` distinction, result types and literal bodies are
unchanged. No compatibility patch, proof, additional hypothesis or
global/local/scoped instance is introduced. Canonical Mathlib instances
provide all structures used here.

The approved checking environment is
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`, Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
Focused builds with inspection of each declaration succeeded with zero
errors and warnings. Both inspections report a data definition with an
empty universe-parameter list, establishing the intended universe-zero
boundary and the sufficiency of these Mathlib-only imports.

## Attribution

Copyright (c) 2026 Naganori Yamaguchi
(`https://github.com/n-yamaguchi-0729`), all rights reserved.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex).
Released under Apache-2.0. The original header is retained verbatim in
the Lean file.

The existing [LICENSE](../../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are preserved
and byte-identical to the pinned originals. Their respective SHA-256 values
are `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The original module has no entry in the root NOTICE's third-party path
inventory. Worker 169 extracted the pair, checked its source correspondence
and wrote this documentation.
