# NYLL M110.013: the constructed subring is the integral closure

This file proves the exact published target
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_isIntegralClosureStatement`
under the required source-adapted theorem name, obtained by removing
`Statement` from that name.

Let `K` and `L` be fields with an arbitrary `K`-algebra structure, and let
`vK` be a valuation in an independently universed ordered value group.
Assume `hval`: every element of `L` or its inverse lies in the actual
integral closure of `vK.valuationSubring` in `L`. Then the valuation subring
`B := integralClosureValuationSubringOfMemOrInv vK hval` satisfies
`IsIntegralClosure B vK.valuationSubring L`. The theorem retains the exact
section parameters, universes, explicit `vK` and `hval`, and the target's
local `let B`. It adds no finite-dimensional, discrete or Henselian premise.

The proof constructs the two fields of `IsIntegralClosure`. The map from
`B` to `L` is the subtype inclusion, so `Subtype.coe_injective` proves its
injectivity. For each `z : L`, membership in `B` is definitionally membership
in the actual integral closure, hence definitionally `IsIntegral
vK.valuationSubring z`. An integral element therefore gives the witness
`⟨z, hz⟩ : B`, whose image is `z` by reflexivity. Conversely, an element
in the image of `B` is integral by its subtype property. These two directions
give `isIntegral_iff`.

The only import is the unchanged published
`IntegralClosureValuationSubringStatements` module, which imports the actual
construction and Mathlib's integral-closure and valuation APIs. There are no
other NYLL proof dependencies or private helper declarations. The source uses
M110.010 to express the same carrier equivalence; this implementation unfolds
the construction directly. The source also installs a local
`HasExtension` instance using M110.012. That binding is unused by
`IsIntegralClosure B vK.valuationSubring L`, whose algebra requirements are
the maps of the two rings into `L`. The published statement already erases
this unused binding, and this proof needs no replacement for it. No global
instance or axiom is introduced. Worker 194 contributed guidance on this
direct proof route.

The pinned source is Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean`,
lines 282–310 (declaration), with section context at lines 21–33.
The source name
`ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_isIntegralClosure`
is prefixed by `Langlands.NYLL`.

The readable original is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean`,
SHA-256 `8f2d21dcbef11b6354d840a350ea2ddf775b670d74581bf9469d499afbe34dad`.
It belongs to registered source `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`,
also recorded by `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

The Lean file preserves the original copyright, author and Apache-2.0 header,
and records the namespace, import and proof changes by Worker 199 on
13 November 2026. The retained license and notices are
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`, with SHA-256 respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The checking environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).
