# Evaluation of the coordinate quotient equivalence

Worker 277; focused proof for Task 5954 revision 3.

Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, pinned at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, is the original source.
The source is [`NormalBasis.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasis.lean>),
lines 325–330 (unit M152.018), declaration
`LocalClassFieldTheory.chosenNormalBasisCoordinateQuotPiLinearEquiv_mk`.
The adapted theorem is
`Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisCoordinateQuotPiLinearEquiv_mk`;
its exact published target is
`Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisCoordinateQuotPiLinearEquiv_mkStatement`.

The fields `K` and `L` share universe `u`. The theorem retains `Field K`,
`ValuativeRel K`, `Field L`, `Algebra K L`, `FiniteDimensional K L`,
`TopologicalSpace K`, `IsNonarchimedeanLocalField K`, and the arbitrary function
`f : Gal(L/K) → 𝒪[K]`, in source order. As in the original theorem's explicit
`omit [IsGalois K L]`, no Galois instance is assumed. The two topology/local-field
instances are explicit theorem binders, matching the published target telescope
even though the equality itself uses only the underlying algebraic constructions.

The proof is `rfl`, as in the source. The target unfolds to evaluation of
`chosenNormalBasisCoordinateQuotPiLinearEquiv` on `Submodule.Quotient.mk f`.
Its published definition is Mathlib's `Submodule.quotientPi` for the constant
family of maximal ideals. The forward map sends a representative to the
function of its coordinate quotient classes, definitionally giving
`fun σ => Submodule.Quotient.mk (f σ)`. The original `[simp]` attribute is restored.
The sole direct import is the published `NormalBasis.CoordinateQuotientStatement`
module; it imports `CoordinateMaximalSubmodule` and Mathlib's local-field
definitions. The coordinate module imports Mathlib's quotient-of-products,
Galois and valuation-ring infrastructure.

Modifications to the source: prefix the namespace with `Langlands.NYLL`, import
only the published target module, omit unrelated declarations and unused
namespace openings, and state the theorem using the published proposition alias.
The source proof route and full theorem telescope are retained. The source
copyright, author and Apache-2.0 header is preserved; `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE` apply. No statement, definition or imported file is changed.

The readable source registrations are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
Development and formal validation use environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).
This support lemma discharges no host class-formation, cup, transfer, Tate or
reciprocity target.
