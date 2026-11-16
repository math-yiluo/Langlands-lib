# Proof of neutral lifting for exact sequences of unramified-field tori

`Langlands.BruhatTits.IntegralModels.unramifiedTorusNeutralSurjectivity`
proves the unchanged published proposition
`UnramifiedTorusNeutralSurjectivityStatement.{u}` at arbitrary universe `u`.
That proposition specializes Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Corollary B.8.6 (printed pp. 682–683 / PDF pp. 713–714),
to the maximal unramified field `K = inertiaFixedField F` and its ring of
integers `O = fixedFieldIntegers F`. Its exact formulation and provenance
are in the statement's paired Markdown.

## The Lean proof

The proof is one application of the published conditional reduction
`unramifiedTorusNeutralSurjectivityAssembly`. That reduction proves
`UnramifiedTorusNeutralSurjectivityAssemblyStatement`, the implication from
four premises to the target. Each premise is discharged by a published
Library theorem:

1. `ConnectedGenerationStatement` (KP Lemma A.4.26, affine form) is proved
   by `Langlands.GroupScheme.connectedGeneration`
   (`Langlands.GroupScheme.IntegralModel.ConnectedGenerationProof`);
2. `TorusQuotientRationalSurjectivityStatement` is proved by
   `Langlands.GroupScheme.torusQuotientRationalSurjectivity`
   (`Langlands.GroupScheme.Torus.QuotientRationalSurjectivityProof`);
3. `UnramifiedTorusNeutralFiniteGenerationStatement` is proved by
   `Langlands.BruhatTits.IntegralModels.unramifiedTorusNeutralFiniteGeneration`
   (`Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralFiniteGenerationProof`);
4. `TorusSurjectionIsogenySectionStatement` is proved by
   `Langlands.GroupScheme.torusSurjectionIsogenySection`
   (`Langlands.GroupScheme.Torus.SurjectionIsogenySectionProof`).

The theorem passes these four proofs, in this order, to
`unramifiedTorusNeutralSurjectivityAssembly`. All five results are stated
at the same universe `u`, so no universe is restricted. No hypothesis is
added and the conclusion is not weakened.

## How the argument runs

The mathematical argument lives in the assembly and its premises; their
paired Markdown files describe it in detail. In outline: the homomorphism
`q` extends to a homomorphism `ψ` of the neutral models over `O`. Its image
on integral sections is open, because `q` is smooth and the neutral integral
points are open. It has finite index, by rational surjectivity of `q`
(premise 2, with torus-cocycle vanishing over `K`), finite generation of
`B(K)` modulo the neutral integral points (premise 3) and an isogeny section
`s` with `q ∘ s = [n]` (premise 4). Lemma A.4.26 (premise 1), applied to the
geometrically connected target neutral model, then makes `ψ` surjective on
integral sections. This is the stated inclusion.

The source proof works over the completion with lft-Néron models and uses
Lemma A.4.25 and Lemma 8.1.2. The Lean route stays over the Henselian ring
`O` and uses Lemma A.4.26 instead, as explained in
`UnramifiedTorusNeutralSurjectivityAssembly.md`.

## Sources and provenance

Kaletha–Prasad (2023), registered `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:
Corollary B.8.6 and its proof, printed pp. 682–683 / PDF pp. 713–714, and
Lemma A.4.26, printed pp. 631–632 / PDF pp. 662–663. This module introduces
no new statement or definition.
