# Natural normalized second adjointness: proof

Author: Worker 733.

`Langlands.Parabolic.normalizedSecondAdjointness` proves the published
`Langlands.Parabolic.NormalizedSecondAdjointnessStatement.{uF,uV,uW}` from
`Langlands.Representation.Parabolic.SecondAdjointnessStatement`. Its type is
exactly that proposition. The field universe `uF`, the inducing-carrier universe
`uV` and the ambient-carrier universe `uW` stay independent. The theorem has no
additional parameters, typeclasses or hypotheses. It therefore proves both
`StandardSecondAdjointnessClause` (standard parabolics of `GL_n`) and
`RefinedSecondAdjointnessClause` (refined parabolics of a product Levi). Neither
the statement pair nor any pair it imports is changed.

## Proof

The proof is one term. It applies the published conditional assembly
`Langlands.Parabolic.SecondAdjointness.secondAdjointness_of_dualities` to two
published unconditional theorems.

- `Langlands.Parabolic.naturalNormalizedInductionDuality.{uF, uV}`
  (`Langlands.Representation.Parabolic.NaturalInductionDualityProof`) proves
  `NaturalNormalizedInductionDualityStatement.{uF, uV}`: natural same-parabolic
  equivalences `D(i_P σ) ≃ i_P(Dσ)` between the smooth dual of a normalized
  induced representation and the normalized induction of the smooth dual.
  These are given in both the standard and the refined case.
- `Langlands.Parabolic.naturalNormalizedJacquetDuality.{uF, uW}`
  (`Langlands.Representation.Parabolic.NaturalJacquetDualityProof`) proves
  `NaturalNormalizedJacquetDualityStatement.{uF, uW}`: natural equivalences
  `r_P(Dπ) ≃ D(r̄_P π)` from the upper normalized Jacquet module of the smooth
  dual to the smooth dual of the opposite normalized Jacquet module. These are
  also given in both cases.
- `secondAdjointness_of_dualities`
  (`Langlands.Representation.Parabolic.SecondAdjointnessAssembly`) takes the
  induction duality statement at `{uF, uV}` and the Jacquet duality statement
  at `{uF, uW}`. It returns `NormalizedSecondAdjointnessStatement.{uF, uV, uW}`.

The two duality statements are used only through these published proofs. The
closing theorem assumes neither of them. Lean reports only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

## The assembled equivalence

For admissible `σ` on the Levi and `π` on the ambient group, let `D` be the
Library's `smoothContragredient`. The assembly module defines the family as the
composite

\[
 \operatorname{Hom}(i_P\sigma,\pi)
 \xrightarrow{D} \operatorname{Hom}(D\pi, D(i_P\sigma))
 \xrightarrow{E_I\circ-} \operatorname{Hom}(D\pi, i_P(D\sigma))
 \xrightarrow{\text{first adj.}} \operatorname{Hom}(r_P(D\pi), D\sigma)
 \xrightarrow{-\circ E_J^{-1}} \operatorname{Hom}(D(r_{\bar P}\pi), D\sigma)
 \xrightarrow{D^{-1}} \operatorname{Hom}(\sigma, r_{\bar P}\pi).
\]

Here `E_I` and `E_J` are the equivalence families chosen from the two duality
proofs. The steps are:

- admissible Hom duality for the ambient group;
- induction duality;
- first adjointness
  (`Langlands.Representation.Parabolic.NaturalFirstAdjointness`);
- Jacquet duality;
- the inverse of admissible Hom duality for the Levi.

One family is fixed per realization and parabolic, before naturality is
checked. Naturality in `σ` comes from the naturality of `E_I` and of first
adjointness under induced maps. Naturality in `π` comes from the naturality of
`E_J` and of first adjointness under composition. In the standard case it is
stated with the pointwise opposite `Jacquet.map`; in the refined case it uses
`T.normalizedRefinedOppositeJacquetMap`. `SecondAdjointnessAssembly.md`
documents these proofs.

## Source

Bill Casselman, *Introduction to admissible representations of p-adic groups,
Chapter III: Induced representations and the Jacquet module*, revision
April 29, 2019, `casselman-2019-jacquet-module`. The ingredients are
Proposition III.1.1 (contragredient of an induced representation, pages 1–2),
Frobenius reciprocity III.3.5 (page 4) and the canonical pairing III.6.2–3
(pages 7–8). The natural family and its naturality proof are derived; that
chapter contains no verbatim theorem of this form.

## Scope

All quantifiers of both clauses are kept: every prime, `PadicField`, compatible
`TopologicalData`, positive rank, block shape and refinement. Every admissible
inducing and ambient representation is covered. Refined inputs are arbitrary
representations of the whole refined Levi and of the whole product Levi. The
normalizations are the statement's own: the positive upper half-modulus for
induction, with the inverse full modulus in the opposite normalized quotient.
This module does not prove generic multiplicity comparison or the irreducible
head.
