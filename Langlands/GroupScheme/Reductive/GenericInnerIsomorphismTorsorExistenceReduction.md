# Reduction of integral inner-isomorphism torsor existence

The primary definition
`Langlands.GroupScheme.GenericInnerIsomorphismTorsor.ofExistenceStatements`
selects an actual integral inner-isomorphism torsor for a supplied DVR,
fraction field, reductive groups, and prescribed generic isomorphism.
It takes four explicit existence proofs as inputs.
The supporting internal theorem
`Langlands.GroupScheme.genericInnerIsomorphismTorsorExistence_of_affineQuotient_and_outerGeometry`
proves that those four existence statements imply
`Langlands.GroupScheme.GenericInnerIsomorphismTorsorExistenceStatement.{u}`
in every universe:

- `RelativeAdjointQuotientExistenceStatement.{u}`, constructing an actual
  affine full-centre fppf quotient over every scheme;
- `GenericIsomorphismSchemeExistenceStatement.{u}`, constructing the
  actual all-test isomorphism scheme for the generically isomorphic
  reductive DVR groups;
- `GenericOuterIsomorphismSchemeExistenceStatement.{u}`, constructing an
  actual fpqc outer quotient for every supplied full-centre quotient and
  isomorphism scheme in this situation;
- `FiniteGenericOuterClassExistenceStatement.{u}`, constructing finite
  scheme data containing the outer class of the prescribed generic
  isomorphism for every supplied outer quotient.

All four are hypotheses of the theorem and inputs to the constructor.
This module proves none of them unconditionally.

## Implemented proof

Fix the original statement's arbitrary DVR `R`, its specified fraction
field `K`, reductive groups `G` and `H`, and actual generic isomorphism
`f`. The imported
`ReductiveRelativeAdjointQuotientExistenceStatement.of_affine` first
upgrades the affine-quotient hypothesis to a reductive full-centre
quotient and selects its actual `A`, `q`, and quotient data. Its
supplied-quotient reductivity proof imposes no smoothness condition on the
centre.

Apply the isomorphism-scheme hypothesis to these same `R`, `K`, `G`, `H`,
and `f`. Apply the outer-quotient hypothesis to that representing scheme
and the selected `A`, `q`, and quotient data. Apply the finite-class
hypothesis to those same choices and the same prescribed `f`. Its
conclusion retains the full natural local family of `f` through the
classifying point.

`GenericInnerIsomorphismTorsor.ofOuter` then produces the original exact
torsor data from these witnesses. The DVR supplies its valuation-ring
hypothesis. The constructor supplies the actual quotient and compatible
actions, the fpqc parameter scheme and invertible shear, natural
isomorphisms on every test with inverse-precomposition compatibility,
and a generic point evaluating to exactly `f`. Packaging that object in
`Nonempty` is the original conclusion.

## Selected torsor data

`GenericInnerIsomorphismTorsor.ofExistenceStatements` applies the supporting
theorem to its four existence proofs and its original `R`, `K`, `G`, `H`,
`hG`, `hH`, and `f`. It uses `Classical.choice` on the resulting
`Nonempty (GenericInnerIsomorphismTorsor R K G H f)`. Its return value is
the actual torsor structure, including its quotient, actions, parameter
scheme, natural isomorphisms, and prescribed generic point.
The definition is noncomputable because it selects these data from a
proposition. Its result retains the exact supplied `f` in its type.

## Provenance and hypotheses

This is internal composition of the imported existence propositions,
supplied-quotient reductivity upgrade, and supplied-geometry constructor.
The data constructor selects the result of that composition. The module
introduces no new source-dependent assertion or geometric
construction. The target statement and its imported Lean/Markdown pairs
are used as they are.

There is no henselian, completeness, finite-residue, splitting, or
characteristic assumption in the conclusion. The four global existence
hypotheses are explicit inputs to this conditional reduction. The Library
proves them (`relativeAdjointQuotientExistence`,
`genericIsomorphismSchemeExistence`, `genericOuterIsomorphismSchemeExistence`,
`finiteGenericOuterClassExistence`), and `genericInnerIsomorphismTorsorExistence`
(`Reductive/GenericInnerIsomorphismTorsorExistenceProof`) applies this reduction
to those proofs.
