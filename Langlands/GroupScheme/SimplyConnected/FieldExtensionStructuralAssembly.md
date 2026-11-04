# Conditional field-extension assembly using proved preservation and splitting

Author: Worker 416.

This internal assembly supplies four published theorems to the existing
cover-existence and simple-connectedness reductions:

- `Langlands.FieldTheory.finiteGaloisTensorDecomposition` gives the actual
  finite Galois tensor equivalence and its pure-tensor formula.
- `isSemisimpleFieldExtension` proves semisimplicity under arbitrary field
  extension.
- `torusFiniteGaloisSplitting` gives a finite Galois splitting extension for
  every actual field torus.
- `centralIsogenyBaseChange` preserves central isogenies under arbitrary
  morphisms of base schemes.

These four facts are proved imports. The new deductions retain the remaining
structural inputs as hypotheses. They do not prove the unconditional
`IsSimplyConnectedFieldExtensionStatement`.

## Cover existence

`simplyConnectedCoverExistence_of_descent_and_splitCover` is a proof-valued
definition with four explicit inputs:

1. Full tensor cover descent,
   `SimplyConnectedCoverTensorDescentStatement.{u,u}`.
2. Split simply connected cover existence,
   `SplitSimplyConnectedCoverExistenceStatement.{u}`.
3. The central-cover universal property,
   `SimplyConnectedCentralCoverUniversalProperty.{u}`.
4. Maximal-torus preservation,
   `MaximalTorusBaseChangeStatement.{u}`.

It constructs the seven-component input conjunction for
`simplyConnectedCoverExistence_of_finiteGaloisInputs`. The published torus
splitting and tensor decomposition theorems supply two components. For the
finite Galois semisimplicity component, introduce the fields, their instances,
the group and its semisimplicity proof, then apply
`isSemisimpleFieldExtension`. The finite-dimensionality and Galois instances
are unnecessary for this unrestricted theorem. The four displayed inputs
supply the other components.

The conclusion is `SimplyConnectedCoverExistenceStatement.{u}` over
arbitrary fields. The actual splitting, cover construction and full-cover
descent are those of the imported finite Galois reduction. This definition
does not prove its four input propositions.

## Simple-connectedness ascent

`isSimplyConnectedAlgebraicClosureAscent_of_descent_and_splitStructure`
is a proof-valued definition. It takes the same four inputs and three more:

5. `RootDatumExistenceStatement.{u}`.
6. Integral coroot-span necessity,
   `SplitSimplyConnectedCorootSpanStatement.{u}`.
7. Integral coroot-span sufficiency,
   `SplitCorootSpanSimplyConnectedStatement.{u}`.

It applies
`isSimplyConnectedAlgebraicClosureAscent_of_fullCoverDescent` to those seven
inputs, `isSemisimpleFieldExtension` and `torusFiniteGaloisSplitting`.
The imported tensor assembly already supplies
`Langlands.FieldTheory.finiteGaloisTensorDecomposition`. The conclusion is
`IsSimplyConnectedAlgebraicClosureAscentStatement.{u}`.

`isSimplyConnectedFieldExtension_of_descent_and_splitStructure` has the same
seven explicit inputs and concludes
`IsSimplyConnectedFieldExtensionStatement.{u}`. It applies the existing
`isSimplyConnectedFieldExtension_of_fullCoverDescent_and_corootCriterion`,
supplying the semisimplicity, central-isogeny and torus-splitting proofs.
That imported deduction uses the closure-ascent and geometric/coroot
reductions to reach the unchanged final statement.

The local `linter.defProp` settings follow the proof-valued-definition
convention of the imported internal reductions. They affect linting only.

## Scope and provenance

The universe `u` remains arbitrary. The full tensor descent input uses index
universe `u`, matching the Galois group in the imported finite Galois step.
The final extension has no perfection, separability, algebraicity,
finiteness, characteristic or algebraic-closure restriction. Finite Galois
extensions occur as auxiliary splitting extensions within the reductions.

All predicates and pullbacks are the published ones. Semisimplicity keeps
the full possibly nonreduced centre. Central isogenies retain the full
scheme-theoretic kernel tested on all schemes. Every extension of a group
or arrow uses the actual `GroupScheme.baseChange` functor. Full descent
applies to the supplied universal cover over the auxiliary splitting
field; the reductions do not assume arbitrary extension-field groups or
isogenies descend.

The provenance is direct internal composition of the five imported public
modules and their named theorems. No private proof is imported and no
existing interface is changed. Independent proofs of the four
cover-existence inputs, and of the additional three inputs for ascent, are
still needed to obtain unconditional conclusions.
