# Density of attached form classes from one nonzero attached form

This module concerns the positive-central rational quotient of `GL_{r+1}`. It uses the data of
`GeneralLinearCuspidalSummandRealizationStatement`: the number field with compact adele
quotient, `ParabolicDynamicStatement`, the central split torus with finite-index injective
character restriction, and right-invariant norm-one Haar measure. Let `S` be the full
almost-everywhere cuspidal `L²` subspace and `πc` its right action.

- `GeneralLinearSummandFormsNonzeroStatement` asserts the following for every nonzero closed
  `πc`-invariant subspace `P` of `S` that is minimal among such subspaces. The submodule
  `summandForms F r T i (P.map S.subtype)` is nonzero. These are the stable automorphic
  functions that are pointwise cuspidal in the matrix model and have an actual quotient class
  (`IsGeneralLinearFormClass`) lying in `P`.
- `GeneralLinearSummandFormsDenseOfNonzeroStatement` is the implication from that
  statement to the published density input `GeneralLinearSummandFormsDenseStatement`.
  `generalLinearSummandFormsDenseOfNonzero` proves it.

## Implemented proof

Fix `P` and use the differential stability proof `generalLinearSummandFormsEnveloping`. Then the
attached forms are the operator realization `V = summandRealization …`. Composing
`summandClassMap` with the inclusion of `S` gives the class map `jV`. Let `H` be the closure of
its range in quotient `L²`.

- `H` lies in the closed subspace `P.map S.subtype`, since every class lies in `P` and `S` is
  closed.
- By the proved `generalLinearQuotientFormClassClosure`, `H` is invariant under the full adelic
  bounded action, which on `S` is `πc`. Its trace `P'` on `S` is therefore a closed invariant
  subspace of `P`.
- A nonzero attached form has a nonzero class. If the class were zero, the zero class and the
  given class would have continuous representatives equal almost everywhere. Because the
  canonical quotient Haar measure is positive on open sets, the two representatives are equal.
  So the form would be zero.

Minimality gives `P' = P`. Every vector of `P` therefore lies in the closure in `L²` of the
attached classes. The subtype embedding identifies closure in `S` with the preimage of closure
in `L²`, giving exactly the closure required by the density statement.

## Provenance and scope

This derived step isolates the existence part of Getz–Hahn, *An Introduction to Automorphic
Representations*, Springer GTM 300 (2024), Lemma 9.7.2 and Theorem 9.7.3, pp. 264–267 (PDF
pp. 276–279). Getz–Hahn argue density through smooth `K`-finite vectors. Here, density follows
from one nonzero attached form, by invariance of the closure under the whole adelic group,
which uses analyticity of scalar coefficients, together with irreducibility of `P`. The module
does not prove the existence statement. That remains the analytic core: smoothing, finiteness
under the centre and compact group, growth and cuspidality of a continuous representative.
