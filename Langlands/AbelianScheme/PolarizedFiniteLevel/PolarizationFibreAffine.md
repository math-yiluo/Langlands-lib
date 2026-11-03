# Affine fibre neighbourhoods from the fixed polarization bundle

This internal application starts with an actual abelian scheme `A` over
`S : Scheme.{u}`, the published `Prerequisites.{u}` package `P`, a selected
`DualWitness A` called `W`, and an actual homomorphism
`lam : A ⟶ W.dual P` satisfying the existing `W.IsPolarization P lam`.
The fixed global line bundle is
`poincareDiagonalBundle A W.hasDual (W.parameterMap P lam)`.
No dimension, degree, finite level or order action is needed for its fibre
ampleness.

`P` retains the published tensor preservation and coherence, Mumford
Picard-zero, universal Picard base change, Picard-zero pullback, dual
base-change compatibility, and polarization base-change statements.
`W` retains representability, geometry and an inverse-evaluation witness for
this selected dual. These conditional prerequisites are not constructed here.

`DualWitness.diagonalBundle_isAmple_overField` works over any field
`K : Type u`. It evaluates the given relative polarization at an algebraic
closure `F` and the canonical map `b : Spec F → Spec K`. The published
`poincareDiagonal_isAmple_of_fieldPresentation` makes the diagonal bundle of
the canonically changed map ample over `F`. The actual
`poincareDiagonalBaseChangeIso` identifies it with the pullback of the fixed
bundle. The published `fieldBaseChangeAmpleReflection` then proves ampleness
of that same bundle over `K`. Thus the field need not be algebraically
closed. This generalizes the argument of `Datum.canonicalBundle_isAmple`
without requiring an ordinary polarized finite-level datum.

`DualWitness.diagonalBundle_isAmple_onFibre` applies this result at every
point `s : S`, including nonclosed points. Set
`b := S.fromSpecResidueField s`, use the published pullback dual witness and
pullback polarization map, and invoke the full
`P.polarizationBaseChange` statement to prove its existing polarization
predicate. The field result supplies ampleness over `S.residueField s`.
`DualWitness.parameterMap_pullbackMap` identifies its classifier with the
canonical dual base-change classifier.
`poincareDiagonalBaseChangeIso` then identifies its bundle with the actual
pullback of the fixed global bundle by `A.X.hom.fiberι s`, the inclusion of
the scheme-theoretic fibre.

The remaining three declarations explicitly assume the entire proposition
`ProperFibreAmpleAffineOpenStatement.{u}` and a locally noetherian base:

- `DualWitness.forall_finset_fibre_affine` applies that proposition to the
  actual proper structure map `A.X.hom`, the fixed global bundle, and the
  preceding fibre-ampleness proof. Every finite set of points of the total
  space lying over a single `s` therefore lies in an affine open of the
  total space.
- `DualWitness.nonempty_quotientData` applies the published
  `FiniteEtaleQuotientExistence.nonempty_quotientData_of_forall_finset_fibre`.
  It gives `Nonempty K.QuotientData` for any actual finite étale subgroup
  `K` of `A`, under the same explicit generic geometric premise.
- `DualWitness.integralOrderModel` additionally takes
  `TorsionFiniteEtaleStatement.{u}`, a map from `S` to the spectrum of a
  characteristic-zero field in universe `u`, a ring `O : Type v` with a
  specified finite integral basis indexed in universe `u`, and an actual
  rational action `α : O →+* Rationalization.End A`. It applies the published
  `integralOrderModelOfForallFinsetFibre` to the affine-open criterion just
  obtained. Its result is the existing `IntegralOrderModel α`, with an
  actual integral order action, positive integral inverse-multiple data,
  forward finite étale isogeny and rational equivariance.

The provenance is an internal assembly of published fixed-bundle ampleness,
canonical base change, quotient and order-saturation constructions.
The generic proper-family fibre-ampleness theorem remains a premise of the
last three declarations; no proof of it is supplied here. The first two
ampleness lemmas require neither it nor a noetherian hypothesis. This module
does not assert a global relatively ample presentation, transport a
polarization to the constructed integral model, or prove CM
representability.
