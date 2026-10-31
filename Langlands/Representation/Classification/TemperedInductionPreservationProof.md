# Preservation of analytic temperedness by actual normalized GL induction

Author: Worker 540.

`Langlands.glTemperedInductionPreservation` proves exactly the published
`Langlands.GLTemperedInductionPreservationStatement.{uF,uV}` from
`Langlands.Representation.Classification.TemperedInductionPreservationStatement`.
It retains every prime, finite p-adic field, supplied topology, positive total
rank, actual block shape, Borel measurable realization, supplied input Haar
measure, complex carrier and representation in that proposition. The field
and carrier universes are independent.

The proof composes published analytic necessity, algebraic preservation of
weak upper Jacquet bounds, and the ambient analytic exponent criterion.
The induction is the actual standard upper parabolic function space with
positive half-modulus covariance and right translation.

## Admissibility and the scalar character of induction

Write `ht : IsTemperedModCenter σ μ` for the hypothesis at the supplied single
Haar measure on the quotient of `B.Levi F.Carrier` by its full center.
Its admissibility component and
`Parabolic.normalizedInductionAdmissibility` prove admissibility of
`T.normalizedParabolicInduced B σ` independently of the desired analytic
conclusion.

The same hypothesis contains a unitary full-center character `c` acting on
`σ`. Restrict its character along `B.diagonalScalarToCenter F.Carrier`:
the resulting `ω` evaluates `c` on the common scalar in every Levi block.
The action identity `c.acts` and
`T.hasScalarCharacter_normalizedParabolicInduced` give the scalar-action
premise for the ambient criterion. That published theorem proves the
covariance calculation on the actual induced functions; the positive
half modulus is one on these scalars.

The criterion requires this scalar-action identity. Its proved reverse
implication constructs the full unitary central-character datum in the
analytic conclusion. Thus the assembly needs no additional central-character
or unitarizability hypothesis.

## From the supplied Levi measure to every ambient measure

`glProductLeviTemperedExponentNecessity`, by Workers 819 and 219, consumes
`hσ` and exactly `ht` with the supplied `μ`. It proves the upper refined
Jacquet bounds for every source refinement, using actual flattened Levi
and block-scalar maps and open-kernel generalized characters with a common
finite power. The chamber is increasing separately within each original
block of `B`.

This necessity theorem obtains the bounds directly from smooth-dual
coefficients and disjoint cells on the actual quotient by the full product
center. Its proof uses the supplied `L^(2+ε)` memberships. The present
assembly makes no change of the input measure and assumes no tensor
presentation of `σ`.

`glInductionWeakJacquetBounds`, by Worker 828, applies to those source bounds
and yields the entire numerical right side of the ambient exponent
criterion. Its proof uses the actual normalized geometric lemma of Workers
164 and 194, finite-filtration detection of generalized characters, evaluation
on geometric pieces, admissible fixed-space character extension and inverse
Weyl chamber coordinates. These published results keep the upper
inverse-half-modulus Jacquet normalization and cancel the induction half
modulus on the required scalars.

Finally, the reverse implication of `glTemperedExponentCriterion`, assembled
by Worker 349 with Workers 819, 219 and 851, converts those bounds to the
unchanged `T.IsTempered` predicate. It applies at carrier universe
`max uF uV`, the universe of the actual induced function space.
Its admissibility and scalar-action premises were proved above.

That criterion's analytic sufficiency uses the published coefficient
estimates, central-quotient Cartan cells and convergent lattice sums.
Its one-block group equivalence and full-center quotient transport prove the
conclusion for every ambient Borel Haar measure. Consequently the conclusion
retains all actual smooth-dual coefficients and every real `ε > 0` in the
original analytic predicate. No Haar-choice invariance premise or analytic
comparison remains in the theorem.

## Provenance and scope

This is an internal composition of the named published theorems. The
original source for the unchanged target is Silberger, *Introduction to
Harmonic Analysis on Reductive p-adic Groups* (1979),
`silberger-1979-harmonic-analysis`, Lemma 4.5.15, printed p.191, with the
input notation on p.190. The original pages were read and visually checked;
their retained PDF has SHA256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.

The implemented route follows the exponent argument of Waldspurger,
*La formule de Plancherel pour les groupes p-adiques d'après Harish-Chandra*
(2003), `waldspurger-2003-plancherel`, III.2.2–III.2.3,
printed pp.265–267. Those original pages were read; the retained PDF has
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
No source-specific errata file for either registered original was found in
the supplied public Library notes or project notes on 2026-10-31.
The complete target Markdown and the parent's analytic-convention
explanation were read. The formal analytic bridges are supplied by the
published necessity and criterion proofs described above.

The original irreducibility premise is retained and passed to the two
published bound theorems. The result asserts analytic temperedness of
induction with no additional premise. Input unitarizability and algebraic
complete reducibility are separate conclusions of the parent statement.
No parent aggregate theorem, tempered exhaustion, square-integrable block
induction or regular Langlands classification proof is used here.
