# Actual automorphic realizations of finite-order Hecke characters

This internal construction takes a finite-order continuous Hecke character
`χ` on the actual idele-class group of an arbitrary-universe number field.
For every natural matrix rank `n`, it constructs the actual line of
automorphic functions `g ↦ χ(det g) * c`, proves its operator properties,
and in rank one constructs an irreducible cuspidal representative and class.
The coefficient field is complex throughout.

## Actual embedded forms

`FiniteOrderHeckeRealization.realization F n χ hχ` is the published actual
determinant twist of the embedded constant realization. Thus it is a
subrepresentation of the whole concrete automorphic operator algebra on
the existing stable form carrier. Its definition uses an actual image of
the previously constructed multiplication map. It supplies no replacement
function carrier or assumed automorphic occurrence.

`scalarEquiv` composes the scalar equivalence of actual constants with
the actual determinant-multiplication equivalence onto that image.
`evaluate_scalarEquiv` gives the function value at every full adelic
matrix. Evaluation at the identity is its inverse, since the determinant
character there is one. `realization_finrank` therefore proves the actual
carrier has complex dimension one.

`form` composes this equivalence with the original form inclusion.
Its pointwise formula is the same, and its injectivity follows from the
two injective maps. In particular `form_one_ne_zero` constructs a
nonzero actual automorphic form for every input character and rank.
All automorphic conditions are inherited from the published
finite-order determinant multiplier, whose preservation theorem already
proves finite level, real smoothness, compact and common center finiteness,
and polynomial growth.

## Actual operators and characters

`finiteRepresentation_scalarEquiv` and
`compactRepresentation_scalarEquiv` identify the original finite and
standard infinite compact actions with scalar multiplication by the
respective restrictions of `χ ∘ det`. They follow from determinant-twist
covariance and the trivial translation action on constants.

`envelopingAction_scalarEquiv` proves that the entire genuine enveloping
algebra acts through its augmentation. The published finite-order
multiplier commutes with the genuine differentials, so the constant-line
augmentation formula transports directly. No derivative action is
stipulated on a new scalar carrier.

`realization_isIrreducible` transports whole-operator irreducibility of
the constants through the published invariant-subspace correspondence.
`realization_hasCentralCharacter` proves the central character is `χ^n`:
the determinant of a rank-`n` scalar matrix has the required exponent.
This includes rank zero.

`realization_hasInfinitesimalCharacter` applies the enveloping formula
to the center and uses surjectivity of the scalar equivalence.
`realization_isRegularAlgebraic` uses the published augmentation
character of highest weight zero. This is the existing infinitesimal
regular-algebraic predicate; no algebraic formula for every component
of `χ` is inferred from it.

## Rank-one cuspidal objects

Under the existing explicit hypothesis
`[CompactSpace (AdeleQuotient F)]`, `cuspidal F χ hχ` is the actual
determinant twist of `ConstantFunctions.rankOneCuspidal F`. Its underlying
realization is definitionally the constructed character line in rank one.
Its irreducibility and cuspidality are supplied by the actual twist
construction, and `cuspidal_hasCentralCharacter` simplifies `χ^1` to `χ`.
The compactness instance is an input, as in the existing cusp API; this
module does not construct it.

`cuspidalClass` retains this constructed representative in the existing
full-operator quotient. Its forgetful image is the whole-operator class
of the same embedded line, and `cuspidalClass_isRegularAlgebraic` proves
the corresponding class predicate using the existing representative
criterion.

## Provenance and scope

These are internal consequences of the actual constant construction and
the published finite-order determinant multiplier, its operator twist,
and its central-character transport. Their intrinsic construction
obligations are proved by composition, the existing twist equations and
the scalar equivalence. No new original-literature claim is used.

Finite order is an explicit hypothesis on the actual input character;
the construction neither chooses a character with prescribed components
nor asserts existence for general infinite-order characters. It proves
no classification of rank-one cusp forms, restricted tensor
factorization, unitarity, spectral decomposition, higher-rank
cuspidality, or local-global compatibility theorem.
