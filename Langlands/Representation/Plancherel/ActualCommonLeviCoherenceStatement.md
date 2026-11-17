# Closed common-Levi coherence of actual normalized comparisons

The primary declaration is
`Langlands.Plancherel.ActualCommonLeviCoherence.ClosedCommonLeviCoherenceStatement`.
It is an unproved closed Prop-valued target. Its composition clause is the
`s = t = 1` common-Levi specialization of Waldspurger, *La formule de
Plancherel pour les groupes p-adiques* (2003), Lemma V.3.2, printed p.295 /
PDF p.61. The actual normalized tensor is V.3 formula (1) on the same page;
its pairwise regularity, unitarity and coefficient properties are V.3.1.
The registered source is `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

## Structural data and actual fibers

The nonarchimedean local field and the representation carrier have independent
universes `u` and `uV`. The ambient group scheme is affine, locally of finite
type and connected reductive. There is no characteristic, splitness,
quasisplitness, rank or induced-irreducibility restriction.

`ParabolicPresentation chi K` bundles a cocharacter, equality of its actual
dynamic centralizer subgroup functor with that of `chi`, and the displayed
factorization of every rational point as a point of its actual parabolic
times a point of `K`. It is an internal bundle of the structural arguments
already used by the common-Levi tensor and V.3.1 target. It does not define
a semistandard index, a Weyl group or a discrete-series class. The target
ranges over all these displayed presentations for the given `K`; it does
not assert existence of such a presentation for an arbitrary compact open.

`fiber chi A K P z` is exactly `ActualCommonLeviTensor.coefficientFiber` for
`P.cocharacter`, at the image of the full unitary parameter `z` under
`ActualCommonLeviV3.unitaryParameter`. `ComparisonSystem` assigns an actual
`G(F) x G(F)` intertwiner to every ordered pair of these fibers, at every
unitary point. The inducing object is the literal common-Levi `SmoothRep`.
Its irreducibility and square integrability modulo the given central
subgroup, with the fixed actual central quotient Haar measure, are the
same structural inducing inputs as in `ClosedV31Statement`. The closed
coherence target retains that statement's `IsActualSplitCenter` premise.

## Identification with the standard operators

`IsActualNormalizedComparison P Q T` has existential witnesses for the two
actual `ContinuedPair` presentations and their actual `ScalarInverseData`.
It requires the nonempty ambient and unitary dense genuine generic locus,
including the nonempty open dense sublocus, and whole-operator rationality
of the particular `compactComparison`. It requires the full unitary
regular extension, agreement on every unitary generic point, uniqueness
by the actual rational germ, and exact coefficient and form identities
of `ActualCommonLeviV3`.

These imported predicates retain fixed actual compact coefficient carriers,
one denominator before the input vector, and ambient local representatives
of the whole tensor. They permit poles of the individual standard factors
to cancel. The coefficient map remains precisely the compact probability
`leviCoefficientMap`; the Hermitian form remains the actual
`leviFormalDegreeProductForm` with its source inverse formal degree and
unchanged central quotient Haar measure. This unit introduces no alternate
normalization or free coefficient-preserving equivalence.

`closedV31_iff_exists` is a proved elementary repackaging: under the actual
split-center identification, the previous closed V.3.1 target for a pair
is equivalent to existence of a `T` satisfying this predicate. Its proof
only reorders the existential witnesses and conjunctions. It does not
prove existence or any analytic property of those witnesses.

## Coherence and continued-presentation independence

`IdentityLaw` says `T P P z v = v` on each actual coefficient fiber.
`CompositionLaw` says
`T Q R z (T P Q z v) = T P R z v`
for every ordered triple, every unitary parameter and every source vector.
The middle fiber is literally the actual coefficient fiber of `Q`, so the
composition is typed without an arbitrary intermediate identification.
`InverseLaw` states both inverse identities, first on the fiber of `P`
and then on the fiber of `Q`.

`inverseLaw_of_identity_composition` is an implemented algebraic implication:
specialize composition to `(P,Q,P)` or `(Q,P,Q)`, then use the corresponding
identity. `bijective_of_inverseLaw` applies the reverse map to prove
injectivity and uses its value as a preimage to prove surjectivity. These
proofs do not establish the substantive identity or composition laws for
the standard operators.

`PresentationIndependenceStatement` says two families satisfying the full
actual normalized-comparison predicate for the same ordered pair are
equal. The existential presentations in the two predicates are independent:
their starting regions, denominators, scalar-inverse witnesses and
continuation data may differ. Both families must be regular extensions of
the particular standard-operator germ, rather than arbitrary invariant
maps. This is a separately named, unproved compatibility target.

`ClosedCommonLeviCoherenceStatement` concludes the existence of a system
with all the pairwise actual V.3.1 properties, the identity, composition
and inverse laws, and continued-presentation independence. None of
continuation existence, generic invertibility or density, regular
extension, or a coherent system is a permanent premise. Existence is
concluded simultaneously for the displayed common-Levi parabolics.

The presentation bundle, existential repackaging and elementary inverse
implications are internal derived infrastructure. The substantive
composition clause is the cited V.3.2 specialization; simultaneous
pairwise specifications and continued-presentation independence express
the compatibility of those actual rational extensions. No substantive
V.3 theorem is proved here. Rational conjugating points, the full `s,t`
composition law, canonical transport for different Weyl representatives,
and the intrinsic semistandard coherent-section adapter remain separate
units of the host task. Existing analytic and representation-theoretic
proof owners are unchanged.
