# Closed actual common-Levi V.3.1 target

The primary declaration is
`Langlands.Plancherel.ActualCommonLeviV3.ClosedV31Statement`.
It is an unproved Prop-valued target for the common-Levi case `s = 1`
of Waldspurger, *La formule de Plancherel pour les groupes p-adiques*
(2003), V.3 formula (1) and Proposition V.3.1, printed p.295 / PDF p.61.
The source is registered as `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The whole-operator polynomial and rational conventions come from IV.1,
printed pp.276-277 / PDF pp.42-43. The actual coefficient fiber and
inverse-formal-degree form follow V.1, printed p.288 / PDF p.54.

## Structural and inducing inputs

The field is any nonarchimedean local field. The ambient group scheme is
affine, locally of finite type and connected reductive. The field universe
`u` and inducing-carrier universe `uV` are independent. Three cocharacters
specify the literal Levi `levi chi` and the two parabolics, with equal
centralizer subgroup functors. A compact open `K` and both actual
factorizations `G(F) = P(F) K` are displayed. No splitness, quasisplitness,
characteristic-zero, positive-rank or induced-irreducibility condition is
introduced.

The inducing object is a canonical `SmoothRep` on the literal Levi, with
irreducibility and square integrability modulo the given central subgroup.
The latter already includes admissibility. The target's
`IsActualSplitCenter` premise identifies that subgroup with the actual
point image of a split component of `parameterScheme chi`, transported
by `parameterHomeomorph chi`. This is an internal characterization using
the existing `IsSplitComponent`; it does not introduce another notion of
split component. The central quotient carries the supplied Borel structure
and one inversion-invariant Haar measure, fixed across all unitary twists.

`unitaryParameter` is the subgroup inclusion into the full actual rational
character parameter group. `unitary_parameter_norm` shows that
`parameterTransport chi` preserves its unitary values.
`unitaryTwist_squareIntegrable` applies the published central-quotient
unitary-twist theorem with the same Haar measure.
`unitaryTwist_irreducible` applies the published twist irreducibility
equivalence only to the inducing representation.

The elementary structural lemmas are implemented proofs.
`ambient_modularCharacter` invokes the proved rational-point reductive
unimodularity theorem. `common_modularCharacter` uses the actual common-Levi
semidirect decomposition, its proved continuous projection, published
literal-Levi unimodularity, and radical unimodularity, then rewrites the
closed Haar restriction character. `iwasawa_sets` unpacks the supplied
factorization into the existing coefficient API's set formulation.
These facts are not analytic assumptions of the closed target.

## Actual family and local regularity

`UnitaryComparisonFamily` consists of intertwiners between the existing
actual positive-Levi coefficient objects at each unitary twist. Thus its
maps retain the full actual `G(F) x G(F)` action. `compactValue` conjugates
such a map by `ActualCommonLeviCompactTensor.compactTensorEquiv`, giving a
map between the fixed actual compact-induction tensor carriers of the
inducing object and its smooth contragredient.

Every germ predicate is tied to specified actual `ContinuedPair` objects
`p` and `q`. Their `genericLocus` requires regularity and bijectivity of
the particular actual forward and inverse-parameter reverse-dual standard
continuations. `compactComparison` tensors the forward continuation with
the transported inverse of that particular reverse operator. Its prior
compact comparison square identifies it with the actual generic
coefficient-fiber map. The present unit does not introduce an alternative
operator or choose an arbitrary coefficient equivalence.

`IsLocalRepresentative` specifies an ambient open set, a global operator
numerator polynomial on the full actual parameter group, and one regular
scalar denominator nonzero throughout the open set. On its intersection
with the genuine generic locus, the numerator is that denominator times
the actual compact comparison. The denominator is chosen before the
polynomiality predicate quantifies over an input vector. Each fixed input
may have its own finite polynomial expansion, as in IV.1; no finite
dimensionality of the whole carrier is assumed.

`RegularGermAt` evaluates such a representative at its center.
`IsRegularUnitaryExtension` requires one such representative around every
unitary point and uses it to evaluate the entire unitary family throughout
that neighborhood. It never requires the individual standard factors to
be regular there. Poles may cancel in the whole tensor.
`AgreesOnUnitaryGeneric` separately requires equality with the actual
generic comparison at every unitary parameter in its genuine domain.
`IsUniqueByRationalGerm` says every local regular representative of this
same actual rational germ evaluates to the specified compact value,
including representatives with different denominators.

`HasDenseGenericLocus` requires the genuine generic set to be nonempty and
dense in the full parameter space, with dense preimage in the entire
unitary subgroup. It also requires a nonempty ambient open dense subset
of that set whose unitary preimage is dense. These are conclusions of the
closed target, not assumptions or restrictions of its unitary domain.

## Exact coefficient and form identities

`coefficientMap` is precisely `CompactInduction.leviCoefficientMap` at the
unitary twist, with the given `K` Haar probability, actual common-Levi
projection and proved modular identities. Its admissibility input comes
from the inducing twist's square integrability. No coefficient-range
identification or alternate quotient-duality scale replaces this map.

`formalDegreeForm` is precisely
`CompactInduction.leviFormalDegreeProductForm`, with
`compactOpenCofinal_of_nonarchimedean (levi chi)`, the same central quotient
Haar measure, and the twist's square-integrability and irreducibility
proofs. It retains the source inverse formal degree; it is not an arbitrary
invariant form. The construction uses the existing form's inducing
formal degree and compact probability normalization.

`PreservesCoefficientsAndForms` requires, at every unitary parameter,
bijectivity of the extended map, equality of the target coefficient of
its image with the source coefficient for every vector, and equality of
the exact inverse-formal-degree Hermitian inner products for every pair
of vectors.

## Closed target and remaining work

`ClosedV31Statement` concludes the existence of both actual continuations,
actual `ScalarInverseData`, the nonempty/dense generic properties, whole
compact-operator rationality on that genuine locus, and an extended
unitary comparison family satisfying all the local regularity, agreement,
rational-germ uniqueness, bijectivity, coefficient and form clauses above.
In particular, none of continuation existence, scalar composition,
generic bijectivity, density or regular extension is a permanent analytic
premise. The supplied square-integrability and irreducibility belong to
the inducing discrete-series object; irreducibility of tempered induction
is never assumed.

The predicates and structural assembly are internal specializations of
the existing actual common-Levi tensor, full rational-character operator
algebra, compact probability coefficients and source formal-degree form.
The substantive assertion is the cited V.3.1 common-Levi specialization.
This unit publishes a target, not a proof of that assertion. Existing
analytic, composition and scalar proof owners are unchanged. Rational
conjugating points, choice comparison, cocycle and Weyl descent, and the
intrinsic semistandard coherent-section adapter are subsequent focused
units of the host task; this pair does not claim to complete those units.
