# Actual unitary supercuspidal products from self-pair gamma rigidity

This is an internal composition of existing actual-action results. It removes
the supplied block shape, square-integrable blocks, real exponents and segment
parameters from the whole smooth-dual gamma rigidity theorem. It does not prove
the unitary classification, the generic epsilon comparison, the segment-head
factor formula or the host associated-pair induction statement.

`unitarySupercuspidalProduct_of_generic_smoothDualGamma` starts with a supplied
smooth representation, its genericity and unitarizability, an integral gamma
certificate for its pair with its actual whole smooth dual, and the restriction
that positive meromorphic order on the real axis can occur only at zero.
The unitary-generic exhaustion is an explicit premise. The proof lifts the
representation carrier to the maximum of the field and source universes and
transports genericity and its invariant positive form along the actual
representation equivalence. Exhaustion supplies a finite positive block shape,
unitary square-integrable blocks, strict real exponents, Hermitian parameter
symmetry and an isomorphism with the entire normalized upper induction.

The existing `IsUnitarySquareIntegrableBlockFamily.segmentParameters` chooses
actual centered segment parameters on these original blocks. No additional
segment-parameter existence premise is used. Composing the carrier-lift
equivalence with the exhaustion isomorphism gives an equivalence from the
original action to this induction. The existing
`unitarySupercuspidalProduct_of_smoothDualGamma` then applies. Its Whittaker
functional comes from the original genericity certificate. The segment-head
and equal-rank supercuspidal L-factor statements remain explicit premises.
The conclusion keeps the original action and yields the entire normalized
upper induction of actual unitarizable supercuspidal blocks, whose carrier
universe is independently prescribed.

`IsAutomorphicPairGammaFactor.isPadicSymmetricGammaFactor_selfPair` treats
automorphic objects. The class smooth-dual relation, its identification with
the canonical class contragredient, and equality of representative classes
produce an actual equivalence between the smooth dual of the supplied object
and the supplied second object. Genericity of the lifted first object gives
genericity of its actual smooth dual. Pullback of smooth functionals along the
carrier-lift equivalence transports this to the original smooth dual; the
representative equivalence then gives genericity of the second object.
`AutomorphicActualGamma` converts the supplied class gamma certificate on these
two generic objects to its integral certificate, retaining the exact generic
epsilon-comparison statement as a premise. Equivalence invariance then replaces
the second action with the actual whole smooth dual. The same rational
function, nontrivial character and supplied self-dual Haar measure are retained.

`unitarySupercuspidalProduct_of_classSelfPairGamma` composes these results.
`HasUnitarySupercuspidalProductOfClassSelfPairGamma` is the Prop-valued interface
for that local conclusion, and its theorem proves it under the four explicit
prerequisites: generic epsilon comparison, unitary-generic exhaustion,
segment-head L-factor formula and equal-rank supercuspidal L-factor formula.
The field, original-object and output-block universes are independent.

All topology is the canonical p-adic topology.

## Arithmetic self-pair specializations

`unitarySupercuspidalProduct_of_localSelfPairMatch` works at the completion
`padicField v` of a number field at a finite place, with field, object and
form-carrier universes equal to `u`. Its premise is an actual pair gamma match
between the classes of the supplied objects and the local relative Weil pair
`localPairClass S ι`, `localPairClass (dual S) ι`. Here `S` is unitary and `ι`
is a supplied continuous local-to-relative Weil homomorphism. The match supplies a
self-dual measure and a certified class gamma factor for it. The existing
`localSelfPair_rationalSpectralValue_real_positive_order_only_zero` supplies the
positive-order restriction. Thus no gamma factor, measure or order hypothesis
remains in this specialization. The four substantive prerequisites, the local
smooth-dual relation, genericity and unitarizability are still premises.

`localComponent_unitarySupercuspidalProduct_of_selfPairMatch` applies the
previous theorem to the actual p-adic object of the local component at `v` of a
cuspidal spectral presentation. It requires that component to be irreducible and
admissible. The cuspidal realization must have unitary central character. The
published `Automorphic.cuspidalUnitaryLocalGenericity` and
`Automorphic.cuspidalUnitaryLocalUnitarity` discharge genericity, for the given
character, and unitarizability. The conclusion is the body of the host
statement for this presentation and place. It gives a block shape and
unitarizable supercuspidal blocks in universe `u`. It also gives an actual
equivalence from the original local action to the entire normalized upper
product induction. The second object, its local smooth-dual relation and the
self-pair gamma match remain explicit premises.

## Scope

The local smooth-dual relation of the component pair and the self-pair gamma
match remain explicit. They require global inputs: the associated gamma
statement, the contragredient association statement, an actual cuspidal dual
with presentation, local irreducibility and admissibility of its component, and
an actual local relative Weil map with a local constant system. All four
substantive prerequisites must also be proved before this composition can
support the unchanged `AssociatedSupercuspidalInductionStatement` at its four
independent universes. This unit is a focused conditional prerequisite and
supplies no proof of that host statement.
