# Reduction of cyclic stable descent to prime descent and the twisted cusp obstruction

`Langlands.Automorphic.Unramified.CyclicStableDescentReductionStatement` and
`Langlands.Automorphic.Unramified.CyclicStableDescentTCReductionStatement`
conclude the exact published stable descent propositions. The proof route
uses the existence clause of Arthur–Clozel (1989), III.4.2(d), printed
pp. 202 and 206–207, the cyclic cuspidal fibre theorem III.3.1, p. 201, and
the self-pair count in III.6.3, p. 217. The correction to composite-degree
existence uses Clozel–Rajan, *Solvable base change*, Theorem 1, PDF p. 2.
Clozel–Rajan explain at the end of §2, PDF p. 7, that the prime-step
descendant in the original III.6.3 argument needs a stability proof.

## Existence with a unitary cuspidal witness

Retain an actual unitary lower cuspidal realization throughout the
degree induction. Degree one identifies the fields by the algebra
isomorphism inducing the inclusion. Take genuine attachments of the
upper cusp in the specified factor universes and transport a lower
one by arithmetic pullback. Independently obtained upper systems agree
outside their exceptional sets by `AssociatedPresentationSpectrum`,
so the residue-degree-one formula gives the weak lift. Prime degree
uses `CyclicPrimeStableCuspidalDescentStatement` with a unitary lower witness.

In composite degree choose the bottom prime step `K/F`. The generator
`σ` of `E/F` restricts to a generator `τ` of `K/F`, say of order `p`.
Induction for `E/K` yields an actual unitary cusp `S` of `K` lifting to
the supplied upper cusp `T`. Equivariance of weak base change, applied
to cuspidal singletons, shows that the conjugate of `S` also lifts to `T`.
The cyclic fibre theorem compares the two lower classes by a finite-order
determinant twist `χ` trivial on the norms from `E` to `K`. The two upper
attachments in this comparison are presentations of the same actual
class. Compare them using `IsoClass.hasSpectralSystem_iff` followed by
`CuspidalSpectralPresentation.spectralSystem_eigenvalues_eq`, and exclude
from the base the contractions of the extra exceptional upper places.
This yields the `SameResidueDegreePowers` hypothesis of III.3.1.

`CyclicPrimeNormCharacterRestrictionStatement` makes `χ` invariant under
`τ`. Naturality of the actual twist under arithmetic pullback then
iterates the conjugation relation `p` times, yielding a self-twist of `S`
by `χ^p`. In a unitary cuspidal weak lift from a unitary cusp, the cyclic
constituent-pair comparison applied to the two identical singleton pairs
gives a sum of self-twist indicators equal to one. The summand for the
identity character is one. Thus every other summand is zero and every
norm-trivial self-twist is trivial, by `cyclicNormKernelCharacter`. Applying
this over `E/K` gives `χ^p = 1`. If `χ` were nontrivial, the character
restriction statement would make its restriction faithful on the norm
quotient of `K/F`. The specialized Clozel–Rajan obstruction excludes the
actual twisted conjugation in that case. Hence `χ = 1`, which makes `S`
stable under `τ`. Obtain a unitary lower cusp by prime stable descent
for `K/F`, and use weak base-change transitivity to obtain the direct
weak lift to `T`.

## All cuspidal descents and distinct twists

For the chosen lower class and any other lower class lifting to `T`,
apply the same comparison of upper presentations and `CyclicCuspidalFiberStatement`.
That theorem takes genuine presentations of the two lower classes and
has no unitary hypothesis, as required for the target's quantifier over
all cuspidal classes. The published `cyclicNormKernelCharacter` gives
all norm-trivial characters as the powers of the supplied `η` with
exponents below `[E : F]`. These powers have finite order and the
published actual determinant twist constructs their classes.
`CuspidalWeakBaseChangeNormTwistStatement` gives the reverse implication
of the fibre equivalence. Finally, the self-pair count over `E/F` excludes
all nontrivial norm-trivial self-twists of the chosen unitary lower
realization. Composing two actual twist relations with a common target
shows that equality of twisted classes forces equality of the two
characters and then of their exponents in the given range.

## Field and factor universes

The intermediate field lies in the upper field universe `uE`. First use
strong induction for fields in `uE`, with factor universe `uW`, and then
handle mixed `uF` and `uE` by the degree-one, prime, and bottom-prime steps
using that same-universe result for `E/K`. The named premises are supplied
at the universe levels used in these two arguments. The compactness of
the intermediate additive adele quotient is the published
`compactSpace_adeleQuotient`. Both statements include the Harris
instantiation `.{0,0,uV,uV}` for arbitrary `uV`.

For the totally complex reduction, the relevant intermediate fields are
totally complex by upward propagation from the base. The prime trace
comparisons in the existence and obstruction inputs therefore use split
complex infinite places. The remaining arithmetic, Euler product and
presentation inputs are shared and do not require real-place transfer.
