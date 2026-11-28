# Invariant distributions supported on finitely many orbits

`FiniteOrbitDistributionSpanningStatement` concerns a continuous action of a
locally compact, sigma-compact nonarchimedean group `G` on a locally compact,
totally disconnected Hausdorff space `X`. The group and space universes are
independent. Let `Z` be closed and the union of the orbits of a finite set
of representatives `s`. For each `x` in `s`, supply an invariant distribution
`L x` supported on the closure of the orbit through `x`, with every point
of that orbit in its topological support. Then every invariant
distribution supported on `Z` belongs to the complex span of those `L x`.
Here `supportedOn C` means annihilating every test function vanishing on
`C`. The support condition on the orbit ensures the chosen distribution
has nonzero restriction when that orbit is relatively open.

## Proof

`finiteOrbitDistributionSpanning` uses
`FiniteOrbitVanishingProof.exists_relOpen_orbit_of_finite_image` to choose
a relatively open orbit `O` in the current nonempty closed invariant
support set `C ⊆ Z`. The ambient group action can have infinitely many
orbits. Only the image of `C` in the orbit quotient is required to be
finite.

Closed restriction of test functions is surjective, so both the
distribution under consideration and the chosen `L x` for `O` descend
to `C`. The closure of `O` lies in `C`, so `L x` satisfies the support
condition for this descent. The distributions on `C` restrict to `O`
by precomposing with extension by zero. The descent and extension
commute with the action by the pullback identities in
`FiniteOrbitVanishingProof`. The restriction of `L x` is nonzero
because otherwise it would annihilate all tests extended by zero from
an ambient open neighborhood cutting out `O` in `C`, contradicting
the topological support condition.

On the transitive orbit, take a compact open indicator on which the
restricted `L x` has nonzero value. Such indicators span the test
functions by the finite decomposition into nonzero fibers.
`homogeneousIndicatorProportionality` shows that an invariant
distribution vanishing on this one indicator vanishes on all compact
open indicators. The two restrictions are therefore proportional.
Subtract the corresponding multiple of `L x` from the ambient
distribution. Every test vanishing on `C \ O` restricts to `C` as an
extension by zero from `O`, so the difference is supported on `C \ O`.
This closed invariant set has strictly fewer orbits. Strong induction
gives the spanning assertion, with zero as the only distribution
supported on the empty set.

## Source

Harish-Chandra, *Admissible invariant distributions on reductive p-adic
groups*, notes by DeBacker and Sally, AMS University Lecture Series 16
(1999), §3.2, Lemma 3.3 and Lemmas 3.4–3.8, printed pp. 19–22
(PDF pp. 34–37), `harish-chandra-1999-admissible-invariant-distributions`.
Lemma 3.3 gives a basis of nilpotent orbital measures. The argument here
abstracts its spanning assertion to finite orbit unions with supplied
distributions. It uses relative open-orbit removal and homogeneous
indicator proportionality in place of the dimension filtration and the
local submersion used in Lemma 3.7.
