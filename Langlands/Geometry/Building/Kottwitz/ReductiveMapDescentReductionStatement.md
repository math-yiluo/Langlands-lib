# Inputs and formal reduction for reductive Kottwitz descent

This unit states a reduction of the published
`ReductiveKottwitzDescentStatement`; it does not prove that target or its
prerequisites. Its provenance is derived: it isolates the exact input statements
for the cocenter and z-extension argument in Kaletha–Prasad, *Bruhat–Tits theory:
a new approach* (2023), §11.5 and Lemma 11.5.1, printed pp. 429–430 / PDF
pp. 460–461, followed by the invariant-valued restriction defined on p. 430.
The authors' corrections of 1 November 2024, Chapter 11, pp. 43–46, do not change
these items.

`GeneralTorusKottwitzEquivarianceStatement` states residual Galois equivariance
of the selected torus Kottwitz map over each coefficient field `k` in precisely
the compatible towers required by the reductive descent target. Here
`K = UnramifiedClosure F` and `E = SeparableClosure F`; `E` is also required to
be a separable closure of `k`, and `K/k` is normal. The maps from `k` into these
two fields form a scalar tower. The group is any actual `k`-torus, and the
formula uses the actual coefficient action and residual inertia-quotient action.
There are no splitting, rank or residue-characteristic restrictions.

KP Proposition 11.1.1, printed p. 421 / PDF p. 452, gives the torus equivariance
argument in the book's Henselian discretely valued setting introduced on printed
p. 420. The new declaration is an explicit prerequisite at the already published
reductive target's coefficient-field generality. It does not assert that an
arbitrary `k` here is a local field, that `K` is its maximal unramified extension,
or that the existing `TorusKottwitzDescentStatement`, which quantifies only over
`F`-tori, proves this stronger prerequisite. In particular, verifying invariance
of the normalized valuations under the relevant coefficient automorphisms is
part of its proof obligation. No value-preservation hypothesis has been added
silently.

`ReductiveKottwitzRationalRestrictionStatement` says that, for every connected
reductive `F`-group, `ReductiveKottwitzEquivariant` implies unique existence of the
invariant-valued rational restriction and correctness of
`reductiveKottwitzRational`. It is a conditional statement and makes no K-point
existence or rational surjectivity assertion.

`ReductiveKottwitzDescentReductionStatement` states that the conjunction of the
following five independently explicit inputs, written as successive implications
in Lean, implies the exact published reductive descent target:

- `SimplyConnectedDerivedKottwitzStatement`;
- `ReductiveKottwitzExistenceStatement`;
- `FundamentalInertiaMapStatement`;
- `TorusInertiaComparisonStatement`;
- `GeneralTorusKottwitzEquivarianceStatement`.

The intended reduction first transfers equivariance from the cocenter torus
through its bijective target map, using residual equivariance of the two maps
composing that comparison. It then transfers equivariance along a z-extension
using surjectivity on K-points and equivariance of the induced inertia map.
Finally it applies the rational restriction step. These implications neither
supply proofs of the five inputs nor weaken the protected descent target.
The three declarations are Prop-valued definitions awaiting proofs.
