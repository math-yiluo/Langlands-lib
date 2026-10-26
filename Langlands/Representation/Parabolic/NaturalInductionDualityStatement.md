# Natural same-parabolic normalized induction duality

Author: Worker 166.

`Langlands.Parabolic.NaturalNormalizedInductionDualityStatement` is a
proposition definition, consisting of the standard and refined natural
induction-duality clauses below. It is a specification awaiting proof.

## Groups, carriers and actions

Both clauses quantify over every prime `p`, every actual finite extension
`F : PadicField p`, every compatible topology `T`, every natural rank `n`,
and every ordered block shape `B`. The field universe `uF` and inducing
representation universe `uV` are independent. Rank zero is included.
There is no topology on the complex representation carrier.

In `StandardNaturalInductionDualityClause`, the ambient group is
`GL_n(F)` and the inducing Levi is the actual product `B.Levi F.Carrier`.
The induction is `T.normalizedParabolicInduced B`. In
`RefinedNaturalInductionDualityClause`, a block refinement `S` specifies
an upper parabolic inside the product Levi `B.Levi F.Carrier`. The
inducing group is the actual subgroup `refinedLevi F.Carrier B S`;
induction is `T.normalizedRefinedInduced B S`. Inputs are arbitrary
representations of this group, without a tensor decomposition or a
condition on restrictions to the individual factors.

For every input `sigma`, the sole representation hypothesis is
`IsAdmissible sigma.ρ`. This includes smoothness and finite-dimensional
fixed spaces for open subgroups; it does not require finite length or
finite dimension of the entire carrier. All group topologies come from
`T.topology`, using the actual general linear and product topologies
and the induced subgroup topology for the refined Levi.

Write `I(sigma)` for the indicated induced representation and `D` for
`smoothContragredient`. The carrier of `D(sigma)` is `SmoothDual sigma.ρ`,
the smooth-vector subspace of the algebraic complex-linear dual, with
action `(g • ell)(v) = ell(g⁻¹ • v)`. It is not the conjugate-linear
Hermitian dual. Induction has its existing smooth covariant function
carrier in universe `max uF uV`.

Both inductions use right translation and covariance
`f(qg) = delta(q)^(1/2) sigma(m(q)) f(g)` for the same upper parabolic.
For standard GL, `delta` is the actual block modulus and the scalar
character is `T.parabolicHalfModulus B`. For the refined clause it is
the product modulus with character `T.refinedParabolicHalfModulus B S`.
The dual is induced with that same positive half-modulus. There is no
change to the opposite parabolic or an inverse-half induction convention.

## Coherent families and the naturality equation

For each fixed group and parabolic, the clause requires one family of
complex-linear representation equivalences

`E_sigma : D(I(sigma)) ≃ I(D(sigma))`.

The family is quantified before the naturality law. For every actual
intertwiner `a : sigma -> tau` between admissible inputs and every
smooth functional `ell` on `I(tau)`, that law is

`E_sigma(D(I(a))(ell)) = I(D(a))(E_tau(ell))`.

Here `D(a)` is exactly `contragredientMap a`, defined by pullback of
smooth functionals. The maps `I(a)` and `I(D(a))` are exactly
`normalizedParabolicInducedMap` or `normalizedRefinedInducedMap`,
which postcompose induced functions by the underlying intertwiner.
Both sides are vectors of `I(D(sigma))`. The equation expresses
contravariant naturality. It is imposed for all objects and maps
within each fixed carrier universe `uV`.

The existing `NormalizedInductionDualityClause` in
`Parabolic.NormalizedInductionStatement` asks only for a pointwise
nonempty equivalence for each admissible standard input. The new
standard clause supplies such equivalences and a coherent choice
natural in the actual intertwiners. An arbitrary choice from the old
pointwise assertion would not establish this coherence. The refined
clause also supplies the corresponding product-Levi assertion.

## Source and derivation

The registered original is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III, revision April 29, 2019,
source `casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
The retained original is
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.

Page 1 fixes connected reductive scope, normalized right-translation
induction with positive half-modulus covariance, and a good compact
subgroup `K` for which `G = P K`. Proposition III.1.1 on page 2 identifies
the smooth contragredient of normalized induction with normalized
induction of the contragredient from the same parabolic. Its displayed
pairing integrates `phi(k)(f(k))` over `K`, for
`phi` in `I(D(sigma))` and `f` in `I(sigma)`.

The coherent naturality requirement is an internal formulation derived
from that pairing, rather than a separate verbatim source theorem.
Choose the compact subgroup and one Haar normalization for the fixed
group and parabolic, uniformly in `sigma`. The pairing defines the
inverse-direction map `J_sigma : I(D(sigma)) -> D(I(sigma))`.
For `a : sigma -> tau`, its pointwise evaluation gives

`J_sigma(I(D(a))(phi))(f) = J_tau(phi)(I(a)(f))`.

Thus `J_sigma ∘ I(D(a)) = D(I(a)) ∘ J_tau`. Taking inverses of the
duality equivalences gives the stated equation for `E_sigma`.
This argument explains why the noncanonical choice of invariant
integral mentioned on page 2 is compatible with the existential
family: the choice is made uniformly for all representation inputs.

Finite products of general linear groups are connected reductive
groups, and the refined parabolic is the product of the chosen upper
parabolics inside those factors. The source therefore applies directly
to arbitrary representations of its Levi. No factorwise admissibility
or tensor-product reduction is used. In rank zero all groups are
trivial, the empty modulus is one, and evaluation at the identity
identifies induction with its input; the same statement includes this
degenerate case.

This file proves no induction-duality, second-adjointness, Jacquet
multiplicity, or irreducible-head theorem. It provides one of the
natural duality interfaces needed for a later proof of actual
second adjointness.
