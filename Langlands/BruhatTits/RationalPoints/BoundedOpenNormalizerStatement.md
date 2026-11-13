# Bounded normalizers inside the rational norm kernel

`BoundedOpenNormalizerStatement.{u}` is the nonarchimedean local-field case of
Kaletha–Prasad Proposition 2.2.16. For every connected reductive group `G`
over a nonarchimedean local field `F`, and every algebraically bounded open
subgroup `H` of `G(F)`, it asserts that

`Subgroup.normalizer H ⊓ rationalCommonNormKernel G`

is algebraically bounded. The topology is the canonical rational-point
topology, and boundedness is the Library's `IsAlgebraicallyBounded F G.X`,
which tests every regular function on the actual affine group scheme.
The universe `u` is arbitrary.

The normalizer is the actual group-theoretic normalizer in `G(F)`. Its
intersection with `Langlands.Plancherel.rationalCommonNormKernel G` is
KP's normalizer in `G(F)^1`: every rational character has unit absolute
value there. This kernel uses all actual `F`-rational characters of `G`.
It is not the subgroup `G(F)^0` defined from Bruhat–Tits zero data.
No assumption that `H` is normal, pro-`p`, a facet subgroup or maximal
is present. No building or integral model is supplied or constructed.

This is an unproved statement. Its intended use in corrected KP 13.5.2 is
to bound the normalizer of a chamber positive subgroup after restricting
to `G(F)^0`, using the published inclusion of the zero subgroup into the
actual rational norm kernel. The host proof still needs the subsequent
facet and finite reductive-group arguments.

The original source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Proposition 2.2.16 and its proof, printed pp.77–78 /
PDF pp.108–109. The source states the result in its more general valued-field
setting. The present formulation restricts to nonarchimedean local fields.
Its `G(F)^1` is defined by unit values of every rational character, matching
the actual common rational norm kernel used here.

The source proof reduces through the central torus and derived quotient
to a semisimple group. An unbounded normalizer then supplies an adjoint
eigenvalue of negative valuation, and Lemma 2.2.15 forces the bounded open
subgroup to contain an unbounded root-generated subgroup. This describes
the literature's route, not a Lean proof supplied by this pair.
The November 2024 corrections PDF contains no entry numbered 2.2.16.
