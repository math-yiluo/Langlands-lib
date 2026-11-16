# Invertibility of actual root commutator maps

This internal module works over an arbitrary commutative ring `R` in universe
`u`, with an affine group scheme `G`, a finite coordinate type `I`, a torus
homomorphism `i`, and cocharacters `mu` and `nu`. It uses the actual dynamic
group `Uc i mu nu` and the actual endomorphism `rootCommutatorMap`.

`rootCommutatorMap_fibre_scalar` takes a field `R`-algebra `K`, an isomorphism
`Phi : Ga K ≅ UK i mu nu K`, and a proof that its ambient composite
`fibreRootMap` is a root parametrization of exponent `a`. On every scheme test
`Z` over `K`, the pullback of the root commutator map, in the `Phi` coordinates,
sends `c` to `(a(t) - 1) * c`. Here `a(t)` is evaluated on the same test scheme
viewed over `R`, at the constant point determined by the supplied base section
`t` of the split torus.

The proof cancels the monomorphism given by the root inclusion. It transports
the fixed torus point through the canonical split-torus base-change isomorphism
and compares its character value by naturality. Root equivariance identifies
conjugation with multiplication by `a(t)`. The ambient commutator formula then
subtracts `c`, using the additive and inverse laws for root points.

`isIso_rootCommutatorMap_field` assumes that `a(t) - 1` is a unit in the global
functions on `Spec R`. Pullback of global functions preserves this unit on
every test. The scalar calculation and the Yoneda scalar criterion therefore
show that the pulled-back commutator map is an isomorphism on the supplied
field fibre.

`isIso_rootCommutatorMap` assumes that `G` is reductive, `i` is fibrewise
maximal, and `P` is the supplied full fibrewise root datum. For a root `alpha`,
`mu` must pair to zero with `P.root alpha`, and every root pairing to zero with
`mu` must equal that root or its negative. It also assumes that the value of
`P.root alpha` at `t`, minus one, is a unit on `Spec R`. Its conclusion is that
the actual map on `Uc i mu (P.coroot alpha)` is an isomorphism over `R`.

The field-fibre comparison supplies a root parametrization on each residue
field fibre. The preceding field criterion proves that each pulled-back map
is an isomorphism. Smoothness of the actual dynamic group gives flatness and
local finite presentation, and the published residue-field criterion then
proves the original map is an isomorphism. `rootCommutatorIso` packages this
map as an isomorphism with the same hypotheses.

The provenance is internal: the construction combines the dynamic torus
action, the field-fibre root comparison, naturality of character values,
additive root-point laws, Yoneda and the residue-field isomorphism criterion.
There is no local-ring, reducedness, noetherian or characteristic hypothesis,
and no global additive coordinate over `R` is assumed. This module does not
yet construct an fppf cover or prove relative semisimple fppf-perfectness.
