# Embeddings under induction from an actual represented Levi

Author: Worker 1758.

This internal construction supplies coefficient maps and finite-length
transport for the published `RepresentedParabolic.leviInductionFunctor`.
It is supporting infrastructure for the proof route in Renard VI.6.2,
rather than a proof of `LeviInductionFiniteLengthStatement`.

The field `k` has arbitrary universe `u`. Its topology is Hausdorff, and the
ambient group scheme has an affine structure morphism. Its rational points
have the published canonical point topology, with local compactness and the
nonarchimedean group property assumed. The data `p : P ⟶ G`, `l : M ⟶ P`
and `r : U ⟶ P` are an actual rational parabolic, rational Levi and matching
geometric unipotent radical, with the multiplication isomorphism. An explicit
`IsAffineHom M.X.hom` instance makes the canonical source topology available
before the particular Levi datum is introduced. This is redundant mathematically:
`hl.isConnectedReductive.isAffineHom` always supplies it. Proof irrelevance
makes the resulting `RationalPointFamily.pointTopology` definitionally equal
to `leviPointTopology l hl`, including in the exact target's instance setup.

`leviInductionMap` accepts a genuine equivariant complex-linear map from a
smooth representation `A` of `M(k)` to another such representation `B`.
Their carrier universes `v` and `w` are independent of each other and of
`u`. It constructs an intertwiner between their actual normalized induced
representations, with carrier universes `max u v` and `max u w`.

The implementation pulls the two coefficient actions back along the inverse
of `leviPointsEquiv p l hp hl`. It retains the same coefficient linear map;
its equivariance at a point of the literal Levi image is the original
equivariance identity at that point's inverse image in `M(k)`. It then uses
the published `normalizedInductionMap` for the actual point-image
semidirect decomposition and closed radical. Thus the new induced map
postcomposes each induced function with the original linear map, retaining
the published Haar-half-character normalization.

`leviInductionMap_hom` proves by definitional equality that at a common
carrier universe this construction is precisely the map of
`leviInductionFunctor`. `leviInductionMap_injective` applies the existing
pointwise injectivity result for `normalizedInductionMap`; the change of
coefficient action leaves the underlying map and its injectivity unchanged.

`leviInduction_hasFiniteLength_of_injective` converts this induced
intertwiner to its group-algebra-linear map through
`Representation.IntertwiningMap.equivLinearMapAsModule`. The existing
`IsFiniteLength.of_injective` then transports finite group-algebra length
from the target induced representation to the source. This is finite
composition length, with no finite-dimensionality assertion.

Finally, `leviInduction_preservesFiniteLength_of_irreducibles` assumes a
nonarchimedean local field and connected reductive ambient group. For each
fixed actual parabolic datum, it applies the published generic finite-length
induction theorem. The induction part of the published
`leviParabolicFunctorsExact` supplies preservation of every actual short
exact sequence, hence also those with finite-length terms. The only
remaining premise is finite length of induction for every irreducible
coefficient. It is an explicit conditional reduction, not a proof of that
premise.

The provenance is internal: all maps and proofs are specializations of
published coefficient-map, module-length and exact-functor results through
the defining Levi-point transport. No literature assertion is introduced.
The unrestricted represented cuspidal embedding, its all-proper-parabolic
cuspidality, represented transitivity and the supercuspidal finite-length
input remain separate obligations in the intended VI.6.2 assembly.
