# Parabolic double-coset covering in a descended rank-one group

This internal unit proves the two-cell covering for the direct relative-rank-one
route. It then derives opposite factor pairs, and the exact rank-one factorization
target, from full-kernel component reductivity alone. Everything holds over every
field `k : Type u`, with all scheme tests.

## The covering theorem

`RelativeRoot.exists_parabolic_mul_normalizer_mul_parabolic` works in the
following setting:

- `G` is a connected reductive group over `k` (`IsConnectedReductive G`).
- `i : T.toGrp → G` is an actual maximal split torus.
- `a` is a nonzero character of `T`.
- `e` is an actual automorphic action of `Gm` on `G` whose restriction along `a`
  is conjugation by `i`.
- `ν` is a cocharacter with `0 < latticePairing T a ν`. Put `χ = ν ≫ i` and
  `P = Dynamic.parabolic χ`.

Then every rational point `g` of `G` can be written `g = p * n * r`, where `p`
and `r` lie in `P(k)` and `n` lies in `normalizerPoints i`. This is exactly the
covering premise taken by the published
`unipotentNormalizerCovering_of_parabolicNormalizerCovering`.

### Implemented proof

1. *The proper flag quotient.* `Dynamic.Affine.parabolicHom χ` is the canonical
   closed affine representative of `P`.
   `isParabolicSubgroup_of_range_eq_dynamicParabolic` shows that it is a
   parabolic subgroup of the connected reductive group `G`.
   `smoothSubgroupQuotientExistence` gives a quotient `q : G.X → Q`, with `Q`
   separated, locally of finite type and quasi-compact over `k`, and `q`
   smooth, surjective and quasi-compact. Its all-test fibers are exactly the
   `P`-cosets. `parabolicSubgroupQuotientProper` shows that `Q` is proper.
2. *Rational lifting.* Every rational point of `Q` lifts to a rational point of
   `G`. For a finite field this comes from
   `Dynamic.rational_lifts_of_finite_torsor` together with the published
   unconditional `finiteFieldTorsorPointStatement`. That step needs `P` to be
   connected, which `DynamicConnected.connectedSpace_of_isRepresentedBy_parabolic`
   supplies. For an infinite field, the opposite-cell open immersion
   (`oppositeCellStatement`) gives the identity section `Dynamic.flagQuotientCell`.
   `Dynamic.rational_lifts_of_reductive_density` then applies with the published
   unconditional `reductiveRationalPointDensity`.
3. *The orbit limit.* Left translation `Dynamic.flagQuotientSchemeAction` acts on
   `Q` and satisfies `act x (q y) = q (x * y)`. Restrict it along `χ`. Because `Q`
   is proper, `AffineLine.exists_extension_of_isProper` extends the `Gm`-orbit of
   `q(g)` to the affine line. Its value at zero is fixed by `χ` on every test
   (`IsGmOrbitExtension.isFixed_evalZero`).
4. *A normalizer representative.* Lift the limit to a rational point `g₁` with
   `q(g₁) = evalZero ext`. Fixedness of the limit is the fixed-coset hypothesis
   of `normalizerRepresentativeOfFixedCoset` (module `RankOneFixedCosets`). That
   construction returns an actual point `n` of `normalizerPoints i` with
   `q(n) = q(g₁)`, so the orbit of `q(g)` has limit `q(n)`.
5. *The double coset.* `Dynamic.BruhatCellLimit.exists_eq_mul_mul_of_mem_normalizerPoints`
   turns this limit into points `b₁, b₂` of the parabolic scheme with
   `g = b₁ * n * b₂`. Their images in `G` lie in `P(k)`.

### Provenance

The covering is an internal derivation. It combines the published proper
homogeneous quotient, the rational-lifting adapters, the proper extension of
orbits and the Bruhat-cell limit theorem with this route's fixed-coset normalizer
construction. It uses neither a general rational Bruhat decomposition, nor a
Tits system, nor a classification of standard parabolics.

## Opposite factor pairs from component reductivity

`RelativeRoot.exists_oppositeFactorPair_of_componentReductivity` takes the
proposition `KernelCentralizerComponentReductiveStatement.{u}` as an explicit
hypothesis. Under that hypothesis it proves: for connected reductive `G`, an
actual maximal split torus `i`, a nonzero character `a`, and a rational point `x`
in `(subgroup i a)(k)`, there is a pair `p` with `IsOppositeFactorPair i a x p`.
`RelativeRoot.oppositeFactorPairOfComponentReductivity` is the corresponding
classical choice of such a pair, as a subtype.

The proof follows the published
`exists_oppositeFactorPair_of_bruhat_and_componentReductivity`, except that the
covering theorem above replaces its rational-Bruhat hypothesis. The steps are:

1. The case `x = 1` is handled by the pair `(1, 1)`.
2. Otherwise `kernelCentralizerStructure` supplies a smooth closed
   representative `j : C → G` of the full kernel centralizer of `a`. The
   hypothesis makes `identityComponent C` connected reductive.
3. Choose `ν` with `0 < latticePairing T (-a) ν` by
   `exists_genericCocharacter_pairing_pos`. `characterFpqc` makes the character
   `-a` fpqc, so `kernelCentralizerIdentityQuotientAction` for `-a` is an actual
   `Gm`-action on the component whose restriction along `-a` is torus
   conjugation.
4. Apply the covering theorem in the component, with the torus
   `kernelCentralizerIdentityTorus` for `-a`; this torus is maximal split there.
   `kernelCentralizerIdentityTorus_neg` identifies it with the torus `iC` for `a`.
5. The dynamic unipotent of `ν ≫ iC` is `subgroup iC (-a)`, and its dynamic
   centralizer is the torus centralizer.
   `unipotentNormalizerCovering_of_parabolicNormalizerCovering` converts the
   covering into `y = u * n * v` with `u, v` in `subgroup iC (-a)` and `n`
   normalizing `iC`. The pair `(u⁻¹, v⁻¹)` is then an opposite factor pair for
   `y`.
6. `forall_exists_oppositeFactorPair_kernelCentralizerIdentity_iff` transports
   pair existence from the component back to `G`.

## The exact target from component reductivity

`rootRankOneFactorization_of_componentReductivity` proves that
`KernelCentralizerComponentReductiveStatement.{u}` implies
`RootRankOneFactorizationStatement.{u}`. It uses the same affineness and
torus-monomorphism instances as that statement, and the smoothness of `G`. It
then applies `hasRankOneFactorization_of_hasOppositeFactorPairs` to the pair
existence above. A relative root is nonzero, which supplies the needed
`a ≠ 0`.

## Scope

Full-kernel component reductivity stays an explicit hypothesis in the
assembly and the implication. This module does not prove it, so it is not an
unconditional proof of `RootRankOneFactorizationStatement`. The unconditional
result is the covering theorem.
