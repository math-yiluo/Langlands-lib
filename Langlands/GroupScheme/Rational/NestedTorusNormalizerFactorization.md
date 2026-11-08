# Centralizer correction for nested-torus normalizers

This internal construction factors each rational point normalizing a smaller
commutative subgroup into a point of its full centralizer and a point normalizing
both the smaller subgroup and a supplied ambient maximal split torus. Rational
conjugacy of maximal split tori in a closed representative of that full
centralizer is an explicit hypothesis.

## Data and exact conclusion

Work over an arbitrary field `k : Type u`. Let `S` and `T` be commutative group
schemes over `Spec k`, let `G` and `H` be group schemes, and supply
`i : T.toGrp ⟶ G` and `f : S ⟶ T`. Write
`a = CommGroupScheme.groupHom f ≫ i`. Assume:

- `hi : IsMaximalSplitTorus i`;
- `j : H ⟶ G` represents the actual subgroup functor `torusCentralizer a`;
- `hjc : IsClosedSubgroup j`;
- `hH : MaximalSplitToriAreConjugate H`, the existing proposition asserting
  rational conjugacy of every pair of maximal split tori in `H`.

The theorem `exists_centralizer_mul_commonNormalizer` asserts that for each
`nS : normalizerPoints a` there are
`z : centralizerPoints a` and `nT : normalizerPoints i` such that the ambient
point of `nT` also belongs to `normalizerPoints a` and

```text
(nS : G(k)) = (z : G(k)) * (nT : G(k)).
```

Here `G(k)` abbreviates the actual morphism type
`Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X`. The equality is in this original
point group. In particular, it is stronger than equality in a Weyl quotient.
Centralizer membership is the existing scheme-level identity for conjugation
along `a`, rather than just commutation with its field-valued image.

The primary definition `normalizerCentralizerFactorization` chooses such a
`z` and `nT`. Its dependent pair type retains both the common-normalizer
membership and the exact product equality. This choice is not claimed to be
canonical, unique, or multiplicative.

The hypotheses do not require a separate splitness or embedding assumption on
`f` or `S`, nor affineness, smoothness, connectedness, or reductivity of `G` or
`H`. Maximal splitness of the supplied upper map and the represented-centralizer
and conjugacy hypotheses remain essential premises.

## Implemented proof

Commutativity of `T` and the factorization through `f` imply, on every test
scheme, `range i ≤ torusCentralizer a`. The represented-subgroup factorization
API therefore lifts `i` to `iH : T.toGrp ⟶ H` with `iH ≫ j = i`.

The full centralizer is normalized by the actual normalizer of `a`. Apply this
fact on every test scheme to the restriction of the supplied `nS`. It shows that
the conjugated map `i ≫ int(nS)` also factors through `j`, giving `iH'`.
Closed-subgroup reflection of maximal splitness makes `iH` and `iH'` maximal
split tori in `H`; for `iH'` one first transports `hi` by the ambient inner
automorphism.

Apply `hH` to `iH'` and `iH`. It supplies a rational point `h` of `H` and a
torus automorphism `e` with
`iH' ≫ int(h) = e.hom ≫ iH`. Put `c = h ≫ j.hom.hom`. Representation of the
full centralizer gives `c ∈ centralizerPoints a`. Transport of inner
automorphisms along `j` and the multiplication law for inner automorphisms give

```text
i ≫ int(c * nS) = e.hom ≫ i.
```

Thus `nT = c * nS` normalizes the upper map. It also normalizes the lower map
because `c` centralizes that map and `nS` normalizes it. Taking `z = c⁻¹` proves
the displayed product equality by cancellation in the original ambient group.
The chosen definition uses classical choice on precisely this existence
theorem.

## Provenance and retained obligations

This pair is an internal derivation from the existing
`MaximalSplitTorusConjugacyReduction`, `MaximalSplitTorusCentralizer`, and
`TorusNormalizer` interfaces. It asserts no new original-literature theorem.
In particular, it does not establish representability, closedness, or rational
maximal-split-torus conjugacy of a centralizer for any new class of groups.

Its intended building use is to separate an arbitrary lower normalizer into a
full-centralizer factor and a common upper/lower normalizer. It does not assume
that the original lower normalizer itself preserves the upper torus. It
constructs no valuation, compatible valuation shift, apartment, building metric,
supplied-model special vertex, stabilizer identity, or unique fixed point.
The unchanged `IntegralModel.BuildingComparisonStatement` remains a separate
unproved goal.
