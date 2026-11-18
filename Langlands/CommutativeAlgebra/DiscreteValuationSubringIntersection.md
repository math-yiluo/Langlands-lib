# Finite intersections of discrete valuation subrings

`Langlands.CommutativeAlgebra.DiscreteValuationSubringIntersection` constructs
`intersection V : Subring K` as the infimum of the underlying subrings of
`V : ι → ValuationSubring K`. The field `K : Type u` and the index type
`ι : Type v` have independent universes.

- `inclusion V i` is the canonical ring homomorphism to `V i`.
  `subtype_comp_inclusion` identifies its composite into `K` with the subring
  embedding. `contraction V i` is the inverse image of the maximal ideal of
  `V i` along this homomorphism.
- For finite `ι`, `localization` supplies `IsLocalization.AtPrime` for `V i`
  over the intersection, with `inclusion V i` as its algebra map.
  `atPrimeAlgEquiv` identifies `Localization.AtPrime (contraction V i)` with
  `V i` as algebras over the intersection.
- For an injective finite family of DVRs, `contraction_isMaximal` and
  `contraction_injective` give the maximality and distinctness of the
  contractions. When `ι` is nonempty, `isMaximal_iff` identifies all the
  maximal ideals. `prime_eq_bot_or_eq_contraction` gives the classification
  of all prime ideals for a finite nonempty DVR family. Each contraction is
  nonzero by `contraction_ne_bot`.
- `center V i` is the image of the closed point of `Spec (V i)` along the
  map induced by `inclusion V i`. The generic point of `Spec (V i)` maps to
  the generic point of the intersection by `comap_inclusion_bot`.
  `eq_bot_or_eq_center` gives the prime classification on `PrimeSpectrum`
  itself.

## Proof

The construction uses `ValuationSubringIntersection` for the localization
and the exhaustion of maximal ideals. Its geometric-sum denominator lemma
expresses any `x ∈ V j` as `x = (x * s) / s`, where `x * s` and `s` belong
to the intersection and `s` is a unit in `V j`. If the contraction at `i`
is contained in the contraction at `j`, `s` is also a unit in `V i`. Then
`x ∈ V i`, so `V j ≤ V i`.

A DVR has Krull dimension one and is proper in its ambient field. Mathlib's
comparison with overrings of a dimension-at-most-one valuation subring
therefore forces equality of the two DVR subrings in this situation.
Injectivity of `V` gives equality of their indices. In particular, if a
contraction is contained in any maximal ideal, the core theorem expresses
that maximal ideal as another contraction, so they coincide.

For any prime `q` of the intersection, choose a maximal ideal containing
it, which is some `contraction V i`. Extend `q` to `V i`. It extends to a
prime since `q` is disjoint from the complement of `contraction V i`.
The only primes of the DVR are its zero and maximal ideals. The former
contracts to zero by injectivity of the inclusion, and the latter contracts
to `contraction V i` by definition. Moreover, the extension of
`contraction V i` is the nonzero maximal ideal of `V i`, so the
contraction is nonzero.

## Provenance

This is the DVR specialization of the published `ValuationSubringIntersection`
core. It formalizes the semilocal intersection of codimension-one local
rings used in Bosch, Lütkebohmert and Raynaud, *Néron Models* (Springer, 1990),
§6.4 Lemma 4, printed p. 155 and PDF p. 162
(`bosch-lutkebohmert-raynaud-1990-neron-models`). The source obtains the
semilocal ring and its local components by valuation approximation. The
Lean construction uses the core's geometric-sum argument and derives the
zero-or-maximal prime classification from the localization correspondence.
