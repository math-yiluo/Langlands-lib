# Finite-level approximation in `L²([G])`

Author: Worker 112.

`Langlands.Global.RestrictionSplitCentre.QuotientL2FiniteApproximationStatement`
is a proposition about `L²` of the restriction split-centre quotient
`RestrictionSplitCentre.Quotient F G S j`. This quotient has the shape
`[G] = A_G G(F) \ G(A_F)` of Getz--Hahn (2.20)--(2.21)
(`getz-hahn-2024-automorphic-representations`, printed pp. 68--69). The space
is `Lp ℂ 2 (quotientHaarMeasure F G S j)` with the published canonical
quotient measure. The proposition is the `[G]` counterpart of the published
positive-torus
`Langlands.Automorphic.GroupSchemeFunctions.GroupSchemeQuotientL2FiniteApproximationStatement`.

## Hypotheses

The proposition quantifies over:

- a number field `F : Type`, and a group scheme `G` over `Spec F` whose
  underlying scheme is affine and locally of finite type;
- a commutative group scheme `S` over `ℚ` and
  `j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G`, which define the published
  quotient `Quotient F G S j`;
- a commutative group scheme `T` over `F` and `i : T.toGrp ⟶ G` with
  `h : subgroup F G S j = imageSubgroup F T G i`, injective
  `characterRestrict i` (`hi`) with finite-index range, `hc : IsCentral i`
  and `hT : IsSplitTorus T.toGrp`;
- right invariance of Haar measure on `normOneSubgroup F G` (an instance
  argument), and any proof `hInv'` of
  `QuotientRightInvariant F G (quotientHaarMeasure F G S j)`.

These are the hypotheses of the published
`rationalQuotientL2FiniteAverage F G h hi hc hT hInv' K` from
`GroupSchemeRestrictionQuotientL2FiniteAverage`, which the conclusion uses.
They are a sufficient setting; the proposition does not claim that they are
needed. Connected reductivity is not assumed.

## Conclusion

Write `ρf` for the published finite right action
`rationalQuotientL2FiniteRightAction F G (quotientHaarMeasure F G S j) hInv'`
of `FiniteAdelicGroupPoints F G` on `L²([G])`. The proposition asserts that
there are a sequence `K : ℕ → OpenSubgroup (FiniteAdelicGroupPoints F G)` and
a proof `hK` that every `K n` is compact as a subset of the finite adelic
points, such that:

- the sets `K n` form an antitone basis of the neighborhood filter of `1`
  (`Filter.HasAntitoneBasis`). They decrease, and every neighborhood of `1`
  contains all sufficiently late `K n`;
- let `A n` be the published average `rationalQuotientL2FiniteAverage` over
  `K n`, with `CompactSpace (K n)` obtained from `hK n` by Mathlib's
  `isCompact_iff_compactSpace`. Then `A n φ` lies in the published
  `Langlands.fixedVectors ρf (K n).toSubgroup` for every `n` and every `φ`;
- `A n φ` tends to `φ` in the `L²` norm as `n → ∞`, for every `φ`;
- the set of `φ` that are `Langlands.IsSmoothVector` for `ρf` is dense. A
  vector is smooth in this sense when some open subgroup of the finite adelic
  points fixes it.

The sequence `K` is chosen before `φ` is quantified, so one sequence works for
every vector. `A n` is the Bochner integral of the orbit against the published
normalized Haar probability measure on `K n`; no other approximation operator
is supplied.

## Provenance and scope

The quotient `[G]` is Getz--Hahn (2.20)--(2.21). The proposition is the `[G]`
form of the published internal positive-torus statement, with the same
conclusion for the published `[G]` finite action and average. No theorem of
Getz--Hahn is cited for it. The module states the proposition and contains no
proof. The intended proof repeats the published positive-torus proof: an
antitone subbasis of the published compact open basis of the finite adelic
points, continuity of the published `[G]` orbit, and the norm bound for the
probability Haar average.

The density concerns the finite adelic action only. For connected reductive
`G`, the density assertion also follows from the published
`QuotientL2SmoothDensityStatement`, which asks for vectors smooth for the
archimedean action and the finite action at once; the sequence of averages
does not. The proposition supplies
no archimedean smoothness, admissibility, finite volume, cuspidal analogue or
spectral decomposition.
