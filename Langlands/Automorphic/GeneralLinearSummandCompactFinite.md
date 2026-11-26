# Archimedean compact-finite smoothing of regular vectors in the quotient `L²` of `GL_n`

Module `Langlands.Automorphic.GeneralLinearSummandCompactFinite`. For `GL_{r+1}` over a number
field `F` and the positive-central rational quotient `Q`, the module produces regular vectors
(`IsRegularVector`) that are `K∞`-finite for the standard archimedean compact subgroup
`K∞ = standardInfiniteCompact F (r+1)`. Here `K∞`-finite means `IsFiniteVector` for
`compactAction`: the orbit of the vector under `K∞` spans a finite-dimensional subspace. The
orbit itself need not be finite. The module also shows that smoothing by a kernel invariant
under conjugation by `K∞` preserves `K∞`-finiteness, and that the kernel can be chosen so that
the smoothing is nonzero.

## Definitions

- `archimedeanAdelicHom F r`: the archimedean inclusion `archimedeanAdelicPoint` of
  `InfiniteAdelicGL F (r+1)` into the adelic points, as a homomorphism.
- `compactParameter F r`: the restriction of this inclusion to `K∞`.
- `compactAction F r T i hi I e hc`: the representation of `K∞` on `L²(Q, μQ)` obtained by
  restricting `ρ = haarQuotientL2BoundedRightAction`.
- `rightIsometry`: `ρ g` as a linear isometry. Hence `integral_rightTranslate`:
  `ρ g` commutes with Bochner integrals.
- `compactAverage F r T i hi I e hc u`: for a Borel structure on `K∞`, the linear map
  `a ↦ ∫_{K∞} a(k) • ρ(k) u dk` from continuous weights, with the probability Haar measure
  `compactProbabilityHaar`. The weights used are those of the Library's `finiteWeights`:
  continuous functions on `K∞` whose left translates span a finite-dimensional space. The
  average is not a projection, and the weight need not be idempotent or belong to a single
  `K∞`-type.
- `smoothingLinear F r T i hi I e hc ν κ`: the map `u ↦ smoothedClass … 1 κ u` as a linear map.

## Results

- `ofFinite_mul_archimedeanAdelicPoint`: finite and archimedean adelic points commute.
- `compactAction_compactAverage`: translating an average by `k` gives the average against the
  left translate `leftRegular k a` of the weight. Hence `compactAverageIntertwiner` intertwines
  the left regular action on weights with `compactAction`. `isFiniteVector_compactAverage`: an
  average against a weight of `finiteWeights` is `K∞`-finite. The orbit span of the average
  lies in the image, under the intertwiner, of the finite-dimensional orbit span of the weight
  (`IsFiniteVector.map`).
- `isRegularVector_compactAverage`: let `u` be regular and invariant under a subgroup `L` of the
  finite adelic points. Then every nonzero average of `u` is regular and invariant under `L`.
  Its representative is the weighted orbit integral of the representative of `u`. The mass
  bound passes by `quotientMassBound_weightedQuotientOrbitIntegral`, and invariance under `L`
  by commutation.
- `exists_finiteWeight_compactAverage_ne_zero`: a nonzero `u` has a nonzero average against
  some weight of `finiteWeights`. A normalized bump `a₀` supported where
  `‖ρ(k) u - u‖ < ‖u‖ / 4` gives an average within `‖u‖ / 4` of `u`. A finite weight `a` with
  `‖a - a₀‖ ≤ 1/4` changes the average by at most `‖u‖ / 4`. Such weights are dense by
  `dense_finiteWeights`, applied to the faithful continuous representation
  `compactComplexRepresentation`.
- `exists_isRegularVector_compactFinite`: every regular vector invariant under `L` gives a
  regular vector invariant under `L` that is `K∞`-finite.
- `smoothedClass_compactAction`: let the kernel `κ` satisfy `κ(k⁻¹ x k) = κ(x)` for `k ∈ K∞`,
  and let `ν` be invariant under right translation by `K∞`. Then smoothing commutes with
  `compactAction`. The substitution `z ↦ k⁻¹ z k` preserves `ν`, by left invariance and the
  right invariance assumed. It turns `∫ κ(z⁻¹) ρ(k z) u` into `∫ κ(z⁻¹) ρ(z k) u`.
  Consequently `smoothingIntertwiner` is an intertwiner, and `isFiniteVector_smoothedClass`
  says smoothing preserves `K∞`-finiteness.
- `exists_smoothedClass_ne_zero`: a nonzero `u` has a nonzero smoothing by a kernel invariant
  under conjugation by `K∞`. The Library's `compactCentralConvolutionApproximation` supplies
  nonnegative real kernels, invariant under conjugation by `K∞`, with `∫ κ(z⁻¹) dν = 1` and
  support in any prescribed neighbourhood of the identity. Choose the neighbourhood where
  `‖ρ(z⁻¹) u - u‖ < ‖u‖ / 2` and apply `integral_smul_ne_zero`.

## Supporting lemmas

`secondCountableTopology_infiniteAdelicGL` transports second countability from the archimedean
group points through `GeneralLinearGroupPoints.infiniteHomeomorph`. `archimedeanAdelicPoint_mul`,
`archimedeanAdelicPoint_mul_left`, `archimedeanAdelicPoint_conj`, `compactParameter_one` and
`rightAction_mul_apply` are multiplicativity identities. `smoothingWeight_one_apply` evaluates the
weight of the identity element as `κ(z⁻¹)`, and `smoothingWeight_conj` is its invariance under
conjugation by `K∞`. `integrable_compactAverage` and `integrable_smoothing` give integrability of
continuous compactly supported weights against bounded continuous orbits.

## Provenance

The module supplies `K∞`-finiteness for the construction of nonzero forms in
`Langlands.Automorphic.GeneralLinearSummandFormsNonzero`. That construction proves the Library's
single-summand density statement. In Getz and Hahn, *An Introduction to Automorphic
Representations* (2024), the corresponding inputs are Lemma 9.7.2 and the comparison (9.40) in
the proof of Theorem 9.7.3, printed pp. 264–266 (PDF pp. 276–278). Lemma 9.7.2 obtains density of
`K`-finite vectors through the factorization of the representation into archimedean and finite
parts. It recovers each `K`-finite vector by a compact convolution. The book does not use the
construction of this module.

The averaging construction here is analogous to the proof of Proposition 4.4.7, printed
pp. 116–118 (PDF pp. 131–133). There a smooth bump is averaged over `K` against a nonnegative
matrix coefficient of a finite-dimensional representation of `K` (Peter–Weyl, Theorem 4.3.4).
That gives a `K`-finite convolution close to the identity. Here the weight is any continuous
weight with finite-dimensional left-translation span, supplied by the Library's
`dense_finiteWeights`. Nonvanishing comes from uniform approximation of a normalized bump. The
smoothing kernel is invariant under conjugation by `K∞`, so smoothing commutes with the action
of `K∞` and preserves `K∞`-finiteness.
