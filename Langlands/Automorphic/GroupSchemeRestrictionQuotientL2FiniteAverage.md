# Compact open averaging on L² of the restriction split-centre quotient

Author: Worker 112.

The published module `GroupSchemeRestrictionQuotientL2` defines the right
regular representation `rationalQuotientL2RightAction` on `L²` of the
restriction split-centre quotient `RestrictionSplitCentre.Quotient F G S j`.
This is the quotient `[G] = A_G G(F) \ G(A_F)` of Getz--Hahn (2.20)--(2.21)
(`getz-hahn-2024-automorphic-representations`, printed pp. 68--69). The
published module `GroupSchemeRestrictionQuotientL2Continuity` proves that this
action is jointly continuous and bounded. The published positive-torus module
`GroupSchemeQuotientL2FiniteAverage` averages the positive-torus quotient
action over a compact open subgroup of the finite adelic points.

The present module carries out that averaging on `[G]`, applying the published
constructor `compactIsometricAverage` to the restriction quotient action. It
also proves that the published `L²` equivalence `quotientL2Equiv` carries the
positive-torus average to the new one.

## Data

- `F : Type` is a number field.
- `G` is a group scheme over `Spec F` whose underlying scheme is affine and
  locally of finite type.
- `S` is a commutative group scheme over `ℚ` and
  `j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G` maps it into the Weil
  restriction.
- `T` is a commutative group scheme over `F` and `i : T.toGrp ⟶ G`.
- `K` is an actual open subgroup of `FiniteAdelicGroupPoints F G`, with the
  original finite adelic topology.

Write `μ = quotientHaarMeasure F G S j`, `R` for the right action on
`Lp ℂ 2 μ`, and `ι = AdelicGroupPoints.ofFinite F G` for the published
continuous inclusion of the finite adelic points. `hInv'` is an arbitrary proof
of `QuotientRightInvariant F G μ`, and every result here holds for whichever
proof is given.

## Restriction to the finite adelic points

For any measure `measureQ` on `Quotient F G S j` with
`hInv : QuotientRightInvariant F G measureQ`:
- `rationalQuotientL2FiniteRightAction` is the representation of
  `FiniteAdelicGroupPoints F G` on `Lp ℂ 2 measureQ` obtained by composing the
  right action with `ι`. This module reuses the declaration from
  `GroupSchemeRestrictionCuspidalL2`; its new `_apply` lemma holds by definition.
- `rationalQuotientL2CompactOpenAction` is the homomorphism from `K` to bounded
  operators. It composes the published `rationalQuotientL2BoundedRightAction`
  with `ι` and the subgroup inclusion. Its `_apply` lemma holds by definition.
- `norm_rationalQuotientL2CompactOpenAction` proves `‖R(ι k) φ‖ = ‖φ‖`, by the
  published norm equality for the bounded action.

No comparison hypothesis is needed for this section.

## Averaging over a compact open subgroup

Assume `h : subgroup F G S j = imageSubgroup F T G i`. Assume also that
`characterRestrict i` is injective with finite-index range, that
`hc : IsCentral i`, that `hT : IsSplitTorus T.toGrp`, and that Haar measure on
`normOneSubgroup F G` is right invariant. These are the hypotheses of the
published joint continuity result for `[G]`.

- `continuous_rationalQuotientL2CompactOpenOrbit` proves that
  `k ↦ R(ι k) φ` is continuous on `K` with the subgroup topology. It composes
  the published continuous orbit `rationalQuotientL2OrbitMap φ` with `ι` and
  the subtype inclusion.

Now assume `[CompactSpace K]`. By Mathlib's `isCompact_iff_compactSpace`, this
is equivalent to compactness of `K` as a subset of the finite adelic points. On
`K` the module reuses the published positive-torus local instances: the
topological group structure of the subgroup, second countability induced from
the finite adelic points, and the Borel σ-algebra. The group integral is taken
against the published normalized Haar probability measure
`compactProbabilityHaar K`. This measure on `K` is different from the
quotient measure `μ` that defines the `L²` norm.

- `rationalQuotientL2FiniteAverage` is the bounded operator
  `compactIsometricAverage K πK _ _`, where `πK` is the compact open action
  above.
- `rationalQuotientL2FiniteAverage_apply` gives its value
  `∫ k : K, R(ι k) φ ∂(compactProbabilityHaar K)`.
- `rationalQuotientL2FiniteAverage_integrable` proves Bochner integrability of
  the orbit for every `L²` class.
- `norm_rationalQuotientL2FiniteAverage_le` bounds the operator norm by `1`.
- `rationalQuotientL2FiniteAverage_fixed` proves `R(ι k) (P φ) = P φ` for
  every `k : K`, where `P` is the average.
- `rationalQuotientL2FiniteAverage_eq_self_iff` proves that `P φ = φ` exactly
  when `φ` is fixed by every element of `K`.
- `rationalQuotientL2FiniteAverage_idempotent` proves `P ∘ P = P`.

These results are the corresponding published facts about
`compactIsometricAverage`, applied to `πK`.

- `rationalQuotientL2FiniteAverage_mem_fixedVectors` proves that every output
  lies in the published `Langlands.fixedVectors` submodule of
  `rationalQuotientL2FiniteRightAction` for `K`.
- `rationalQuotientL2FiniteAverage_isSmoothVector` proves that every output is
  a `Langlands.IsSmoothVector` of the finite right action, with witness `K`.
- `rationalQuotientL2FiniteFixedRetraction` is the average with codomain the
  `K`-fixed vectors. `_val` says that its underlying vector is `P φ`, and
  `_inclusion` says that it is the identity on `K`-fixed vectors.

## Comparison with the positive-torus average

- `quotientL2Equiv_finiteAverage` takes explicit splitting coordinates `I` and
  `e : T.toGrp ≅ splitTorus (Spec F) I`. It proves
  `E (P⁺ φ) = P (E φ)` for every `φ` in `L²` of the positive-torus quotient
  measure `positiveRationalQuotientHaarMeasure F G T i`. Here
  `E = quotientL2Equiv F G h` and `P⁺` is the published
  `haarQuotientL2FiniteAverage F G T i hi I e hc K`. The proof moves `E` inside
  the Bochner integral using Mathlib's `LinearIsometry.integral_comp_comm`, then
  rewrites the integrand with the published `quotientL2Equiv_rightAction`.

## Split components

Assume `hj : IsSplitComponent j` and `hs : IsSplitComponent i`, together with
the injectivity and finite-index hypotheses on `characterRestrict i`, the
norm-one right-invariance instance and `[CompactSpace K]`. The comparison
equality is the published `subgroup_eq_of_splitComponents F G hj hs`. Right
invariance of `μ` is the published
`quotientHaarMeasure_rightInvariant_of_splitComponents`. Centrality and the
split-torus property come from `hs`.

- `splitComponentL2FiniteAverage F G hi K hj hs` is the average for this data.
  `splitComponentL2FiniteAverage_apply` gives its value as the Bochner
  integral of the published `splitComponentL2RightAction` over `K`.
- `norm_splitComponentL2FiniteAverage_le`,
  `splitComponentL2FiniteAverage_eq_self_iff` and
  `splitComponentL2FiniteAverage_isSmoothVector` specialize the results
  above.
- `splitComponentL2Equiv_finiteAverage` proves that the published
  `splitComponentL2Equiv F G hj hs` carries the positive-torus average, for any
  splitting coordinates of `T`, to `splitComponentL2FiniteAverage`.

## Provenance and scope

The quotient follows Getz--Hahn (2.20)--(2.21). Every construction here is
internal. It applies the published `compactIsometricAverage` to the published
bounded and jointly continuous right action on `[G]`, and compares the result
with the published positive-torus average through the published `L²`
equivalence. No literature theorem is attributed to this module.

The module proves smoothness for the finite adelic action of its outputs only.
It does not prove density of smooth vectors, convergence of the averages as `K`
shrinks, archimedean smoothness, admissibility, or any spectral decomposition.
The existence of split components and the injectivity and finite index of
`characterRestrict i` are hypotheses here and are not proved in this module.
Norm-one right invariance is an instance hypothesis. For smooth connected `G`,
and hence for connected reductive `G`, the published
`AdelicGroupPoints.normOneHaarRightInvariant` in
`Langlands.Global.AdelicNormOneHaarRightInvariantProof` supplies it. This
module does not invoke that proof.
