# The lower mixed quotient in JPSS Section 4.9

This module constructs the actual lower mixed subgroup and its quotient for
JPSS (1983), Section 4.9, equations (2) and (8), printed pages 416 and 418.
Its namespace is
`Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient`. The field is every
canonical `F : PadicField.{uF} p`, for every prime `p` and arbitrary universe
`uF`. The two ranks `a = m 0 + 1` and `b = m 1 + 1` are arbitrary positive
integers, with `a + b = t + 1`. All topology is the canonical topology.

The registered source is `jpss-1983-rankin-selberg`, H. Jacquet,
I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg convolutions*,
American Journal of Mathematics 105 (1983), 367–464, original PDF
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The rendered original has printed pages 412–413 at zero-based PDF indices
47–48 and printed pages 416–418 at indices 51–53. These locators are one
page later than the contract's stated offset. No applicable registered
errata file was found in the supplied project resources.

Printed page 412, Section 4.6 equation (5), supplies the block diagonal
unipotent subgroup, while printed page 413 supplies the lower block
unipotent subgroup. Printed page 416 defines the larger lower mixed group
`L` immediately after equation (2). Equation (2) integrates over rectangular
lower radical fibers, from the zero slice of the diagonal mixed quotient
through `L \ G^0`. Printed page 418, equation (8), uses the same lower mixed
quotient and fibers from `N_a \ GL_a`, with density `|det a|^b`. The
unweighted small slice average intended here corresponds to the fact that
this density is constant `q^(-k*b)` on determinant slice `k`. These are
provenance statements about the source displays; the integration formulas
are outside the module's claims.

## Subgroup and actual coordinates

Write `B = succBlockShape m h`, `G = GeneralLinear (t + 1) F.Carrier`,
`R(Z) = TwoBlockLowerUnipotentQuotient.lowerRadical h F.Carrier Z` and
`D(a0,n) = TwoBlockFirstBlockQuotient.mixedEmbedding F h (a0,n)`.
The selected definition `lowerMixedSubgroup F h` consists precisely of
products `R(Z) D(a0,n)` with `a0` in the published `normOneSubgroup F a`
and `n` in the published `upperUnipotent b F.Carrier`. No subgroup or
factorization assertion is an input.

The helper `entryBlock h R g i j` is the actual matrix subblock in the
published `B.index` coordinates. The four `entryBlock_lowerProduct` lemmas
show that `lowerProduct Z a0 n = R(Z) D(a0,n)` has blocks
`[[a0,0],[Z*a0,n]]`. `mem_lowerMixedSubgroup_iff` characterizes membership
by the vanishing upper-right block, normalized absolute value one for the
first diagonal determinant, and the lower-entry and diagonal conditions
for the upper-unipotent second block. The lower-left block has no
condition. The backward implication uses the actual opposite Levi
projection: its two diagonal blocks are invertible, and
`oppositeParabolic_factorization` reconstructs `g` with radical coordinate
`entryBlock g 1 0 * a0⁻¹`.

`mixedSubgroup_le_lowerMixedSubgroup` and
`lowerBlockUnipotent_le_lowerMixedSubgroup` give the two distinct published
subgroup inclusions. `lowerMixedSubgroup_le_oppositeParabolic` gives the
opposite-parabolic inclusion, and `lowerMixedSubgroup_le_normOneSubgroup`
follows by determinant multiplicativity, `det R(Z) = 1`, and the published
determinant of `D(a0,n)`.

`lowerMixedDiagonal` extracts the actual opposite Levi blocks, retaining
their norm-one and upper-unipotent proofs. `lowerMixedCoordinates` returns
`(X*a0⁻¹,(a0,n))`. `lowerMixedSubgroupEquiv` and
`lowerMixedSubgroupHomeomorph` give the required equivalence and
homeomorphism. Their evaluation and inverse-coordinate lemmas identify the
representative and all three actual coordinates. `isUnit_entryBlock_zero_zero`
records explicitly that the first entry block is invertible.

The multiplication and inverse formulas are

```text
(Z,a0,n) * (Z2,a2,n2) = (Z + n*Z2*a0⁻¹, a0*a2, n*n2),
(Z,a0,n)⁻¹ = (-n⁻¹*Z*a0, a0⁻¹, n⁻¹).
```

They are proved as `lowerProduct_mul`, `lowerProduct_inv` and the
corresponding `lowerMixedSubgroupEquiv_mul` and `_inv` laws. The equivalence
is not asserted to preserve the direct product group multiplication.
The block multiplication proof splits the matrix sum into the two blocks
and uses matrix associativity and the unit inverse equations. Continuity
of the forward coordinates uses the published continuous Levi embedding
and lower radical; continuity of the inverse uses the continuous opposite
Levi projection and matrix multiplication. Closedness follows from the
same intrinsic block criterion: entry equalities are closed and the
normalized absolute value of the first block determinant is continuous.

## Quotient and determinant slices

`LowerMixedQuotient F h` is exactly
`QuotientIntegration.LeftQuotient (lowerMixedSubgroup F h)`.
`projectionFromMixed` and `projectionFromLower` descend the identity on
representatives from the two published quotients. They are continuous,
surjective and compatible with right translation, with the displayed
representative formulas. `t2Space_lowerMixedQuotient` uses closedness of
the actual subgroup to prove that the quotient is Hausdorff.

`determinantOrder F h` descends `ord(det g)` using the proved norm-one
inclusion, and `determinantSlice F h k` is its fiber at `k : ℤ`. The
representative formula and continuity are explicit. Each slice is clopen
and measurable for the Borel structure. Distinct slices are disjoint and
their union is the full quotient. Right translation adds `ord(det g)` to
the order. The preimage of each slice under either projection is exactly
the corresponding published source slice. Thus the source's `L \ G^0`
is the zero slice of this quotient.

## Commutation of the lower radical with block-diagonal matrices

Write `I(v) = TwoBlockFirstBlockQuotient.firstBlockEmbedding h F.Carrier v`
and `Hminus = TwoBlockLowerUnipotentQuotient.lowerBlockUnipotent h F.Carrier`.
Over an arbitrary commutative ring, `lowerRadical_mul_leviEmbedding_blockPair`
and `leviEmbedding_blockPair_mul_lowerRadical` prove the block identities

```text
R(W) * diag(u,w) = diag(u,w) * R(w⁻¹ * W * u),
diag(u,w) * R(W) = R(w * W * u⁻¹) * diag(u,w)
```

for invertible diagonal blocks `u` and `w`, where `diag(u,w)` is the
published Levi embedding of `blockPair (u,w)`. Both are proved block by
block with `ext_entryBlock` and the entry-block formulas for `R(W)` and the
Levi embedding, followed by matrix associativity and the unit inverse
equations. `firstBlockEmbedding_mul_lowerRadical` is the case `w = 1`:
`I(v) * R(W) = R(W * v⁻¹) * I(v)`.
`leviEmbedding_blockPair_mem_lowerBlockUnipotent` shows that `diag(u,w)`
lies in `Hminus` when both blocks are upper unipotent, using the published
block criterion `mem_lowerBlockUnipotent_iff`;
`firstBlockEmbedding_mem_lowerBlockUnipotent` is the case `w = 1`.

## Rectangular fibers and their total average

`radicalFiberPoint F h Z g` is the class `[R(Z) * g]` in the published
`MixedQuotient F h = M \ G`, where `M = mixedSubgroup F h` and
`Z : Matrix (Fin b) (Fin a) F.Carrier`. It is the point at which the inner
integrand of equation (2), printed page 416, evaluates `F`: the source writes
`F[(1 0; z 1) h]` with the rectangular variable `z`. The map is defined on
all of `G`; restricting to the source's zero slice is expressed by the slice
law below.

- `continuous_radicalFiberPoint` proves joint continuity in `(Z, g)` from the
  proved continuity of `R` (`continuous_lowerRadical`), continuity of
  multiplication in `G` and continuity of the quotient map.
- `radicalFiberPoint_mul` proves
  `radicalFiberPoint Z (g * g') = rightTranslate g' (radicalFiberPoint Z g)`.
- `determinantOrder_radicalFiberPoint` proves that the published determinant
  order of `M \ G` at the fiber point is `T.ord (det g)`, because
  `det R(Z) = 1`. `radicalFiberPoint_mem_determinantSlice_iff` is the
  corresponding membership law for the published slices of `M \ G`.

`radicalChange F Z0 a0 n Z = n⁻¹ * (Z + Z0) * a0` is the affine change of
rectangular coordinates attached to `l = R(Z0) * D(a0,n)`; it is stated for
rectangles of arbitrary sizes. `radicalFiberPoint_lowerRadical_mixedEmbedding_mul`
proves the representative-change formula

```text
radicalFiberPoint Z (R(Z0) * D(a0,n) * g) =
  radicalFiberPoint (n⁻¹ * (Z + Z0) * a0) g.
```

The proof combines `R(Z) * R(Z0) = R(Z + Z0)` (`lowerRadical_add`), the
commutation `R(Z + Z0) * D(a0,n) = D(a0,n) * R(n⁻¹ * (Z + Z0) * a0)` from
the first identity above, and the published `mk_mul_of_mem`, which absorbs
the left factor `D(a0,n) ∈ M` into the class.

`radicalChangeHomeomorph` packages the affine change as a homeomorphism of
the rectangle, with inverse `W ↦ n * W * a0⁻¹ - Z0`.
`measurePreserving_radicalChange` proves that, for every measurable
structure on the rectangle that is Borel for the canonical topology and
every additive Haar measure `μR` on it, the affine change maps `μR` to
`μR`. The proof factors the change as the translation `Z ↦ Z + Z0`
followed by the linear map `X ↦ n⁻¹ * X * a0`. Translation preserves `μR`
by additive invariance (`map_add_right_eq_self`; the rectangle is a
commutative group). The published
`Langlands.HarmonicAnalysis.padicRectangularHaarScaling`, applied to
`A = n⁻¹` and `B = a0⁻¹`, gives the linear part with scaling factor one:
an upper unipotent matrix has determinant norm one
(`determinantNorm_eq_one_of_mem_upperUnipotent`), and `a0` has determinant
norm one by definition of `normOneSubgroup`. `integral_comp_radicalChange`
deduces `∫ Z, G (radicalChange Z0 a0 n Z) dμR = ∫ Z, G Z dμR` for every
function `G` into `ℂ`, with no integrability hypothesis, from
`MeasurePreserving.integral_comp` and the measurable embedding given by the
homeomorphism.

In the section `Average`, a measurable structure on the rectangle is a
section variable. `radicalFiberIntegral F h μR f g` is the total Bochner
integral `∫ Z, f (radicalFiberPoint Z g) dμR` for arbitrary
`f : MixedQuotient F h → ℂ` and arbitrary `μR`.

- `radicalFiberIntegral_lowerRadical_mixedEmbedding_mul` proves invariance
  under left multiplication of `g` by `R(Z0) * D(a0,n)`, for a Borel
  additive Haar measure `μR`, from the representative-change formula and
  `integral_comp_radicalChange`.
- `radicalFiberIntegral_lowerMixedSubgroup_mul` extends this to every element
  of `lowerMixedSubgroup F h` through the coordinate decomposition
  `lowerMixed_decomposition`.
- `radicalFiberIntegral_mul` shows that right translation of `g` by `g'` is
  right translation of the integrand `f` by `g'`; it holds for every measure.

`radicalAverage F h μR f : LowerMixedQuotient F h → ℂ` is
`QuotientIntegration.descend` of `radicalFiberIntegral F h μR f` along this
invariance; it takes the Borel and additive Haar instance arguments.
`radicalAverage_mk` is the representative formula
`radicalAverage μR f [g] = ∫ Z, f (radicalFiberPoint Z g) dμR`, and
`radicalAverage_rightTranslate` proves
`radicalAverage μR f (rightTranslate g q) =
radicalAverage μR (f ∘ rightTranslate g) q`. No coset representative is
chosen and no integrability premise appears.

## First-block fibers and their total slice average

`firstBlockFiberPoint F h q g`, for `q` in the published
`RankinSelberg.LeftUnipotentQuotient (m 0) F.Carrier = N_a \ GL_a`, is
defined by `QuotientIntegration.descend` from `v ↦ [I(v) * g]` in the
published `LowerQuotient h F.Carrier = Hminus \ G`. It is well defined
because `I(n * v) * g = I(n) * (I(v) * g)` and `I(n) ∈ Hminus` for
`n ∈ N_a` (`firstBlockEmbedding_mem_lowerBlockUnipotent`). This is the
point at which the inner integrand of equation (8), printed page 418,
evaluates `F`: the source writes `F[(a 0; 0 1) h]` with `a ∈ N_a \ GL_a`.

- `firstBlockFiberPoint_mk` is the representative formula
  `firstBlockFiberPoint [v] g = [I(v) * g]`.
- `continuous_firstBlockFiberPoint` proves joint continuity in `(q, g)`.
  The product of the published open quotient map `GL_a → N_a \ GL_a` with
  the identity of `G` is an open quotient map, and the composite with it is
  `(v, g) ↦ [I(v) * g]`, continuous by the published continuity of
  `firstBlockEmbedding`.
- `firstBlockFiberPoint_mul` is the right-translation law
  `firstBlockFiberPoint q (g * g') = rightTranslate g' (firstBlockFiberPoint q g)`.
- `determinantOrder_firstBlockFiberPoint` proves that the published
  determinant order of `Hminus \ G` at the fiber point is the published small
  order `RankinSelberg.determinantOrder T (m 0) q` plus `T.ord (det g)`, by
  multiplicativity of `ord` and the published determinant of `I(v)`.
  `firstBlockFiberPoint_mem_determinantSlice_iff` is the corresponding
  membership law for the published slices of `Hminus \ G`.

`firstBlockEmbedding_mul_lowerRadical_mul_mixedEmbedding` proves the block
identity

```text
I(v) * (R(Z0) * D(a0,n)) = R(Z0 * v⁻¹) * diag(1,n) * I(v * a0)
```

from `firstBlockEmbedding_mul_lowerRadical` and the published
`firstBlockEmbedding_mul_leviEmbedding_blockPair`.
`lowerRadical_mul_leviEmbedding_one_mem` shows that the first two factors
lie in `Hminus`. Hence `firstBlockFiberPoint_lowerRadical_mixedEmbedding_mul`
proves

```text
firstBlockFiberPoint q (R(Z0) * D(a0,n) * g) =
  firstBlockFiberPoint (rightTranslate a0 q) g.
```

The supplied measure `μA` on `N_a \ GL_a` is any measure for the Borel
structure of the canonical quotient topology. For an integer `k` and
arbitrary `f : LowerQuotient h F.Carrier → ℂ`,
`firstBlockFiberIntegral F h μA k f g` is the total Bochner set integral

```text
∫ q in RankinSelberg.determinantSlice T (m 0) k,
  f (firstBlockFiberPoint q g) dμA.
```

- `firstBlockFiberIntegral_lowerRadical_mixedEmbedding_mul` proves invariance
  under left multiplication of `g` by `R(Z0) * D(a0,n)`, assuming the
  published `TwoBlockFirstBlockQuotient.NormOneRightInvariant F (m 0) μA`.
  After the change formula, right translation by `a0` maps `μA` to itself by
  that hypothesis, and it maps the small slice `k` onto itself because
  `ord(det a0) = 0` (`rightTranslate_mem_determinantSlice` and
  `ord_determinant_eq_zero`). The set-integral change of variables
  `MeasurePreserving.setIntegral_preimage_emb` along the measurable embedding
  `rightTranslate a0` needs no integrability hypothesis.
- `firstBlockFiberIntegral_lowerMixedSubgroup_mul` extends this to every
  element of `lowerMixedSubgroup F h` through `lowerMixed_decomposition`.
- `firstBlockFiberIntegral_mul` shows that right translation of `g` by `g'`
  is right translation of the integrand `f` by `g'`.

`firstBlockAverage F h μA hμA k f : LowerMixedQuotient F h → ℂ` is
`QuotientIntegration.descend` of `firstBlockFiberIntegral F h μA k f` along
this invariance. `firstBlockAverage_mk` is the representative formula and
`firstBlockAverage_rightTranslate` the right-translation law. In equation
(8) the inner integral runs over all of `N_a \ GL_a` with density
`|det a|^b`. On small slice `k` that density is the constant `q^(-k*b)`, so
the unweighted slice average `firstBlockAverage` is the intended per-slice
data; the module does not sum over slices or insert the density.

## Scope

All results are derived constructions implementing the matrices and
domains displayed in equations (2) and (8); none is a statement printed in
the source. The module supplies neither integration formula (2) or (8),
the existence of compatible quotient measures, unimodularity of
`Lminus`, normalization of measures, outer measurability of arbitrary
averages, Tonelli or Fubini statements, convergence, representation
integrands nor functional equations. The averages are total Bochner
integrals, which are zero for non-integrable fibers; their invariance and
descent hold for every scalar function without integrability premises.
