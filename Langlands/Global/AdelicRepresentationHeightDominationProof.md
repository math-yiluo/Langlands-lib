# Closed embeddings dominate full adelic representation heights

`Langlands.Global.RepresentationGrowth.closedImmersionAdelicHeightDomination`
proves the existing proposition
`Langlands.Global.RepresentationGrowth.ClosedImmersionAdelicHeightDominationStatement`
at its arbitrary universe `u`. For every number field `F`, every actual group
scheme `G` over `Spec F`, positive natural ranks `N` and `M`, and matrix
representations `rho : G -> GL_N` and `sigma : G -> GL_M`, a scheme-theoretic
closed immersion `rho` gives a real `C >= 1` and a natural `e` such that

```text
adelicHeight F G sigma g <= C * (adelicHeight F G rho g)^e
```

for every actual full adelic point `g`. Both witnesses precede the point
quantifier. This is exactly the published statement, without additional
hypotheses on the group, either representation, or local estimates.

The height is the existing `RepresentationGrowth.adelicHeight`. At an infinite
place `v`, its factor is `(rank * localMaximum v)^v.mult`, where the maximum
contains every matrix entry and every inverse-matrix entry. The finite factor
is the `finprod` of the corresponding unscaled local maxima over all finite
places. The proof preserves these factors and the existing place
multiplicities.

## Polynomial estimates

`exists_adelic_polynomial_bound` concerns a family `z x c` of elements of
`Adeles F`, indexed by points `x` and variables `c`. Suppose functions `hi x v`
and `hf x v` are at least one and bound every variable norm at the respective
infinite and finite places. For a fixed polynomial `p` over `F`, the lemma
produces functions `A` on infinite places and `B` on finite places, and a
single natural `e`, such that

```text
1 <= A v,    1 <= B v,    B.HasFiniteMulSupport,
||infiniteProjection v (aeval (z x) p)|| <= A v * (hi x v)^e,
||finiteProjection v (aeval (z x) p)||   <= B v * (hf x v)^e.
```

The constants and exponent are independent of `x`; the exponent is also
independent of the place. The exponent is a bound produced by induction and
need not be the polynomial's minimal degree.

The implemented proof uses `MvPolynomial.induction_on`:

- For a constant coefficient `r`, let `a` be its image in the full adele
  algebra. Take exponent zero and the local constants
  `max ||projection v a|| 1`. The finite adele component of `a` is integral
  at almost every finite place by its actual restricted-product membership.
  The completion-integer membership criterion and
  `Valued.toNormedField.norm_le_one_iff` then show that the finite constant
  equals one at almost every place. This proves finite multiplicative
  support.
- For addition, add the infinite constants, take the maximum of the finite
  constants, and take the maximum of the two exponents. The ordinary triangle
  inequality handles infinite places; `IsUltrametricDist.norm_add_le_max`
  handles finite places. Since each controlling function is at least one,
  either power is bounded by the common power. Finite multiplicative support
  is preserved by the maximum.
- For multiplication by a variable, retain the constants and increase the
  exponent by one, using multiplicativity of the local norms and the given
  variable bound.

`exists_adelic_polynomial_family_bound` combines this result for a finite
family of polynomials. It multiplies the respective constants and sums the
exponents. Each constant is at least one, so its factor is bounded by the
product; each exponent is at most the sum, and the controlling functions are
at least one. A finite product of finite-support functions again has finite
multiplicative support. This supplies common constants and one exponent for
all coordinates simultaneously.

## Closed-embedding coordinates

The algebraic input is the published
`exists_coordinate_polynomial` from
`RepresentationHeightDominationProof`. For every entry and inverse entry of
`sigma`, it gives a fixed polynomial over `F` in the entries and inverse
entries of `rho`, valid at every affine `F`-algebra point. The proof applies
this identity at the actual algebra `Adeles F`. No separately supplied local
domination assertion is used.

The finite coordinate set `Coordinate (Fin M)` is given a local `Fintype`
instance using its equivalence with two copies of `Fin M × Fin M`.
The variable values are the coordinates of `adelicMatrix F G rho g`. The
controlling functions are

```text
hi g v = N * infiniteLocal F N (adelicMatrix F G rho g) v,
hf g v = finiteLocal F N (adelicMatrix F G rho g) v.
```

Positive rank and the existing matrix-height lemmas make both functions at
least one. Every coordinate norm is at most its local maximum, by
`MatrixInverseHeight.entry_le_localMaximum` and the invariance of that
maximum under inversion. At infinite places `N >= 1` also bounds this
maximum by the scaled function `hi`.

The private helper `norm_coordinate_le_localMaximum` records these coordinate
bounds. The other private helper, `localMaximum_le_of_coordinates`, bounds the
maximum by any nonnegative simultaneous bound on all coordinates; it uses
the finite function norm formula twice for the matrix and its inverse.
Consequently the common polynomial estimates give

```text
infiniteLocal sigma g v <= A v * (hi g v)^e,
finiteLocal sigma g v   <= B v * (hf g v)^e.
```

## Product assembly

Set

```text
Ci = product over infinite v of (M * A v)^v.mult,
Cf = finprod over finite v of B v,
C  = Ci * Cf.
```

All factors defining `Ci` and `Cf` are at least one, hence `C >= 1`.
These constants and `e` have already been chosen before introducing `g`.

For finite places, the existing
`AdelicMatrixHeight.hasFiniteMulSupport_finiteLocal` applies to both
representations at `g`, since their ranks are positive. Finite multiplicative
support of `B` and of `(hf g)^e` justifies `finprod_mul_distrib` and
`finprod_pow`. Monotonicity via `finprod_le_finprod₀` therefore yields the
bound by `Cf * (finprod v, hf g v)^e`.

For infinite places, multiply the local estimates by `M`, raise each to the
original natural multiplicity `v.mult`, and take the finite product. The
identities for powers and products give the bound by
`Ci * (product v, (hi g v)^v.mult)^e`.
Multiplying the two estimates and regrouping powers gives exactly the
asserted inequality for `adelicHeight`, with the original dimension scaling,
full finite product, and complex-place multiplicities.

## Provenance and scope

This is an internally derived proof of the Library proposition. Its
[statement Markdown](AdelicRepresentationHeightDominationStatement.md) records
the Getz–Hahn motivation and the distinction between that source and the
Library's coordinate-algebra generalization. The present argument reuses the
published algebraic coordinate-polynomial theorem and supplies the simultaneous
adelic estimates and their product assembly directly. It does not rely on the
earlier mixed-space infinite-height domination theorem.

This contribution proves only full adelic height domination. Growth
independence and properness are separate consequences and are not asserted
here.
