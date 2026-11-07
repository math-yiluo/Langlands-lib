# Native relative kernel integral

This is an internal extension of the published split-kernel restriction and
complex quotient-integral constructions to native modules over a commutative
complex algebra `R`. The coefficient ring, ambient group, section group and
coefficient carriers have independent universe parameters. The complex and
`R`-module structures on each carrier form a scalar tower.

Let `r : G →* L` have a continuous homomorphic section `s`, with
`r (s l) = l`. Assume `G` is a locally compact topological group, `H` is a
closed subgroup containing the image of `s`, and `σ` is a smooth
`R`-linear representation of `H`. Write `N = ker r`, `I = H ∩ N`, and
`σI` for the actual restriction of `σ` to `I`.

`splitKernelCompactEquiv` is the imported arbitrary-coefficient equivalence
obtained by restricting the original compactly supported covariant function
to `N`. The new `splitKernelCompactCoinvariantRestrictEquiv` applies the
actual full-coinvariant functor to this equivalence and its inverse. Thus
its source is the quotient of the original compact induction by its
`N`-relations, and its target is the full coinvariant quotient of the
compact induction from `I` to `N`. Both inverse laws follow on original
function representatives. No quotient comparison is supplied as a premise.

`fullCoinvariantsComplexScalarTower` records that the complex scalars and
native scalars on the actual relation quotient still form a tower.
`isSmooth_splitKernelInducing` derives smoothness of `σI` by continuous
restriction to the intersection; it works over any commutative coefficient
ring and needs no complex structure.

## The integral and its quotient

Supply a Borel measure `ν` on `I \ N` which is finite on compact sets.
`splitKernelCompactIntegral` first restricts the original compact function
to `N`, then applies the native `compactCoinvariantIntegral`. It is
`R`-linear, with target the actual native quotient `σI_I`.
The displayed `_apply` formula is the published complex finite-fiber
algebraic integral, followed by `fullCoinvariantsComplexEquiv`. This
comparison sends the complex class of each original vector to its native
class. The theorem `splitKernelCompactIntegrand_mk` states that the
integrand at the quotient class of `n` is exactly the native class of
`f(n)`. Complex scalar restriction changes neither vectors nor functions.

When every right translation on `I \ N` preserves `ν`,
`splitKernelCompactIntegral_translate` proves invariance under each actual
right translation by `n ∈ N`. The proof uses equivariance of the imported
restriction map and invariance of the native absolute integral.
`splitKernelCompactCoinvariantDesc` composes the quotient restriction
equivalence with the native absolute integral descent. Its `_mk` and
`_mk_integral` formulas identify its value on `[f]` with this same
relative integral.

For an arbitrary native coefficient intertwiner `T : σ → τ`, the theorems
`splitKernelCompactIntegral_natural` and
`splitKernelCompactCoinvariantDesc_natural` commute with the actual
pointwise postcomposition of compact functions and the quotient map
induced by the restricted `T`. The two coefficient carriers can live in
independent universes. The proofs use naturality of actual kernel
restriction and of the native absolute integral, followed by quotient
surjectivity for descent.

## Bijectivity

The final section additionally assumes that `G` is Hausdorff, `N` is
locally compact, and the neighborhoods of `1 ∈ N` have the stated basis
of compact open subgroups. Supply Borel structures on `N` and `I`,
regular left and right Haar measures `μN` and `μI`, and
`IsCompatible I μN μI ν`. This compatibility retains nonzeroness,
regularity, right invariance and the Weil formula of the published
quotient-measure definition. Local compactness of `I` follows from its
closedness in `N`.

`splitKernelCompactCoinvariantDesc_bijective` composes the bijectivity of
the actual quotient restriction equivalence with the proved native
absolute quotient-integral bijectivity theorem. The intersection
closedness and the smoothness of `σI` are derived from the hypotheses
above. `splitKernelCompactCoinvariantEquiv` packages this same descended
map as an `R`-linear equivalence

```text
(c-Ind_H^G σ)_N  ≃ₗ[R]  σI_I.
```

Its `_mk` formula retains the explicit finite-fiber integral of the
original restricted function, and its `_natural` theorem retains
naturality under every native coefficient intertwiner.

This unit introduces no new geometric or representation-theoretic
premise beyond the displayed topology, smoothness and supplied measure
data. It constructs neither those measures nor rational orbit geometry.
The companion `CoefficientSplitKernelEquivariant` module proves the
section covariance and packages its precise Haar twist. Compact
induction in stages, normalized rational orbit identification and native
compact-open fixed-module finiteness remain separate obligations.
