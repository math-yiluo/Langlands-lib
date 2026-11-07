# An analytic engine for products of global functional equations

## Contents

The module, in namespace `Langlands.Global.FunctionalEquationComparison.RelativeWeilEngine`,
collects generic analytic bookkeeping for the proof of
`RelativeWeilTwistFunctionalEquationStatement`. It uses the published notions
`MeromorphicEq` (equality of punctured germs at every point of `ℂ`) and `NonzeroMeromorphic`
(meromorphic on `ℂ` with germ not identically zero anywhere) from
`Langlands.Global.Factors.FiniteComparisonStatement`. Nothing here is specific to number
fields or to Weil groups. The equivalence-relation, finite-product and reflection
helpers, including `NonzeroMeromorphic.reflect`, are reused from
`FiniteComparisonProof` in the enclosing `FunctionalEquationComparison` namespace.

### Punctured germs

- The imported `MeromorphicEq.refl`, `.symm`, `.trans`, and the new `meromorphicEq_of_eq`
  (pointwise equality gives germ equality): `MeromorphicEq` is an equivalence relation.
- `MeromorphicEq.mul`, `MeromorphicEq.inv`, `MeromorphicEq.zpow n`, the imported `MeromorphicEq.finset_prod`:
  germ equality is compatible with products, inverses, integer powers and finite products.
- The imported `reflection_tendsto` and `MeromorphicEq.reflect`: the reflection `s ↦ 1 - s` maps
  punctured neighbourhoods of `z` to punctured neighbourhoods of `1 - z`, so germ equality of `f`
  and `g` gives germ equality of `s ↦ f (1 - s)` and `s ↦ g (1 - s)`.
- `meromorphicEq_of_codiscrete`: equality eventually along `Filter.codiscrete ℂ`, that is,
  equality outside a closed discrete subset of `ℂ`, gives germ equality.
- `meromorphicEq_cancel`: if `g` is `NonzeroMeromorphic`, then
  `a s · (g s)⁻¹ · (b s · g s)` and `a s · b s` have the same punctured germs.

### Nonzero meromorphic functions

- `NonzeroMeromorphic.meromorphicAt`, `NonzeroMeromorphic.congr` (invariance under germ
  equality), `nonzeroMeromorphic_const` (nonzero constants), `nonzeroMeromorphic_one`.
- `NonzeroMeromorphic.mul`, `.inv`, `.zpow n`, `.finsetProd`, `.reflect`: closure under
  products, inverses, integer powers, finite products and `s ↦ 1 - s`.
- `nonzeroMeromorphic_of_ne_zero_halfPlane`: a function meromorphic on `ℂ` that is nonzero at
  every point of some right half-plane `σ < Re s` is `NonzeroMeromorphic`.

### Products with nonzero limits

- `ne_zero_of_hasProd`: if `HasProd f a` and `a ≠ 0`, then every factor `f i` is nonzero.
- `hasProd_zpow`: if `HasProd f a` and `a ≠ 0`, then `HasProd (f · ^ n) (a ^ n)` for every
  integer `n`.
- `hasProd_fiberwise`: if `π : P → Q` has finite fibres `fib q` (`p ∈ fib q ↔ π p = q`), then
  `HasProd f a` gives `HasProd (fun q ↦ ∏ p ∈ fib q, f p) a`.
- `hasProd_compl_of_ne_zero`: if `HasProd f a` and `f z ≠ 0` for `z ∈ B`, then the product over
  `{z // z ∉ B}` has limit `a · (∏_{z ∈ B} f z)⁻¹`.

### Global functional-equation packages

`HasGlobalEquation l d e A Ad Ae T`, for families `l d e : Q → ℂ → ℂ` of local L-factors,
dual L-factors and epsilon factors on a type of places `Q`, functions `A Ad Ae : ℂ → ℂ` (the
archimedean L, dual L and epsilon products) and a finite set `T` of places, says that there are
`σ : ℝ` and `Λ Λd : ℂ → ℂ` such that

- `Λ` and `Λd` are meromorphic on `ℂ`;
- for `σ < Re s`, the product over all `v : Q` of `l v s` has limit `Λ s` (`HasProd`) with
  `Λ s ≠ 0`, and the product of `d v s` has limit `Λd s` with `Λd s ≠ 0`;
- `Λ(s) A(s)` and `Ae(s) (∏_{v ∈ T} e v s) Λd(1 - s) Ad(1 - s)` have the same punctured germs
  everywhere.

The results about packages are:

- `hasGlobalEquation_one T`: all data identically `1`.
- `HasGlobalEquation.mul`, `.inv`, `.zpow n` and `hasGlobalEquation_finsetProd`: packages with
  the same `T` multiply pointwise, invert and take integer powers, and finite products of
  packages are packages.
- `HasGlobalEquation.changeSet`: `T` can be replaced by `T'` when `e v` is identically `1` at
  every place of the symmetric difference.
- `HasGlobalEquation.congr`: `l` and `d` can be replaced by families agreeing with them on some
  right half-plane, uniformly in `v`; `e v` for `v ∈ T`, `A`, `Ad` and `Ae` can be replaced by
  functions with the same punctured germs.
- `HasGlobalEquation.pushforward`: along `π : P → Q` with finite fibres `fib q`, a package on
  `P` with exceptional set `T.biUnion fib` gives a package on `Q` with exceptional set `T` whose
  local data at `q` are the products over `fib q`.

### Conversion to the target format

`complDisjSumEquiv B` is the equivalence from `{z : Q // z ∉ B}` to the places of `I ⊕ Q`
outside `univ.disjSum B`, for a finite type `I`.

`HasGlobalEquation.toFunctionalEquation`: let `I` be a finite type (the infinite places) and
suppose `HasGlobalEquation l d e A Ad Ae B`. Let `arch : I → LocalFactors` and
`f : Q → LocalFactors` satisfy:

- every factor of every `arch w` is `NonzeroMeromorphic`, and the products over `w` of the
  archimedean L, dual L and epsilon factors have the same punctured germs as `A`, `Ad`, `Ae`;
- for some `σ'` and every `z ∉ B`, `(f z).lFactor s = l z s` and `(f z).dualLFactor s = d z s`
  whenever `σ' < Re s`;
- for `z ∈ B`, the three factors of `f z` have the same punctured germs as `l z`, `d z`, `e z`
  and are `NonzeroMeromorphic`.

Then there are `σ`, `Lp` and `Lpd` such that the Euler data with local factors
`Sum.elim arch f` and partial L-functions `Lp`, `Lpd` satisfy `Admissible`,
`HasEulerProductsOutside` at `σ` and `FunctionalEquation`, all at the exceptional set
`univ.disjSum B`. This is the conclusion format of the target statement, whose
`assembledEulerData arch f Lp Lpd` and `exceptionalPlaces F B` unfold to these data and this set.

## Source and provenance

This module is internal derived content: routine bookkeeping with no counterpart in the
literature. In the classical proof of the functional equation of Artin L-functions through
Brauer's induction theorem (Tate, *Number theoretic background*, Corvallis 1979, §3.5; Henniart
2000, §2.3), one multiplies the functional equations of Hecke L-functions with integer
exponents and regroups places of extension fields over places of the base field. The package
`HasGlobalEquation` and its closure lemmas formalize exactly this step. The conversion lemma
adapts a package to the published target format, where the exceptional set contains all
infinite places and the partial L-functions omit the factors of that set.

## Proof

The germ lemmas are filter manipulations: `EventuallyEq.mul`, `.inv`, `.fun_comp`, and
composition with `tendsto_reflect_punctured`. Codiscrete equality is unpacked with
`mem_codiscreteWithin`. For `NonzeroMeromorphic`, the orders are computed with
`meromorphicOrderAt_mul`, `meromorphicOrderAt_inv` and `meromorphicOrderAt_zpow`. The reflected
order is compared through `meromorphicOrderAt_eq_top_iff` and the punctured-neighbourhood map.
For the half-plane criterion, the order is finite at the point `σ + 1`, because the function does
not vanish on a punctured neighbourhood of it. Since `ℂ` is preconnected, the order is then finite
everywhere (`MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected`).

`ne_zero_of_hasProd` notes that a zero factor makes the partial products eventually `0`, so the
limit would be `0`. `hasProd_zpow` uses `HasProd.pow` and, for negative exponents,
`HasProd.inv₀`. `hasProd_fiberwise` transports the product along the equivalence between
`Σ q, fib q` and `P` and applies `HasProd.sigma` with finite inner products.
`hasProd_compl_of_ne_zero` uses `HasProd.congr_cofinite₀` to replace the factors on `B` by `1`,
then `hasProd_subtype_iff_mulIndicator`.

The package lemmas pick the larger of the two half-plane bounds. `HasProd.mul`, `HasProd.inv₀` and
`hasProd_zpow` give the products, and the functional equations combine with the germ lemmas
and pointwise ring identities. For `changeSet`, both products over `T` and `T'` equal the product
over `T ∪ T'` (`Finset.prod_subset`). For `pushforward`, the epsilon product over `T.biUnion fib`
splits with `Finset.prod_biUnion`, because distinct fibres are disjoint.

For the conversion, `Lp s = Λ s · (∏_{z ∈ B} l z s)⁻¹` and `Lpd s = Λd s · (∏_{z ∈ B} d z s)⁻¹`.
The factors on `B` are nonzero on the half-plane by `ne_zero_of_hasProd`. Hence
`hasProd_compl_of_ne_zero`, followed by the agreement of `f` with `l` and `d` off `B` and
transport along `complDisjSumEquiv`, gives `HasEulerProductsOutside` on `max σ σ' < Re s`.
`Λ` and `Λd` are `NonzeroMeromorphic` by the half-plane criterion. The products over `B` are
`NonzeroMeromorphic` because each factor has the germ of a nonzero meromorphic `f z` factor, so
`Lp` and `Lpd` are `NonzeroMeromorphic`. The functional equation splits every product over
`univ.disjSum B` by `Finset.prod_disjSum`. The archimedean and `B` factors are replaced by germs,
the inserted product over `B` cancels by `meromorphicEq_cancel` (reflected for the dual side), and
the package's functional equation joins the two sides.
