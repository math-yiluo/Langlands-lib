# Renard II.3.13: proof of the completed Hecke comparison

Worker 107 and Worker 104, Task 5530. Source: Renard, *Représentations des
groupes réductifs p-adiques*, French version dated 9 July 2026, II.3.13,
Theorem and its proof, printed p.55 / PDF p.61, with the Lemma and its proof,
printed pp.54–55 / PDF pp.60–61; source registration
`renard-2026-representations-groupes-reductifs-padiques`.

The theorem `statements` proves the exact published statement
`Langlands.HarmonicAnalysis.Distribution.RenardCompletion.Statements.{uG}` at
its full universe parameter. For every Hausdorff, locally compact, totally
disconnected topological group `G` with its Borel structure and every left
Haar measure `μ`, it supplies:

- the idempotentedness witness `heckeAlgebra_isIdempotented μ`;
- the bilinear product `essentialProduct μ` on `rightEssentiallyCompact μ`, with
  `essentialProduct_rightSpecification μ`, a proof of
  `RenardEssentialProducts.RightProductSpecification`;
- the additive equivalence `comparison μ` with the published compatible-family
  carrier `IdempotentedRingRightLimit (HeckeAlgebra μ)`, with
  `comparison_specification μ`, a proof of all six clauses of
  `ComparisonSpecification`;
- uniqueness: every additive equivalence satisfying the specification equals
  `comparison μ` (`eq_comparison`).

No countability or unimodularity hypothesis is used. The proof uses the action
laws of `RenardCompletionActions`. It constructs its own product and does not
use a proof of the separate product-existence statement unit.

## Idempotents and fixed tests

`heckeAlgebra_isIdempotented` applies the published
`HeckeAlgebra.finiteFamilyLocalUnits` with the top open subgroup. For a finite
set `s` of Hecke elements, it gives a compact open subgroup `K` whose normalized
indicator `e_K` is an idempotent and a two-sided unit for `s`. The published
`Hecke.NondegenerateEquivalence.idempotented` is not used, because it takes a
`NonarchimedeanGroup` instance that the target's hypotheses do not provide as
an instance.
`exists_leftUnit` extracts an idempotent left unit of a single element.

`Fixes μ e f` means `f * ě = f`, the left-Haar test convolution transposed by
the full right action. Thus `(V*e)(f) = V(f)` for every distribution `V`
(`rightHeckeConvolution_apply_of_fixes`). The following facts hold:

- every test is fixed by some idempotent (`exists_fixes`): a left unit `e` of
  the Hecke element `f̌` gives `e * f̌ = f̌`. Inverting this with
  `inversion_convolution` gives `f * ě = f`;
- a larger idempotent fixes the same tests (`Fixes.mono`), because `e ≤ e'`
  gives `e' * e = e` and `rightTest_assoc` applies;
- the fixed tests of `e` form a subspace (`Fixes.add`, `Fixes.smul`), and any
  two tests have a common fixing idempotent (`exists_fixes_two`, by the
  published `IsIdempotented.finite_upper_bound`);
- a distribution is determined by its actions `V*e` for all idempotents `e`
  (`distribution_ext_of_idempotents`).

Two lemmas convert the hypotheses used in the target into `Fixes`:

- `rightInvariant_of_rightConvolveTest`: if the published right convolution of
  `f` with the Haar distribution of `K` is `f`, then `f(x) = ∫_K f(xk⁻¹) dk`.
  Right invariance of the Haar integral on `K` (`subgroupIntegral_mul_right`)
  then gives `f(xk) = f(x)`. `fixes_normalizedIndicator` then shows that `e_K`
  fixes such `f`. The proof uses `ě_K = e_K` and the published
  `HeckeAlgebra.mul_normalizedIndicator_of_rightInvariant`.
- `fixes_of_rightConvolveTest`: suppose the source's hypotheses hold, namely the
  published scalar convolution `rightConvolveTest f (e μ) = f` and the inverted
  distribution of `e μ` equals `e μ`. Then `Fixes μ e f`. Indeed,
  `rightConvolveTest f (e μ)(x)` evaluates the inverted distribution at a left
  translate of `f`. Replacing it by `e μ` gives `∫ f(xy) e(y) dμ(y)`, which is
  `(f * ě)(x)` by `convolution_inversion_apply`. The inversion hypothesis is
  essential here on nonunimodular groups.

## The forward map: Hecke coordinates

For `T` right essentially compact, `coord μ T h` is the Hecke element whose
density is `T*h`. It is chosen by `exists_heckeDistribution_eq` and is unique by
`heckeDistribution_injective` (`coord_spec`, `coord_eq`). Injectivity gives:

- `coord_mul`: `coord T (h*k) = coord T h * k`, from `(T*h)*k = T*(h*k)` and
  `rightHeckeConvolution_heckeDistribution`;
- `coord_add` and `coord_smul`, from linearity of `T ↦ T*h`.

`family μ T` is the family `e ↦ coord T e` over all Hecke idempotents. By
`coord_mul` it lies in the published carrier: `coord T e * e = coord T (e*e)`
equals `coord T e`, and for `e ≤ f` we have
`coord T f * e = coord T (f*e) = coord T e`. This is the source's map
`T ↦ (e ↦ T*e)`.

## The inverse map

Let `a` be a compatible family. If `e ≤ g` and `e` fixes `f`, then
`(a_e μ)(f) = (a_g μ)(f)` (`heckeDistribution_val_of_fixes`). Indeed,
`a_e = a_g * e`, so `a_e μ = (a_g μ)*e`, and this is evaluated at a test fixed by
`e`. A common upper bound then shows that `(a_e μ)(f)` does not depend on the
idempotent `e` fixing `f` (`heckeDistribution_val_eq_of_fixes`). This is the
source's claim that the definition does not depend on the choice of `e`.

`invDist μ a` is the distribution `f ↦ (a_e μ)(f)` for a chosen `e` fixing `f`;
its value function is `invDistFun`. Additivity and homogeneity use a common
fixing idempotent and the choice independence. `invDist_apply_of_fixes` gives
the value for every fixing idempotent.

`rightHeckeConvolution_invDist`: if `e*h = h`, then `invDist a * h = (a_e*h) μ`.
Here `e` fixes `f * ȟ`, because `(f * ȟ) * ě = f * (e*h)ˇ`. Then
`invDist a (f * ȟ) = (a_e μ)(f * ȟ) = ((a_e μ)*h)(f)`. This is the source's
computation `A*h = ā(e)*h`. Hence `invDist a` is right essentially compact
(`invDist_mem`), with coordinates `a_e` (`coord_invDist`, using `a_e * e = a_e`).

## The additive equivalence

`comparison μ` has forward map `family` and inverse `a ↦ invDist a`. It is
additive by `coord_add`. The coordinate of `invDist a` is `a` by
`coord_invDist`. For `T` and a test `f` fixed by `e`,
`invDist (family T)(f) = ((coord T e) μ)(f) = (T*e)(f) = T(f)`.
`comparison_smul` records coordinatewise complex scalar compatibility.

## The product

`productFun μ T U` transports the published product of compatible families:

    productFun T U = comparison.symm (product hA (comparison T) (comparison U)).

It is additive in each variable by the published `add_product` and
`product_add`. It is homogeneous in each variable by `product_val` with a left
unit of the relevant coordinate, together with `comparison_smul`.
`essentialProduct μ` is the resulting bilinear map built with `LinearMap.mk₂`,
and `comparison_essentialProduct` restates its definition.

`coord_essentialProduct` shows `coord (T·U) h = coord T (coord U h)`. Choose
`e₀` with `e₀*h = h` and `f` with `f * coord U e₀ = coord U e₀`. Then
`product_val` gives that the `e₀`-coordinate of `T·U` is
`coord T f * coord U e₀`. Repeated use of `coord_mul` finishes the proof.
Consequently `(T·U)*h = T*(coord U h)` (`rightHeckeConvolution_essentialProduct`),
which is the source's identity `(T₁*T₂)*h = T₁*(T₂*h)`.

`diracElement` and `heckeElement h` are `δ₁` and `h μ` as right essentially
compact elements. Their coordinates are `h ↦ h` and `k ↦ h*k`, so `comparison`
sends them to the published `unit` and `canonical h`.

## The specifications

`essentialProduct_algebraLaws` proves the four clauses of
`RenardEssentialProducts.AlgebraLaws`:

1. associativity, transported from the published `product_assoc`;
2. `δ₁` is a two-sided unit, transported from `unit_product` and `product_unit`;
3. on compactly supported `T` and `U`, the product is the published compact
   convolution. Both sides are compared after acting by each idempotent `e`.
   Then `(t·u)*e = T*(coord u e)`. With `rightHeckeConvolution_compact`, this is
   `T ∗ (U ∗ e μ)` in compact convolution, and the published
   `convolution_associative` turns it into `(T ∗ U)*e`;
4. for a Hecke density `h μ`, the product `T·(h μ)` is `T*h`, by
   `coord_heckeElement` and `rightHeckeConvolution_mul`. The product `(h μ)·T` is
   `h*T`. Both have action `(h * coord T e) μ` at every idempotent `e`, by
   `rightHeckeConvolution_heckeDistribution`, `leftHecke_rightHecke_comm`,
   `coord_spec` and `leftHeckeConvolution_heckeDistribution`.

`essentialProduct_rightSpecification` adds the two remaining clauses of
`RightProductSpecification`.

- The evaluation formula: if `f` is fixed by right convolution with the Haar
  distribution of `K`, then `e_K` fixes `f`. With `h = coord U e_K`, we get
  `(T·U)(f) = ((T·U)*e_K)(f) = (T*h)(f)`. This is the source's definition
  `⟨T₁*T₂, f⟩ = ⟨T₁*(T₂*e_K), f⟩`, now a property of the transported product.
- The action formula: `(T·U)*h = T*k` with `k = coord U h`.

`comparison_specification` proves the six clauses of `ComparisonSpecification`:
the coordinate formula is `coord_spec`; scalar compatibility is `coord_smul`;
product preservation is `comparison_essentialProduct`; the Dirac and Hecke
clauses are `comparison_diracElement` and `comparison_heckeElement`; the inverse
formula combines `fixes_of_rightConvolveTest` with `invDist_apply_of_fixes`.

`eq_comparison` proves uniqueness from the first clause alone. If
`((E T)_e) μ = T*e` for all `T` and `e`, then `heckeDistribution_injective`
identifies `(E T)_e` with `coord T e`. This is the faithfulness argument named
in the statement Markdown.

## Relation to the source

The source defines the product by the evaluation formula and the comparison
by its two mutually inverse maps. Here the inverse map and the coordinate map
follow the source. The product is instead transported along the comparison
from the published product of compatible families, and the source's
evaluation formula is then proved as a property. Idempotents fixing a test are
taken in the left-Haar sense `f * ě = f`. The source's inversion-symmetric
choices are a special case (`fixes_of_rightConvolveTest`), so the published
inverse formula holds for exactly the idempotents the statement names. All
other names are internal helper definitions and lemmas of this proof.
