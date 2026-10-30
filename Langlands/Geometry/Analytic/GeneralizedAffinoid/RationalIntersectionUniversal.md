# Bounded pushout property of positive-polyradius rational intersections: proof

Author: Worker 965.

`Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation.RationalIntersection.boundedPushout`
proves the published proposition `BoundedPushoutStatement.{u, v}` from module
`Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalIntersectionUniversal.Statement`,
with the coefficient universe `u` and target universe `v` independent. All
declarations below lie in the namespace
`Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation.RationalIntersection`.
The module adds no hypotheses: the target \(E\) may be the zero ring, need not
satisfy \(\|1\|=1\), and the tuple lengths may be zero.

## Notation

Fix the statement's data \(K, A, m, n, s, t, g, h, f, k\) and write
\(B=\)`algebra K A s g f`, \(C=\)`algebra K A t h k` and
\(D=\)`Algebra K A s t g h f k`, the published all-products quotient with
denominator \(gh\), numerators `numerators K A g h f k` and radii
`productRadii s t`. Product indices `a : Fin ((m + 1) * (n + 1))` are decoded
by `finProdFinEquiv.symm a = (a.1, a.2)`, exactly as in `productRadii` and
`numerators`. Write \(S=(1,s_0,\ldots)\), \(T=(1,t_0,\ldots)\),
\(F=(g,f_0,\ldots)\), \(H=(h,k_0,\ldots)\), and a bar for `presentationMap K A`.

## Structural clauses

Clauses 1 and 2 of the statement are discharged verbatim by the imported
theorems `leftMap_comp_baseMap` and `rightMap_comp_baseMap` of the published
`GeneralizedAffinoid.RationalIntersection` module.

## Radii and monomial helpers

- `leftFactorRadii s n` and `rightFactorRadii m t` are positive polyradii on the
  product index with radii \(S_{a.1}\) and \(T_{a.2}\). `weight_productRadii`
  proves that the product-radius weight of every exponent \(d\) is the product of
  the two factor weights, from \(\prod_a (S_{a.1}T_{a.2})^{d_a}=
  \prod_a S_{a.1}^{d_a}\prod_a T_{a.2}^{d_a}\) (`Finsupp.prod_mul`, `mul_pow`).
- `monomialValue_mul` states that the monomial of a pointwise product of two
  tuples is the product of the two monomials. `map_monomialValue` states that a
  \(K\)-algebra map commutes with monomial evaluation.

## Extended fractions

`leftExtendedFraction` is \(Y=(1,Y_0,\ldots,Y_{m-1})\) in \(B\), where the
\(Y_i=\)`fraction K A s g f i` are the published fraction coordinates;
`rightExtendedFraction` is \(W=(1,W_0,\ldots)\) in \(C\). Their norm bounds
`norm_leftExtendedFraction_le` and `norm_rightExtendedFraction_le` give
\(\|Y_i\|\le S_i\) and \(\|W_j\|\le T_j\): in position zero this is the imported
`PresentedAffinoidAlgebra.norm_one_le` (\(\|1\|\le 1\), allowing a zero
quotient), elsewhere the published `norm_fraction_le`.
`leftExtendedFraction_equation` and `rightExtendedFraction_equation` give
\(\operatorname{base}_B(\bar g)\,Y_i=\operatorname{base}_B(\bar F_i)\) and the
analogue for \(C\): in position zero both sides are \(\operatorname{base}(\bar g)\),
elsewhere this is the published `fraction_equation`.

## The tuple and its bound

Let \(\alpha:B\to E\) and \(\beta:C\to E\) be bounded \(K\)-algebra maps.
`pairTuple` is the tuple \(b_a=\alpha(Y_{a.1})\,\beta(W_{a.2})\) in \(E\).

`pairTuple_bounded` proves `HasBoundedMonomials (productRadii s t) E b`, that is
a constant \(c>0\) with \(\|b^d\|\le c\cdot\)`(productRadii s t).weight d` for
every \(d\). Let \(c_\alpha,c_\beta>0\) be the boundedness constants of
\(\alpha,\beta\) (`BoundedAlgHom.bounded`). By `map_monomialValue` and
`monomialValue_mul`,
\[
 b^d=\alpha\big(Y'^{\,d}\big)\,\beta\big(W'^{\,d}\big),\qquad
 Y'_a=Y_{a.1},\ W'_a=W_{a.2}.
\]
The imported `monomialValue_norm_le_weight` (coordinate bounds and
\(\|1\|\le1\) imply the weighted monomial bound) applied to \(Y'\) with
`leftFactorRadii s n`, and to \(W'\) with `rightFactorRadii m t`, bounds the two
monomials by the factor weights. Submultiplicativity in \(E\), the bounds
\(\|\alpha(x)\|\le c_\alpha\|x\|\), \(\|\beta(y)\|\le c_\beta\|y\|\) and
`weight_productRadii` give the constant \(c=c_\alpha c_\beta\). No row-sum
regrouping of exponents is needed.

`pairTuple_equation` assumes the agreement hypothesis
\(\alpha\circ\operatorname{base}_B=\beta\circ\operatorname{base}_C\) (`hcompat`)
and proves, with \(\varphi=\alpha\circ\operatorname{base}_B\),
\[
 \varphi(\overline{gh})\,b_a=\varphi\big(\overline{F_{a.1}H_{a.2}}\big)
\]
for every product index \(a\). Both sides are expanded multiplicatively. The
agreement hypothesis rewrites \(\alpha(\operatorname{base}_B(\bar h))\) and
\(\alpha(\operatorname{base}_B(\bar H_{a.2}))\) as the corresponding values of
\(\beta\). The extended fraction equations, transported by \(\alpha\) and
\(\beta\), then turn the right side into the left, and `ring` closes the
commutative rearrangement.

## The lift and its properties

Assume further that \(E\) is ultrametric and complete. `pushoutLift hcompat` is
the published `RationalPresentation.liftFromBase` for \(D\), applied to the base
map \(\varphi\), the tuple \(b\), `pairTuple_bounded` and `pairTuple_equation`.
`pushoutLift_comp_base` is `liftFromBase_comp_baseMap`: the lift composed with
`base K A s t g h f k` is \(\varphi\).

Now assume `[CompleteSpace K]` and the generation hypotheses `hf`, `hk`.

- `pushoutLift_comp_leftMap`: the lift composed with `leftMap` is \(\alpha\).
  By the published `hom_ext_base` for \(B\) (which uses `hf`), it suffices to
  compare after composing with \(\operatorname{base}_B\). The imported
  `leftMap_base` turns the left side into the lift applied to `base`, which is
  \(\varphi\) by `pushoutLift_comp_base`.
- `pushoutLift_comp_rightMap`: the same argument for \(C\), using `hk`,
  `rightMap_base`, and finally `hcompat` to replace
  \(\alpha\circ\operatorname{base}_B\) by \(\beta\circ\operatorname{base}_C\).
- `existsUnique_pushoutLift`: the lift is the unique bounded map with both
  factorizations. Existence is the two preceding theorems. For uniqueness let
  \(\theta\) satisfy \(\theta\circ\)`leftMap`\(=\alpha\). Apply `hom_ext_base`
  for \(D\) with the published `generatesUnitIdeal K A g h f k hf hk` (the
  product tuple generates the unit ideal). For \(x\in A\), `leftMap_base` gives
  \(\theta(\operatorname{base}(x))=
  \theta(\text{leftMap}(\operatorname{base}_B(x)))=\alpha(\operatorname{base}_B(x))\),
  and `pushoutLift_comp_base` identifies this value with the lift at
  \(\operatorname{base}(x)\). Only the left factorization of \(\theta\) is used.

`boundedPushout` introduces the statement's data, supplies clauses 1 and 2 as
above, and for clause 3 returns `existsUnique_pushoutLift hf hk hcompat`.

## Scope

The proof constructs \(\theta\) from \(\alpha\) and \(\beta\) alone, with no
operator-norm bound recorded for \(\theta\). It uses only the published rational
extension machinery (`liftFromBase`, `liftFromBase_comp_baseMap`,
`hom_ext_base`) and the published intersection maps. It does not address the
spectral-image factorization property of Berkovich's Definition 2.2.1, which the
statement's Markdown distinguishes from this pushout property.
