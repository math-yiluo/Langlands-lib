# Bounded universal property of the rational intersection quotient: proof

Author: Worker 36 (Lean proof and original Markdown). Markdown revised by
Worker 297.

`RationalIntersection.boundedPushout` proves `BoundedPushoutStatement`
from `RationalIntersectionUniversal.Statement` for the product quotient
`RationalIntersection.algebra` of `RationalIntersection.Definitions`.
Let \(P\) be a presented strict affinoid algebra over a complete
ultrametric normed field \(K\), and suppose \((g;f_i)\) and \((h;k_j)\)
each generate the unit ideal. The proof supplies bounded restriction maps
from the two rational localization algebras to the product quotient,
with their base-composition equations. Then, for every complete
ultrametric normed commutative \(K\)-algebra \(B\) and bounded maps
\(\alpha,\beta\) out of the two localizations that agree on \(P\), it
constructs exactly one bounded map out of the product quotient restricting
to \(\alpha\) and \(\beta\). The target lives in an independent universe
`v`, need not satisfy `NormOneClass` and may be the zero ring. Empty
tuples, the zero base algebra and trivially valued fields are allowed;
no nontriviality instance is assumed.

## Imported results

The restriction maps are the published `RationalIntersection.leftMap`
and `RationalIntersection.rightMap`, with `leftMap_comp_baseMap`,
`rightMap_comp_baseMap` and `generatesUnitIdeal` (the product tuple
generates the unit ideal), all from module `RationalIntersection`.
From `RationalLocalization` the proof uses `liftFromBase` (convergent
Tate evaluation descended through the closed relation ideal),
`liftFromBase_comp_baseMap`, the extensionality theorem `hom_ext_base`,
the defining relations `coordinate_equation` and the coordinates
`fractionCoordinate`.

## Product fraction tuples

`bounded_cons_one` proves that adjoining the unit as a first coordinate
preserves bounded monomials. Its powers are bounded by
\(\max(1,\lVert1\rVert)\), so a normalized unit is not required.
`fractionProducts` multiplies the two tuples \((1,b_1,\dots,b_m)\) and
\((1,c_1,\dots,c_n)\) pairwise, indexed through `finProdFinEquiv` exactly
as `numerators` indexes the products of \((g,f_1,\dots,f_m)\) and
\((h,k_1,\dots,k_n)\). `fractionProducts_bounded` bounds the powers of
each product coordinate by the product of the two positive bounds and
converts through `hasBoundedMonomials_iff_pow_bound`.

Suppose a bounded map \(\phi:P\to B\) and tuples \(b_i,c_j\) satisfy
\(\phi(g)b_i=\phi(f_i)\) and \(\phi(h)c_j=\phi(k_j)\).
Write \(b'=(1,b)\), \(c'=(1,c)\), \(F=(g,f)\) and \(H=(h,k)\).
`fractionProducts_equations` checks the product presentation's relations
\(\phi(gh)\,b'_i c'_j=\phi(F_i H_j)\), first extending the two families of
equations to the coordinates indexed by zero, where they read
\(\phi(g)\cdot1=\phi(g)\) and \(\phi(h)\cdot1=\phi(h)\).
`liftFromSolutions` applies `RationalLocalization.liftFromBase` to the
product denominator \(gh\), the product tuple and these equations, and
`liftFromSolutions_comp_baseMap` records that its composition with the
intersection base map is \(\phi\). Neither uses a unit-ideal hypothesis.

## The lift

`mappedFractions_bounded` shows that a bounded map out of a rational
localization sends its fraction coordinates to a tuple with bounded
monomials: the coordinates are images of Tate variables, and
`hasBoundedMonomials_map_X` applies to the composition with the bounded
presentation map.

For bounded \(\alpha,\beta\) with
\(\alpha\circ\text{base}_f=\beta\circ\text{base}_k\) (`hcompat`), `lift`
applies `liftFromSolutions` to \(\phi=\alpha\circ\text{base}_f\),
\(b_i=\alpha(\text{frac}_i)\) and \(c_j=\beta(\text{frac}_j)\). The first
equations are \(\alpha\) applied to the defining relations of the left
localization. For the second, `hcompat` rewrites
\(\alpha(\text{base}_f(h))\) and \(\alpha(\text{base}_f(k_j))\) as the
corresponding values of \(\beta\), and the defining relations of the right
localization finish the equation. `lift_comp_baseMap` gives
\(\text{lift}\circ\text{base}=\alpha\circ\text{base}_f\).

`lift_comp_leftMap` proves \(\text{lift}\circ L=\alpha\) with `hom_ext_base`
for the left localization (using \(h_f\)): both sides agree after
composing with \(\text{base}_f\), by `leftMap_comp_baseMap` and
`lift_comp_baseMap`. `lift_comp_rightMap` is the same argument for the
right localization (using \(h_k\)), with `hcompat` as the final step.

## Uniqueness and the closing theorem

`existsUnique_lift` takes `lift` as the witness. For uniqueness, any
\(\psi\) with \(\psi L=\alpha\) and \(\psi R=\beta\) satisfies
\(\psi\circ\text{base}=\psi\circ L\circ\text{base}_f=\alpha\circ\text{base}_f
=\text{lift}\circ\text{base}\), so `hom_ext_base` for the product quotient,
with the unit ideal supplied by `generatesUnitIdeal`, gives
\(\psi=\text{lift}\).

`boundedPushout` introduces the data and the two unit-ideal hypotheses,
supplies `leftMap`, `rightMap` and their base-composition equations, and,
for each target \(B\), maps \(\alpha,\beta\) and `hcompat`, concludes
with `existsUnique_lift`.

## Scope and source context

The result is a bounded pushout property of the displayed constructed
algebras. It does not show that a bounded map out of \(P\) whose spectral
image lies in the intersection admits bounded solution tuples; no
implication from spectral bounds to power bounds is used or assumed.
Comparison with the image-containment universal property of
Definition 2.2.1, arbitrary radii and structure-sheaf descent are outside
this proof.

The source context is Berkovich, *Non-archimedean analytic spaces*
(Trieste lectures, 2009), Exercise 2.2.2(ii)-(iii), printed/PDF p.9:
rational quotient presentations and intersections of rational domains.
The registered source is `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`;
see the [author's PDF](https://www.wisdom.weizmann.ac.il/~vova/Trieste_2009.pdf).
The common-target formulation and the proof route above are internal
derivations from the concrete quotient and evaluation constructions,
not a proof quoted from the source.
