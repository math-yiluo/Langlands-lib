# Intrinsic weighted rational quotients over actual coefficient elements

Worker 56 constructs the intrinsic relative model and its bounded evaluation.
The fraction equation, forward spectrum inequality and denominator-one
specialization adapt the arguments in `GeneralizedAffinoid/RationalPresentation`,
previously coauthored by Workers 56 and 36. Worker 36 is credited for that
adaptation. Published relative series, closed-ideal quotients and evaluation
are reused by their Lean names.

## Inputs and actual algebra

Fix an ultrametric normed field `K`, an actual
`A : PresentedAffinoidAlgebra K`, a natural number `m` and arbitrary positive
real radii `s : PositivePolyradius (Fin m)`. The numerator and denominator
inputs are actual elements `g : A` and `f : Fin m → A`. No representatives
in the scalar presentation of `A` are chosen.

All declarations are in
`Langlands.Analytic.PresentedAffinoidAlgebra.RelativeRationalPresentation`.
Write `C` for the bounded constant-series inclusion
`GeneralizedTateAlgebra.constantAlgHom s K A`. The set `equations` is
the range of `j ↦ C(g) X_j - C(f_j)`. `Algebra` abbreviates the actual
`RelativeRelations.QuotientAlgebra` for these equations:

\[
 B=A\{s^{-1}Y\}/
       \overline{\langle C(g)Y_j-C(f_j):j\in\operatorname{Fin}m\rangle}.
\]

The carrier, operations and quotient norm come from the published closed-ideal
quotient, rather than a record assuming a universal property. Inherited
instances make it an ultrametric normed commutative `K`-algebra, an `A`-algebra,
and a scalar tower over `K → A`. If `K` is complete, the imported quotient
completeness instance makes `B` complete.

`quotientMap` is the contractive quotient projection.
`quotientMap_surjective`, `quotientMap_eq_zero_iff` and
`norm_quotientMap_le` specialize the published surjectivity, exact closed
kernel and contraction laws. `exists_representative_norm_lt` states that
each element `a : B`, for each `ε > 0`, has a relative-series representative
of norm less than `‖a‖ + ε`. Thus the construction retains the actual quotient
norm. These are direct applications of `RelativeRelations`, not new
closedness results for arbitrary ideals.

`GeneratesUnitIdeal` records `Ideal.span (insert g (Set.range f)) = ⊤`.
The constructions and conclusions in this module do not require it.

## Structural map and fractions

`baseMap : A → B` is the bounded constant-series inclusion followed by the
quotient projection (`baseMap_apply`). It is definitionally the inherited
`A`-algebra map (`baseMap_eq_algebraMap`) and is contractive
(`norm_baseMap_le`). `fraction j` is the projected coordinate `Y_j`, with
`norm_fraction_le` asserting `‖fraction j‖ ≤ s j`.

`fraction_equation` is

\[
  \operatorname{baseMap}(g)\operatorname{fraction}_j
      =\operatorname{baseMap}(f_j).
\]

Its proof projects the corresponding equation and uses preservation of
subtraction and multiplication. Invertibility of `baseMap(g)` is not a
conclusion of this equation.

`hom_ext` says that bounded `K`-algebra maps out of `B` agreeing on every
coefficient and every fraction are equal. The target is any normed
commutative `K`-algebra in an independent universe; it need not be complete
or ultrametric. Compose both maps with the quotient projection and use the
published relative-series extensionality on coefficients and coordinates.
Quotient extensionality then gives equality.

## Constructed evaluation and uniqueness

For existence, let the target `D` be a complete ultrametric normed
commutative `K`-algebra. Supply a bounded coefficient map
`φ : BoundedAlgHom K A D` that is contractive, coordinates
`b : Fin m → D` satisfying

\[
  \left\|\prod_j b_j^{d_j}\right\|\le s^d
       \quad\text{for every }d:\operatorname{Fin}m\to_0\mathbb N,
  \qquad
  \varphi(g)b_j=\varphi(f_j).
\]

The monomial bound includes exponent zero and is supplied explicitly;
no norm-one instance or nonzero-target assumption is imposed.
`evaluateCoefficientsHom_equations` shows that the published actual
coefficient evaluation annihilates every rational equation. It rewrites
evaluation on constants and variables to the supplied relation.
`evaluate` applies the existing bounded closed-ideal descent to that map.
The map is constructed from the convergent coefficient sum and quotient
descent; no desired map or inverse is assumed.

`evaluate_quotientMap` computes the result on a representative `h` as
`GeneralizedTateAlgebra.evaluateCoefficients s φ b h`. This is the sum
of `φ(h_d)` times the coordinate monomials. `evaluate_baseMap` and
`evaluate_fraction` give exactly the supplied coefficient and coordinate
values. `norm_evaluate_le` proves that evaluation is contractive for the
actual quotient norm, by applying `RelativeRelations.norm_descend_le`
with constant one and the published coefficient-evaluation contraction.

`eq_evaluate` proves that any bounded map having these coefficient and
fraction values equals the constructed evaluation, using `hom_ext`.
`existsUnique_evaluate` packages existence and uniqueness among all such
bounded maps. The existence hypotheses are the explicit contraction and
weighted monomial bounds above. This does not assert a spectral-bound
universal property for arbitrary bounded coefficient maps.

## Forward spectrum map and Weierstrass specialization

`locus` is the subset of `BanachSpectrum A` defined by
`x(f_j) ≤ s_j x(g)` for every `j`. It is closed by continuity of evaluations
and intersection of closed inequalities (`isClosed_locus`) and compact by
compactness of the coefficient spectrum (`isCompact_locus`).

`spectrumMap` is the continuous pullback along `baseMap`, with
`spectrumMap_apply` recording `spectrumMap(x)(a) = x(baseMap(a))`.
`spectrumMap_mem_locus` uses the fraction equation, multiplicativity,
domination by the quotient norm and the coordinate bound. It neither
divides by the denominator nor assumes its value is nonzero.
`spectrumToLocus` bundles this forward map with its proved codomain.
No surjectivity, injectivity or homeomorphism onto the locus is asserted.

`WeierstrassAlgebra` is the denominator-one specialization.
`weierstrass_fraction` identifies each fraction with `baseMap(f_j)`.
`weierstrassLocus` is defined by `x(f_j) ≤ s_j`, and `locus_one` identifies
it with the denominator-one rational locus by the value of a spectrum
point at one.

## Provenance and scope

The retained original is Vladimir Berkovich, *Non-Archimedean analytic
spaces*, Trieste lectures (2009), registered as
`berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Printed/PDF pages 7–9 were read directly. Section 2.1 on page 7 supplies
the quotient-norm convention. Definition 2.1.6(i)–(ii), page 8, supplies
relative weighted restricted series and relative affinoid presentations.
Exercise 2.2.2(i)–(ii), page 9, supplies the relative rational and
Weierstrass equations and their expected loci.

The source states analytic-domain conclusions over a complete
nonarchimedean field, with the indicated nonvanishing hypothesis in the
rational case. Here the closed quotient, its intrinsic bounded evaluation
and its forward spectral inequalities are derived from the published
actual relative-series and quotient interfaces. The construction and
uniqueness allow incomplete `K`; evaluation assumes completeness of the
target. No analytic-domain theorem is inferred from those weaker
hypotheses.

Empty variable blocks, zero coefficient or target quotients, nonproper
relation ideals, arbitrary positive radii and trivial valuations are
retained. The intrinsic model uses actual coefficient elements, but the
module does not compare distinct scalar presentations of `A`, construct a
new scalar `PresentedAffinoidAlgebra K` presentation of `B`, or identify
`B` with the existing scalar rational model. Those comparison obligations,
denominator invertibility, reverse spectrum inclusion, full analytic-domain
representability, sheaves and sites remain separate.
