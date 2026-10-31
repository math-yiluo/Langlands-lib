# Weighted rational quotients under coefficient presentation equivalences

This module constructs a comparison of the scalar rational quotients for
two actual coefficient presentations and a supplied bounded algebra
equivalence between their coefficient algebras. Their arities, radii and
closed ideals may differ. The new coordinate block and its arbitrary
positive real radii are the same. The declarations are in
`Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation`.

Work over a complete ultrametric normed field `K`. Supply scalar denominator
and numerator representatives `g,f` for `A` and `g',f'` for `B`, and
`e : BoundedAlgEquiv K A B`, with
`e(q_A(g)) = q_B(g')` and `e(q_A(f(j))) = q_B(f'(j))` for every new
coordinate `j`. The equivalence and equalities are actual input; arbitrary
coefficient presentations are not asserted equivalent.

Write `Q_A = algebra K A s g f` and `Q_B = algebra K B s g' f'`.
These are the actual scalar weighted-series quotients by the closure of the
old coefficient relations together with `g Y_j - f_j`, with the old series
inserted into the enlarged coordinate block. Write
`R_A = RelativeRationalPresentation.Algebra K A s (q_A(g)) (q_A ∘ f)`
and similarly for `R_B`. These intrinsic quotients use relative weighted
series over the actual coefficient algebras and equations
`C(q_A(g)) X_j - C(q_A(f(j)))`. All these constructions are imported from
the published modules by their Lean names.

`presentationEquiv` composes the published scalar-to-intrinsic comparison,
intrinsic coefficient equivalence, identity identification along the matching
data equalities, and inverse scalar-to-intrinsic comparison for `B`. The
identity identification and its formulas are proved by equality
induction. All maps act on the concrete closed-ideal quotient algebras with
their actual quotient norms. The displayed inverse maps come from the
proved inverse identities of the constituent equivalences.

More explicitly, if `α_A : Q_A ≃ R_A` and `α_B : Q_B ≃ R_B` are
`relativeEquiv` and `E` is `RelativeRationalPresentation.coefficientEquiv`
for `e`, the constructed map is `α_B.symm ∘ δ ∘ E ∘ α_A`. Here `δ`
identifies the intrinsic quotient for data `e(q_A(g)),e(q_A(f(j)))`
with `R_B`. The public `dataEquiv` implements `δ`; its public coefficient and fraction
formulas are reused by `RationalLocalization/RelativeComparison`. Equality
induction also proves its private quotient-projection formula and exact norm
preservation in both directions. It assumes no quotient map
or inverse law as additional input.

`relativeEquiv_presentationEquiv` states this comparison formula after
applying the target scalar-to-intrinsic comparison. The four coefficient and
fraction formulas send a coefficient `a` to `e(a)`, send it back by
`e.symm`, and preserve each fraction coordinate label in both directions.
The proofs use the corresponding published formulas and the inverse
identities.

`relativeEquiv_presentationEquiv_presentationMap` computes every scalar
representative `h` of `Q_A` after applying the comparison and `α_B`:

```text
α_B(presentationEquiv(q_Q_A(h))) =
  quotientMap_B(mapCoefficientsAlgHom s e.toBoundedAlgHom
    (Adjoin.relativeSeriesEvaluation K A s h)).
```

Thus the source scalar series is evaluated as relative series over `A`,
its coefficients are mapped through the actual `e`, and it is projected
to `R_B`. The proof rewrites by the corresponding published representative
formulas and the equality-induced projection formula. This theorem is a
formula in the intrinsic target; it does not choose scalar representatives
in `B` for all mapped coefficients.

`eq_presentationEquiv` characterizes the forward map among all
`BoundedAlgHom K Q_A Q_B`: any such map with the displayed coefficient and
fraction values equals `presentationEquiv.toBoundedAlgHom`. Its proof
applies the scalar rational quotient's published `hom_ext` to these two
families of values. No density or uniqueness property is assumed.

The two estimates `norm_presentationEquiv_le` and
`norm_presentationEquiv_symm_le` preserve the supplied coefficient bounds
without enlarging their constants. For each real `c ≥ 0`, they give

```text
(∀ a : A, ‖e(a)‖ ≤ c * ‖a‖)
  → ∀ x : Q_A, ‖presentationEquiv(x)‖ ≤ c * ‖x‖,
(∀ b : B, ‖e.symm(b)‖ ≤ c * ‖b‖)
  → ∀ y : Q_B, ‖presentationEquiv.symm(y)‖ ≤ c * ‖y‖.
```

The two constants and hypotheses are independent, and `c = 0` is allowed.
The forward proof moves to the intrinsic target by exact norm
preservation, removes `δ`, and applies the published intrinsic coefficient
estimate. The inverse proof unfolds the composite inverse, uses the
published inverse coefficient estimate, and removes the two other
isometric factors. Both estimates concern the actual quotient norms.

Under `∀ a : A, ‖e(a)‖ = ‖a‖`, `norm_presentationEquiv` proves exact
norm equality for every source quotient element. It combines the exact
norm equalities of the constituent maps. `norm_presentationEquiv_symm`
applies this equality to an inverse image and uses the forward-inverse
identity. `isometry_presentationEquiv` then uses the additive
norm-preservation criterion. Isometry is conditional on the stated
coefficient hypothesis.

`presentationEquiv_eq_representativeEquiv` checks the fixed-coefficient
specialization. For the identity bounded equivalence of `A` and matching
classes of two choices of scalar representatives, the two underlying
bounded maps of `presentationEquiv` and the published
`representativeEquiv` are equal. The proof uses `hom_ext` and their
coefficient and fraction formulas. This reuses the earlier representative
comparison and checks agreement with it.

`presentationSpectrumHomeomorph` is the genuine contravariant
homeomorphism `BanachSpectrum Q_B ≃ₜ BanachSpectrum Q_A` obtained from
the constructed bounded algebra equivalence. The spectrum has its actual
topology defined by evaluation of multiplicative seminorms. Its two
evaluation lemmas are

```text
presentationSpectrumHomeomorph(x)(a) = x(presentationEquiv(a)),
presentationSpectrumHomeomorph.symm(x)(b) =
  x(presentationEquiv.symm(b)).
```

`presentationSpectrumHomeomorph_naturality` is equality of continuous maps
from `BanachSpectrum Q_B` to `BanachSpectrum A`. One path first applies
this homeomorphism and then the structural `spectrumMap` for `Q_A`;
the other applies the structural map for `Q_B` and then
`e.spectrumHomeomorph`. Continuous-map and spectrum extensionality reduce
the equality to `presentationEquiv_baseMap`.

`presentationLocusHomeomorph` restricts `e.spectrumHomeomorph` to
`locus K B s g' f' ≃ₜ locus K A s g f`. The loci are the subspaces
defined by all inequalities
`x(q_A(f(j))) ≤ s(j) * x(q_A(g))`, and likewise for `B`. Rewriting by
`hg,hf` proves exactly the predicate equivalence needed for
`Homeomorph.subtype`, which supplies the actual inverse and continuity.
The forward evaluation is `x(e(a))`; the inverse evaluation is
`x(e.symm(b))`. These three locus declarations omit completeness of `K`;
the scalar quotient comparison uses completeness.

The source context is Berkovich, *Non-Archimedean analytic spaces*,
Trieste lectures (2009), registered as
`berkovich-2009-trieste-analytic-spaces`, retained PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Printed/PDF pages 8–9 were read directly: Definition 2.1.6(i) supplies
relative weighted series, Definition 2.1.11 bounded algebra morphisms and
the contravariant direction of spectra, and Exercise 2.2.2(ii) the rational
equations and inequalities. The comparison here is an internal derivation,
not a numbered result of the source. The source's analytic-domain
representability conclusion is outside this module's scope.

The finite coordinate block may be empty; the closed coefficient ideals
need not be proper; the quotients may be zero rings; the valuation need
not be nontrivial; and radii need not lie in a value group. No
unit-ideal condition on the rational data is used. Such hypotheses belong
to further domain and representability results, not the comparisons
proved here. This module does not prove invertibility of the denominator,
surjectivity of the structural map onto its inequality locus, rational
domain representability, atlases, analytic sheaves, or etale or equivariant
sites. Identity and composition laws for this scalar comparison are also
separate from the laws implemented here. This is one local algebra and
spectrum contribution to the larger analytic construction.
