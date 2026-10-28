# Scalar and intrinsic weighted rational quotient comparison

Worker 56 constructs this specialization of the published comparison with
additional equations. The general maps and their proved inverse identities
are imported from `GeneralizedAffinoid.RelativeEquationComparison`, authored
by Worker 812. The intrinsic quotient and coefficient transport are reused
by their published Lean names.

## Inputs and concrete quotients

Fix a complete ultrametric normed field `K`, an actual
`A : PresentedAffinoidAlgebra K`, a natural number `m`, and arbitrary
positive real radii `s : PositivePolyradius (Fin m)`. Write
`r = A.polyradius`, `I = A.ideal` and `q_A = presentationMap K A`.
Supply representatives `g` and `f j` in `GeneralizedTateAlgebra r K`.
Their classes are `ḡ = q_A g` and `f̄_j = q_A (f j)`.
All new declarations are in
`Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation`.

The source of `relativeEquiv` is the published scalar presentation
`algebra K A s g f`, whose actual carrier and quotient norm are those of

\[
 B_{\mathrm{sc}}
 =K\{r^{-1}T,s^{-1}Y\}/
   \overline{\langle i(I)\cup\{i(g)Y_j-i(f_j):j\in\operatorname{Fin}m\}\rangle},
\]

where `i = appendLeft r s K`. The target is the published
`RelativeRationalPresentation.Algebra K A s ḡ f̄`, namely

\[
 B_{\mathrm{rel}}
 =A\{s^{-1}Y\}/
   \overline{\langle C(\bar g)Y_j-C(\bar f_j):j\in\operatorname{Fin}m\rangle},
\]

where `C = constantAlgHom s K A`. Both are concrete closed-ideal
quotients of the actual weighted restricted series algebras.

## Equality of equations and quotient relabelling

`relativeSeriesEvaluation_equation` computes the published scalar
evaluation `Adjoin.relativeSeriesEvaluation K A s` on each scalar rational
generator. Evaluation preserves subtraction and multiplication, sends
`i(h)` to `C(q_A h)`, and sends the new scalar coordinate indexed by
`Fin.natAdd A.arity j` to the relative coordinate `X s A j`. Consequently,
the result is exactly `C(ḡ) X_j - C(f̄_j)`.

`relativeEquationRelations_eq` proves equality of the entire relation
sets, rather than just containment of their generated closed ideals:

\[
 \operatorname{relativeSeriesEvaluation}
      \bigl(\{i(g)Y_j-i(f_j):j\}\bigr)
   =\{C(\bar g)Y_j-C(\bar f_j):j\}.
\]

Each direction unpacks a member of the displayed range and applies the
generator computation. `mapsRelations_to_intrinsic` and
`mapsRelations_from_intrinsic` rewrite along this equality and use
`RelativeRelations.mapsRelations_id`. Their compatibility hypotheses
are thus proved for the identity coefficient map.

`relativeEquationEquiv` applies `RelativeRelations.transportEquiv` with
`BoundedAlgEquiv.refl K A` and these two proofs. It identifies the generic
relative quotient by evaluated scalar equations with the intrinsic
rational quotient. The forward and inverse
`relativeEquationEquiv_quotientMap` formulas fix every relative-series
representative. `norm_relativeEquationEquiv` applies the generic
norm-preservation theorem to the identity on `A`, so the relabelling
preserves the actual quotient norms.

## The bounded equivalence and its computations

`relativeEquiv` packages the published `Adjoin.relativeEquationMap` and
`Adjoin.relativeEquationInverse` with `BoundedAlgEquiv.ofHomInv`. The
required inverse identities are the already proved
`relativeEquationInverse_map` and `relativeEquationMap_inverse`.
It then composes this equivalence with `relativeEquationEquiv`.
No inverse or desired equivalence is supplied as an input.

`relativeEquiv_presentationMap` computes the forward map on an arbitrary
scalar series `h`:

\[
 e(q_{B_{\mathrm{sc}}}(h))
   =q_{B_{\mathrm{rel}}}(\operatorname{relativeSeriesEvaluation}(h)).
\]

`relativeEquiv_symm_quotientMap` computes the inverse on any relative
series representative `h` as
`Adjoin.relativeEquationInverseEvaluation K A s (equations K A s g f) h`.
This is the published convergent evaluation in the scalar quotient, using
its coefficient map and new coordinate tuple. It is a concrete bounded
evaluation, including for a zero quotient.

`relativeEquiv_baseMap` and `relativeEquiv_fraction` state

\[
 e(\operatorname{baseMap}_{\mathrm{sc}}(a))
   =\operatorname{baseMap}_{\mathrm{rel}}(a),\qquad
 e(\operatorname{fraction}_{\mathrm{sc},j})
   =\operatorname{fraction}_{\mathrm{rel},j}.
\]

They specialize the generic additional-equation comparison formulas and
the quotient relabelling formula. The two corresponding
`relativeEquiv_symm_baseMap` and `relativeEquiv_symm_fraction` identities
follow by applying the inverse identity.

`norm_relativeEquiv` combines `norm_relativeEquationEquiv` with the
published exact norm equality for `Adjoin.relativeEquationMap`.
`norm_relativeEquiv_symm` applies this equality to the inverse image and
uses `e(e.symm a) = a`. Thus both actual quotient norms are preserved
exactly. `isometry_relativeEquiv` follows by the norm criterion for an
additive homomorphism.

`hom_ext` transfers the intrinsic quotient's coefficient/fraction
extensionality to the scalar rational presentation. Its target is any
normed commutative `K`-algebra in an independent universe, with no
completeness or ultrametric condition on that target. Compose the two
bounded maps with `e.symm`, use the inverse coefficient and fraction
formulas to apply intrinsic extensionality, and evaluate the resulting
map equality at `e(a)`. The inverse identity gives the desired equality
on every scalar quotient element.

## Loci and spectra

`locus_eq_relativeLocus` records the definitional equality of the scalar
and intrinsic subsets of `BanachSpectrum A`: both say
`x(f̄_j) ≤ s_j * x(ḡ)` for every `j`. This equality itself needs no
completeness of `K`.

`relativeSpectrumHomeomorph` is the actual contravariant homeomorphism
provided by the bounded algebra equivalence:

\[
 \mathcal M(B_{\mathrm{rel}})\ \simeq\ \mathcal M(B_{\mathrm{sc}}).
\]

Its forward evaluation formula is `x ↦ x ∘ e`; the inverse evaluation
formula is `x ↦ x ∘ e.symm`. These are the two
`relativeSpectrumHomeomorph_apply` formulas. Continuity and the inverse
identities come from `BoundedAlgEquiv.spectrumHomeomorph`.

`relativeSpectrumHomeomorph_naturality` is an equality of continuous maps
to `BanachSpectrum A`: the scalar structural spectrum map after this
homeomorphism equals the intrinsic structural spectrum map. Its proof
evaluates at each coefficient `a : A` and applies
`relativeEquiv_baseMap`. Combined with equality of loci, this identifies
the two already constructed forward structural images in the same
rational inequality set.

## Provenance and scope

The retained original is Vladimir Berkovich, *Non-Archimedean analytic
spaces*, Trieste lectures (2009), registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Printed/PDF pages 8–9 were read directly for this specialization.
Definition 2.1.6(i), page 8, gives the relative weighted-series algebra;
Definition 2.1.11 there gives the bounded-map dual category;
Exercise 2.2.2(ii), page 9, gives the rational equations and inequalities.
The exact isometric comparison between these two presentations is internal
derived infrastructure, proved from the published general
additional-equation comparison and identity coefficient transport. It is
not a numbered statement of the original.

Completeness of `K` is used through the general comparison, whose reverse
map uses convergent relative coefficient evaluation. No unit-ideal,
nonzero-quotient, proper-ideal, nonempty-variable-block, nontrivial-valuation,
or value-group condition on the positive radii is imposed.
Both arities may be zero.

This module compares the rational quotient attached to the supplied
scalar representatives with the intrinsic quotient for their actual
classes in the same coefficient algebra `A`. It does not yet package
representative independence or comparison across different coefficient
presentations, or assert denominator invertibility, surjectivity of the
structural spectrum map onto the inequality locus, analytic-domain
representability, sheaves, sites, or the Harris tower.
