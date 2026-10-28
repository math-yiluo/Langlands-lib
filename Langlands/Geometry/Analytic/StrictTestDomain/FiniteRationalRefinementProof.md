# Finite standard rational refinement

Author: Worker 575.

`Langlands.Analytic.StrictTestDomain.finiteRationalRefinement` proves the
unapplied published proposition
`Langlands.Analytic.StrictTestDomain.FiniteRationalRefinementStatement.{u}`
for every universe `u`. The hypotheses and conclusion are exactly those of
the imported statement. In particular, the field is complete and ultrametric,
the base is the actual presented strict affinoid algebra, and the given finite
family covers its `BanachSpectrum` by the existing `RationalData.locus`.
The conclusion supplies a tuple without common spectrum zeros whose actual
`standardRational` loci each lie in one fixed member of the original family.
The imported statement and its dependencies are unchanged.

The construction and its supporting lemmas are private to this proof module.
For each datum `D i`, `extendedEntry` extends the numerator tuple by its
denominator, indexed by `Option (Fin (D i).arity)`: `none` selects the
denominator and `some j` selects numerator `j`. The finite dependent type
`RefinementChoice D` consists of functions selecting one extended entry at
each `i`, together with a proof that at least one selection is `none`.
`refinementProduct D φ` is the product of those selected algebra elements
over the original finite index type. Thus varying numerator arities require
no padding or common bound.

At a point in a rational locus, `denominator_pos` derives positivity of its
denominator directly from the datum's no-common-zero field: if the
denominator value were zero, the rational inequalities and nonnegativity
would force every numerator value to be zero. `extendedEntry_nonzero`
extracts a nonzero evaluated entry at every point from the same field.
`eval_refinementProduct` applies the multiplicative seminorm's finite-product
identity.

`refinementProduct_nonzero` proves that the products have no common spectrum
zero. Given a point, choose a member of the original cover containing it,
and select a nonzero extended entry in every datum. Replace the selection
in the chosen cover member by its denominator. That value is positive, so
every selected value remains nonzero. The updated selection is admissible,
and evaluation of its product is a product of nonzero real numbers.

For the containment lemma `refinementProduct_refines`, fix an admissible
selection `φ` and an index `i₀` at which it selects the denominator. Suppose
a point `x` maximizes the evaluated product of `φ` among all admissible
products. Some admissible product is nonzero by the preceding lemma, so the
maximal value is positive. Choose `i₁` with `x ∈ (D i₁).locus`. If
`i₁ = i₀`, the required containment already holds at this point.

Otherwise, for any numerator `j` of `D i₀`, form `ψ` by replacing the
`i₀` selection by `some j` and the `i₁` selection by `none`. The latter
replacement makes `ψ` admissible. Write `r` for the product of the evaluations
at all indices other than `i₀` and `i₁`. The private finite-product identity
`prod_two` factors both products, using two erased indices. With
`b₀ = x ((D i₀).denominator)`, `b₁ = x ((D i₁).denominator)`,
`a = x ((D i₀).numerator j)`, and `v` the value of the original selection
at `i₁`, maximality gives

```text
a * b₁ * r ≤ b₀ * v * r.
```

The common factor `r` is nonnegative, and it cannot be zero because the
original product is positive. Cancel `r`. Membership in `(D i₁).locus`
implies `v ≤ b₁`, including when that selection was itself the denominator.
Since `b₀ ≥ 0`, it follows that `a * b₁ ≤ b₀ * b₁`. Finally `b₁ > 0`
by `denominator_pos`, so cancellation gives `a ≤ b₀`. This holds for every
numerator `j`, proving membership in the existing locus of `D i₀`.
The containing index `i₀` was chosen from `φ` before considering the point.

The final theorem installs finite enumerations from the given `Finite I`
instance, enumerates the admissible choice type by `Fin n`, and takes `f`
to be the corresponding product tuple. It transports the product
nonvanishing and containment lemmas across this equivalence.
`mem_standardRational_locus` is the definitional maximality condition used
in the final step. The published `standardRational_covers` then also shows
that these refining loci cover the whole spectrum.

Empty index types and empty spectra require no special assumptions or
branches. When `I` is empty, no selection is admissible, so `n = 0`; the
point-cover hypothesis rules out spectrum points, and both output obligations
are vacuous. When the spectrum is empty with nonempty `I`, the construction
may produce a nonempty tuple, and all of its locus inclusions and its
no-common-zero condition hold vacuously. Zero bases are therefore permitted.
Empty numerator tuples are handled by their `Option (Fin 0)` extended entry,
and the containment goal then has no numerator inequalities. Empty loci,
repetitions, and nonreduced bases are also allowed.

The source is Piotr Achinger, *Introduction to non-Archimedean Geometry*
(November 22, 2020), Definition 7.2.1 and the rational-cover part of
Lemma 7.2.2, printed/PDF pp.65–66; the scalar-field convention is on p.6.
The retained original is registered as
`achinger-2020-non-archimedean-geometry-nov22`, SHA256
`666cc6a90efbfc05f5fa0156044a259beaabdf989c45b633542e1cd2cdc0ec95`.
The implemented dependent choices accommodate varying arities in place of
the source's common numerator bound. The source's occurrence of
`x ∈ U_φ` in the second claim refers to its refining locus `V_φ`.
The restriction to choices containing a denominator is essential to its
assignment of a containing original locus.

Achinger works with the maximal spectrum and nontrivially valued scalars.
The extension here to Banach-spectrum points and trivially valued scalars is
derived from the implemented argument: it uses only nonnegative
multiplicative evaluations, the point-cover and no-common-zero hypotheses,
finite products, and cancellation of positive real numbers. It uses neither
a small nonzero scalar nor reducedness or an integral-domain assumption on
the base, and the proof itself does not use completeness. Berkovich,
*Non-Archimedean analytic spaces* (Trieste lectures, 2009), Exercise
2.2.2(ii)–(iii), printed/PDF p.9, supplies the rational-domain context with
no common spectrum zeros. That original is registered as
`berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Both retained originals and their hashes were checked; no registered
Achinger or Trieste erratum was found in current Library notes on
2026-10-28.

This theorem proves finite geometric refinement. It provides no analytic
gluing, acyclicity, scalar descent, relative descent or whole-spectrum
assembly; those remain separate obligations. Gerritzen–Grauert is
unnecessary because the given cover members are already rational.
