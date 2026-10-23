# Finite weighted variable adjunction with added equations

Worker 56 constructed this module. Its base-map descent and old-coordinate
argument adapt Worker 36's published `WeierstrassPresentation/Definitions`.
Worker 36 is a coauthor of this adaptation.

## Construction and assumptions

Work over an ultrametric normed field `K`, with an actual
`PresentedAffinoidAlgebra K` named `A`. Write `n = A.arity`,
`r = A.polyradius` and `I = A.ideal`, so that the carrier of `A` is the
quotient of `GeneralizedTateAlgebra r K` by the closed ideal `I`, with its
quotient norm. Let `s` be any strictly positive real polyradius on `Fin m`,
and let `E` be any set of series in the enlarged weighted Tate algebra with
polyradius `r.append s`.

All declarations are in
`Langlands.Analytic.PresentedAffinoidAlgebra.Adjoin`.
The old-variable inclusion `i` is the published bounded map
`GeneralizedTateAlgebra.appendLeft r s K`. The new presentation is

\[
  B_E=K\{r^{-1}T,s^{-1}Y\}/
       \overline{\langle i(I)\cup E\rangle}.
\]

Here the notation denotes the concrete weighted restricted-series algebra and
its actual normed quotient. `relations` constructs the set `i(I) ∪ E`, and
`algebra` applies the published `ofRelations` construction to it. In particular,
it uses every element of the old ideal, with no choice of generators or lifts
of elements of `A`.

Neither coefficient completeness nor a nontrivial valuation is assumed.
The finite arities may be zero, the radii need not lie in the value group,
and the equations may be an infinite set. No properness or reducedness
hypothesis is placed on either ideal, so zero and nonreduced quotients are
allowed. Over complete coefficients the imported `GeneralizedAffinoid.Banach`
instances also give completeness of these presentations.

## Base map, coordinates and equations

`baseMap` constructs a bounded `K`-algebra homomorphism `A → B_E`.
It first composes the isometric inclusion `i` with the enlarged quotient map.
Every element of `I` maps to zero because its image belongs to the supplied
relation set. `BoundedAlgHom.liftQuotient` therefore descends this composite to
the original quotient.

`baseMap_presentationMap` gives its exact formula on representatives:

\[
  \operatorname{baseMap}(q_A(f))=q_{B_E}(i(f)).
\]

`norm_baseMap_le` proves that this map is contractive. The representative
bound combines contraction of the enlarged quotient map with the exact norm
of `appendLeft`; `quotient_norm_bound`, with constant one, then transfers
that bound to the actual quotient norm on `A`.

`baseMap_coordinate` shows that the old coordinate indexed by `i : Fin n`
maps to the coordinate indexed by `Fin.castAdd m i`.
`newCoordinate` is the quotient coordinate indexed by `Fin.natAdd n j`.
Its norm is at most `s j` by `norm_newCoordinate_le`, using the existing
quotient-coordinate bound and the second-block formula for the appended
polyradius. `presentationMap_equation` proves `q_{B_E}(f) = 0` for every
`f ∈ E` by membership in the defining relation set.

## Empty-equation retraction and isometry

For `E = ∅`, `zeroSpecialization` constructs a bounded map `B_∅ → A`.
Its map on enlarged series is the composite of `appendProjectLeft`, which
sets the new variables to zero, and `q_A`. For a relation `i(f)` with
`f ∈ I`, the identity `appendProjectLeft (appendLeft f) = f` shows that
this composite vanishes. There are no extra equations to check.
`descendRelations` extends this vanishing to the closed generated ideal and
constructs the map on the quotient.

`zeroSpecialization_presentationMap` records the representative formula.
`norm_zeroSpecialization_le` proves contraction from contraction of the
coefficient projection and of `q_A`, again transferring the representative
bound to the quotient norm. To prove `zeroSpecialization_baseMap`, the proof
chooses a series representative using `presentationMap_surjective` and
applies the two representative formulas and the published projection-inclusion
identity. Thus zero specialization is a left inverse to the base map.

Combining contraction in both directions proves `norm_baseMap_empty`:

\[
  \|\operatorname{baseMap}(a)\|=\|a\|.
\]

`isometry_baseMap_empty` converts this norm equality into metric isometry
using the additive homomorphism underlying the base map. These are laws of
the constructed maps and quotient norms; no evaluation or extension theorem
is assumed.

## Provenance and scope

The source context is Vladimir Berkovich, *Non-Archimedean analytic spaces*,
Trieste lectures (2009), Example 1.2.2(v), printed/PDF page 4; the quotient
norm discussion and Definitions 2.1.1–2.1.2, page 7; and Exercise 2.2.2(i),
page 9. The registered source is
`berkovich-2009-trieste-analytic-spaces`, with PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

The source defines finite positive-polyradius series, affinoid algebras via
admissible quotients, and Laurent/Weierstrass presentations by adjoining
variables and equations to an affinoid algebra. The present module is a
derived construction on a chosen weighted presentation: it forms a closed
quotient directly over `K`. Its maps, estimates and retraction are justified
by the implemented quotient arguments. Their validity without completeness
is an extension established by those arguments, not a claim attributed to
the complete-field source.

The adaptation from Worker 36 replaces strict evaluation-based variable
inclusion by the coefficientwise weighted inclusion and accepts an arbitrary
closed-ideal presentation and arbitrary enlarged-series equations. It reuses
the published `GeneralizedAffinoid.Relations`,
`GeneralizedTateAlgebra.Embedding` and `BoundedQuotient` interfaces.

Comparison with a relative series algebra over `A`, independence from the
chosen presentation, localization universal properties and representation of
analytic domains remain separate obligations. This module supplies the
concrete adjunction quotient and its intrinsic maps for those later steps.
