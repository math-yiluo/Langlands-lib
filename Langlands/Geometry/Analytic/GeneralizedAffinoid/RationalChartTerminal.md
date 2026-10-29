# The actual whole rational chart and its terminal property

Author: Worker 56.

The namespace is
`Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart`.
Let `K` be an ultrametric normed field and let
`A : PresentedAffinoidAlgebra K`. The underlying algebra of `A` is the
published closed quotient of a finite positive-polyradius Tate algebra, with
its actual quotient norm. The construction uses the published `RationalChart`
category of rational presentations over this fixed algebra.

## The empty-variable chart

`whole K A` has arity zero, the unit polyradius on `Fin 0`, denominator one,
and the empty numerator tuple. Its unit-ideal generation condition follows
because the image of its denominator is one. Its algebra is the actual
`RationalPresentation` closed quotient for these data, rather than a
replacement carrier defined to be `A`.

`locus_whole` proves that the chart's inequality locus is `Set.univ` in
`BanachSpectrum A`: there are no numerator inequalities to check.
These two declarations require no completeness hypothesis on `K`. This is
an internal extension of the concrete quotient construction beyond the
complete-field context of the cited analytic-space source.

## The constructed algebra identification

The remaining declarations assume `CompleteSpace K`. Define
`wholeRetraction K A` from the whole-chart algebra to `A` by composing:

1. The published isometric `RationalPresentation.relativeEquiv`, from the
   scalar presentation to its intrinsic relative rational quotient.
2. `RelativeRationalPresentation.evaluate` in `A`, with the identity base
   map and the empty tuple of substituted coordinates.

The relation equations are vacuous. The monomial estimate needed by relative
evaluation comes from `monomialValue_norm_le_weight`, using the existing
bound `‖(1 : A)‖ ≤ 1` and the empty coordinate bounds. This bound also
allows the zero quotient.

`wholeRetraction_baseMap` proves that the retraction composed with the
whole chart's structural map is the identity on `A`, by the two comparison
and evaluation base-map equations.
`wholeRetraction_comp_baseMap` records the corresponding bounded algebra
homomorphism equality.

`wholeBaseMap_comp_retraction` proves the other inverse equation using
`RationalPresentation.hom_ext_base`. The two endomorphisms of the actual
whole-chart quotient agree after composition with its structural map, by
`wholeRetraction_baseMap`. The uniqueness theorem for bounded maps over
the base therefore identifies them. `wholeBaseMap_retraction` is the
pointwise version.

`norm_wholeRetraction_le` combines the contractive relative evaluation
estimate with the isometric scalar-to-relative comparison.
`norm_wholeBaseMap` combines contraction of the structural map with
contraction of its left inverse to prove

`‖(whole K A).baseMap a‖ = ‖a‖`.

The other inverse equation gives `norm_wholeRetraction`, the analogous
norm equality for the retraction.
`wholeEquiv K A` packages these constructed inverse bounded algebra maps
as a `BoundedAlgEquiv K A (whole K A).algebra`.
`wholeEquiv_apply` and `wholeEquiv_symm_apply` identify its two maps,
and `norm_wholeEquiv` and `isometry_wholeEquiv` record its isometry.

## Spectrum and terminality

`wholeSpectrumHomeomorph K A` is the spectrum homeomorphism induced by
`wholeEquiv`, directed from the whole-chart spectrum to the base spectrum.
`wholeSpectrumHomeomorph_apply` proves that its forward map is precisely
`(whole K A).spectrumMap`, the seminorm comap of the structural algebra map.
`wholeSpectrumHomeomorph_symm_apply` identifies its inverse at a seminorm
`x` and a quotient element `a` with `x (wholeRetraction K A a)`.

For any `d : RationalChart K A`, `toWhole K A d` constructs an arrow
`d ⟶ whole K A`. An arrow in this category stores a bounded algebra map
in the opposite direction, so its restriction is

`d.baseMap.comp (wholeRetraction K A)`.

Its equation over `A` follows from `wholeRetraction_comp_baseMap`.
`toWhole_restriction` gives the elementwise formula, and
`norm_toWhole_restriction_le` proves that this actual restriction is
contractive. `toWhole_spectrumMap` proves that, after the constructed
whole-spectrum homeomorphism, its induced spectrum map is the original
structural map of `d`.

The selected declaration `wholeIsTerminal K A` constructs
`CategoryTheory.Limits.IsTerminal (whole K A)` by `IsTerminal.ofUniqueHom`.
Existence uses `toWhole`; uniqueness uses the already proved subsingleton
property of actual restrictions over `A`. Thus a restriction algebra map
is constructed before the categorical property is packaged.

## Provenance and scope

The original analytic context is Berkovich, *Non-Archimedean analytic spaces*
(Trieste lectures, 2009), Exercise 2.2.2(i),(ii), printed/PDF page 9,
Fact 2.2.3(i) and Definition 2.2.7, printed/PDF page 10.
The registered source is `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The original describes positive-radius quotient models, their spectrum
identification, and affinoid domain embeddings.
In Exercise 2.2.2(ii) the displayed inequality contains a subscripted
`g_i`, while the data and quotient relations use a single denominator `g`;
the published Lean rational-presentation model uses that common denominator.
Here it is one.

This contribution has derived provenance. The empty-tuple,
denominator-one specialization, the particular evaluation and norm proofs,
and the chosen-presentation terminal-object witness are internal constructions
from the published quotient, comparison, evaluation and restriction APIs.
The cited source supplies their analytic context; it does not state this
exact Lean categorical packaging.

Arity zero, arbitrary positive radii in the presentation of `A`, trivial
valuations and zero quotients are permitted. The terminal property concerns
the existing category of rational charts with actual bounded restrictions
over `A`. Full image-based factorization against arbitrary affinoid test
algebras in Definition 2.2.1, general affinoid domains, structure sheaf gluing,
analytic atlases and etale or equivariant sites remain further constructions.
