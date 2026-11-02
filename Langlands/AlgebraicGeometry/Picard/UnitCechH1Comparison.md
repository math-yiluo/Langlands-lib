# Actual unit-sheaf H¹ for finite-cover line-bundle cocycles

This is an internal bridge between the published actual-unit transition
encodings, fixed-cover gauge classification, and finite-cover comparison with
actual sheaf cohomology. Fix `X : Scheme.{u}` and an open family
`U : ι → X.Opens`, with `ι : Type u`.

`unitSheaf X` abbreviates the actual abelian-group sheaf of units of the
structure sheaf. Its underlying presheaf is the previously published actual-unit
presheaf, with multiplication written additively.
`pairUnits_transitionCochain` and `transitionCochain_pairUnits` identify the two
published encodings as inverse functions on all overlap units and all ordered
one-cochains. These identities need no closedness or covering hypothesis.

`quotientClass_eq_iff` spells out equality in the fixed-family ordered Čech H¹
quotient: the classes of closed cochains `z` and `w` agree if and only if
`w - z = d a` for a zero-cochain `a`. The sign is the one already used in the
published unit-gauge classification. This lemma also needs no cover hypothesis
or finiteness.

Now assume that the index type is finite and the opens cover `X`.
`classOfCocycle U hU z` is the image of the Čech class of `z` under the published
`AbelianSheafCechH1.comparisonHom`. Its value lies in the actual
`CategoryTheory.Sheaf.H (unitSheaf X) 1`, defined through Ext in Mathlib.
The comparison uses the published chosen injective embedding and connecting
homomorphism; it is not a newly defined cohomology group.

Injectivity of that comparison and the quotient equality criterion prove
`classOfCocycle_eq_iff`: the two actual H¹ classes agree exactly when `w - z`
is a zero-cochain differential. Combining this with the published classification
of glued module sheaf isomorphisms gives
`nonempty_iso_glued_iff_classOfCocycle_eq`: on this finite full cover, the actual
module sheaves glued from `z` and `w` are isomorphic exactly when their actual
unit-sheaf H¹ classes agree.

For chosen finite affine transition data `D : UnitCechPresentation.FinitePresentation M`,
`D.cohomologyClass` is the class of its closed cochain.
`D.lineBundleIso` reuses the published recovery isomorphism to identify `M` with
the underlying module sheaf of the actual line bundle constructed from that
cochain. Existence of such data for a locally free rank-one module on a compact
scheme is already published in `UnitCechPresentation`.

The provenance is internal: inverse encoding formulas come directly from
`UnitCechPresentation`, the quotient equality is the additive quotient relation,
and the main equivalence composes the published actual comparison injection
with the published unit-gauge criterion. No new external assertion is translated.
No cover-independent classification of all line bundles is claimed.
In particular, independence of `D.cohomologyClass` from the chosen cover or
presentation, coverage of all actual H¹ classes by these constructions,
pullback or sheaf-morphism naturality, the Picard group law, deformation and
Picard representability remain separate obligations.
