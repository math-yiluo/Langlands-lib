# Renard II.2.5: the original-action projector presheaf

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, II.2.5, printed pp.39–40 / PDF pp.45–46,
the inverse-functor definition before (II.2.5.1). The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The 2010 corrections, PDF pp.2–3, concern the separate smooth-algebra
nondegeneracy convention; the 2026 source includes that clarification.

All declarations are in `Langlands.Sheaf.Renard.ProjectorBasisSheaf`.
`compactOpenBasis hX` consists of every compact open of the supplied topology,
using the published compact-open neighborhood-basis theorem. Its basis objects
retain their actual open subsets and inclusion arrows. Compact opens are closed
because `hX : IsLocallyProfinite X` supplies Hausdorffness. The empty open,
binary unions and binary intersections are actual objects of this basis.

For an abelian group `M : Type v` with its specified original
`NonUnitalModule (PointwiseTestAlgebra.Carrier X) M`, `Value hX M U` is exactly
the published `NonUnitalModuleCorner.FixedPart` at the actual characteristic
idempotent of `U`. `fixedPart_eq_range` identifies its subgroup with the image
of the original characteristic action. No new fixed-part model is introduced.
`action_apply` explicitly selects the original module's scalar operation.

`restrict hX M h` is the full additive map obtained by composing the published
projection for the smaller open with the published inclusion for the larger.
`restrict_val` and `coe_restrict` expose its entire formula. The characteristic
product identity proves `action_absorb`, which gives identity and composition
of restrictions. `rawPresheaf` packages the resulting actual contravariant
functor, with value universe exactly `v`, independent of the space universe `u`.
`restriction_hom` and `restriction_val` identify its categorical restrictions.
The zero characteristic of an empty open forces every fixed vector to vanish;
this proves normalization and gives the actual normalized `presheaf`.

Renard uses nondegenerate modules for the later equivalence. This additive
presheaf construction needs only the original module laws, so allowing all
original modules is an internal strengthening of the source definition.
No complex scalar action on `M`, smooth extension, output separation or gluing
hypothesis is assumed. This unit constructs the presheaf and does not claim
the sheaf condition, categorical functor, compact-section recovery, equivalence
or stalk comparison; the sheaf and functor constructions are subsequent units.
