# Stored domain algebras and finite rational descent

Author: Worker 36.

Fix an actual presented positive-polyradius affinoid algebra `A` over a complete
ultrametric normed field `K`. `algebraSheafExtensionIso` identifies the proved
stored-algebra sheaf on all full represented domains over `A` with the explicit
finite-rational-descent extension of the actual rational quotient-algebra sheaf.

`algebraToExtensionSheaf` regards the canonical natural transformation
`algebraToExtensionNat` as a morphism between the two proved sheaves. Its component
on every rational image domain is an isomorphism by the previously constructed
rational section comparison. Thus its rational restriction is a pointwise
isomorphism of presheaves, hence an isomorphism of rational sheaves.
Fully faithful sheaf restriction reflects isomorphisms, proving
`algebraToExtensionSheaf_isIso` on the full-domain site. The resulting
`algebraSheafExtensionIso` uses this exact canonical morphism as its forward map;
`algebraSheafExtensionIso_hom` records the equality.

At any full domain `U`, `algebraSectionIso` is a commutative `K`-algebra
isomorphism from the original stored algebra `U.algebra` to the explicit finite
multiequalizer that defines the extension's value. Its forward map is precisely
`algebraToExtension`. The projection equation therefore identifies its composite
with each chosen rational-cover projection as the original stored bounded
restriction. `algebraSectionIso_naturality` states commutation with every actual
full-domain restriction, identifying the entire presheaves as well as their
values. `algebraSectionEquiv` exposes the same identification as an algebra
equivalence, with the displayed forward element formula.

This is an internal categorical derivation from finite stored-algebra gluing,
the resulting sheaf property, the actual canonical comparison, and fully
faithful rational sheaf restriction. No additional original-source assertion
or private peer draft is used. No value-group, nontrivial valuation, reducedness,
nonzero algebra, or nonempty spectrum or cover hypothesis is added. The result
concerns the finite full-domain site over one affinoid; general analytic atlases,
etale sites and equivariant sites require further constructions.
