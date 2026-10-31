# Resolution formulas for source squares with target coefficients

This internal successor to `DerivedPlusSource` records the actual morphism in
D⁺ obtained by following a derived source square with a target coefficient map.
A compatible lift from the mapped source resolution to any target injective
resolution computes the composite. The hypotheses and localization universes
are those of `DerivedPlusSource`; no exactness of the two section-like functors
is added.

The proof uses the arbitrary-resolution component formula for `derivedMap` and
naturality of `imageResolutionIso` for the chosen compatible lift. It cancels
the target representative isomorphism and applies functoriality of localization.
It does not deduce equality from equality on cohomology.
