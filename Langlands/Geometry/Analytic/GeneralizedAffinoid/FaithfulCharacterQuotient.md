# Presented quotients with faithful bounded characters

Let `K` be an ultrametric normed field, `R` a presented affinoid `K`-algebra,
and `L` any normed commutative `K`-algebra. For a bounded algebra map
`χ : R → L`, this construction forms the actual presented closed quotient
of `R` by `ker χ`. Neither completeness of `K` or `L` nor a field
structure on `L` is needed for this algebraic construction.

The kernel is closed because the bounded map is continuous and `L` is
Hausdorff. The existing `ClosedQuotient` construction supplies the
presented quotient algebra and its surjective bounded quotient map.
Its bounded quotient universal property descends `χ` to `character χ`.
The factorization is an equality of bounded algebra maps.

The descended character is injective: choose representatives for two
quotient elements, subtract them, and use that their character values
agree precisely when the difference lies in the kernel. Consequently,
composition with this character detects equality of bounded algebra maps
into the quotient.

Pullback of multiplicative seminorms along the quotient map is injective,
since every quotient element has a representative. Thus if the spectrum
of `R` is small in any independently specified universe `v`, the quotient
spectrum is small in that same universe. The algebra universe `u`, the
smallness universe `v`, and the coefficient universe `uL` remain
independent.

This is an internal construction from the published presented closed
quotient and actual bounded spectrum APIs, together with Mathlib's
smallness transfer along an injection. It supplies a faithful algebraic
test source; it does not assert a universal property of analytic
pullbacks or equality detection for arbitrary analytic morphisms.
