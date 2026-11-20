# Global presentations of rational height

This constructs a global case of the actual numerator-minus-denominator kernel-rank formula used by Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper half spaces* (1997), Appendix, printed p. 112 (PDF p. 38). The rank exponents are normalized by the formal module residue cardinality `q`.

`RationalHom.GlobalHeightPresentation` adds a constant numerator rank to a global scalar-isogeny presentation. The source's finite scalar height determines the denominator rank. The presentation extends to each open by coefficient base change and supplies the same local height at every prime.

On a cover built from global formal modules, chart evaluation first extends the numerator and denominator to the test algebra and then conjugates by the actual chart coordinate isomorphisms. Both operations preserve the signed height.

The inverse calculation applies when the source and target have the same positive scalar height. Choose an integral dual at a scalar exponent large enough to accommodate both the given denominator and the numerator rank. The actual composite is the corresponding scalar homomorphism. Multiplicativity of the actual kernel ranks gives the complementary numerator exponent at each prime. Canceling the original denominator in the rational composition shows that the dual with the new denominator presents the specified inverse tensor. Subtracting its scalar denominator exponent gives the negative of the original signed height.
