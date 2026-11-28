# Convolution of tests with a fixed central character

Henniart and Lemaire, *Changement de base et induction automorphe pour
GL_n en caractéristique non nulle* (2011), I.2.9, printed p. 22 (PDF p. 30),
use convolution with a chosen quotient Haar measure on the single-place group.
The retained PDF has source ID
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`
and SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.

For a central subgroup `Z` of a topological group `G`, two tests `f₁, f₂` with
the same inverse central character, and a Borel Haar measure `μ` on `G ⧸ Z`,
`Langlands.Hecke.CentralCharacterTest.convolution` has value at `g` given by the
integral of `convolutionIntegrand` against `μ`. This function takes the value
`f₁(x) f₂(x⁻¹ g)` on the class of `x`. Replacing `x` by `z x` multiplies
the two factors by `ω(z)⁻¹` and `ω(z)`, respectively. The Library's
`QuotientIntegration.descend` descends the kernel to left cosets, and
`QuotientIntegration.normalLeftQuotientHomeomorph` identifies them with `G ⧸ Z`.

The product of the identity with the quotient projection is open and is a
quotient map, so joint local constancy follows from local constancy of the kernel
on `G × G`. At each `g`, the descended kernel vanishes off the compact projected
support of `f₁` and is continuous. This proves integrability. Compactness of the
same set lets joint local constancy give a neighborhood of `g` on which the
entire kernel stays fixed, so the integral is locally constant. Translating `g`
by `z` multiplies the second factor by `ω(z)⁻¹` and gives the equivariance law
for the integral. If the kernel is nonzero at `(g, [x])`, then `[g]` is the
product of `[x]` and `[x⁻¹ g]` from the two projected supports. The projected
support of the result is therefore contained in their compact product and is
closed by local constancy and equivariance. The construction uses the same
supplied measure throughout.
