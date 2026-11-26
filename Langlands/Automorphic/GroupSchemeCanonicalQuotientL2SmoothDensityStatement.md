# Smooth-vector density on the canonical adelic quotient

`Langlands.Global.RestrictionSplitCentre.CanonicalQuotientL2SmoothDensityStatement`
states two norm-density assertions for the canonical \(L^2([G])\) of a
connected reductive group over a number field. It uses
`CanonicalQuotient F G`, `canonicalMeasure F G` and the existing right
actions on their \(L^2\) classes. The first dense set consists of vectors
with a smooth infinite adelic orbit in the existing reductive atlas.
The second consists of those smooth vectors that are also fixed by an open
subgroup of the finite adelic group, expressed by
`rationalQuotientL2BiSmoothVectors`.

The carrier and measure follow Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), §2.6, (2.19)–(2.22) and Lemma 2.6.2, printed
pp. 68–69 (PDF pp. 85–86). In this convention
\([G]=A_G G(F)\backslash G(\mathbb A_F)\), with \(A_G\) the identity component
of the real points of the greatest \(\mathbb Q\)-split torus of the
restriction of scalars of the centre. The registered source is
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.

The density assertions are a derived specialization of
`QuotientL2SmoothDensityStatement`. The canonical split components give the
subgroup comparison and the central split torus. Character restriction is
injective by `canonical_characterRestrict_injective` applied to
`centralSplitTorusCharacter`, and has finite-index range by
`canonical_finiteIndex`. Right Haar invariance on the norm-one group comes
from `AdelicGroupPoints.normOneHaarRightInvariant`. The measure and right
invariance in the conclusion are the canonical ones.

The statement uses number fields and group schemes in universe zero, as
in the canonical quotient. Its mathematical scope includes non-split
and anisotropic connected reductive groups. Density concerns \(L^2\)
vectors and their orbit maps.
