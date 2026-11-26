# Proof of the central uniformizer lattice comparison

`Langlands.Aubert.General.RepresentedParabolic.centralUniformizerSquareIntegrability`
proves `CentralUniformizerSquareIntegrabilityStatement.{u,v}`.
[Statement](CentralUniformizerSquareIntegrabilityStatement.md)

The common norm kernel of the actual split component \(A_G(k)\) is
open. Its intersection with the image of the uniformizer section is
the identity, by uniqueness of the section representative modulo the
norm kernel. Thus the lattice is discrete and closed in the
Hausdorff split torus. The closed point embedding of the split
component into \(G(k)\) transports this closedness to the image
\(C_{A_G}\).

Write \(Z=Z(G(k))\). The projection from \(Z/C_{A_G}\) to
\(Z/A_G(k)\) is a continuous open surjective homomorphism.
Its kernel is the image of the compact common norm kernel of
\(A_G(k)\). Indeed a point of \(A_G(k)\) differs from its
uniformizer-section representative by a norm-kernel element, and
the section representative becomes the identity in \(Z/C_{A_G}\).
The compact-kernel properness theorem then gives compactness of
\(Z/C_{A_G}\) as the preimage of \(Z/A_G(k)\), whose compactness is
supplied by `compactSpace_center_quotient_splitComponent`.
[Compact-kernel properness](../../Analysis/CompactKernelHaarLpProof.md) ·
[Compactness of the quotient by the split component](../../HarmonicAnalysis/HarishChandraSchwartz/RationalSquareIntegrableDecayProof.md)

The proof applies `centralSubgroupCoefficientLpComparison` to
\(C_{A_G}\subset Z\) with the proved closedness and compact
central quotient. Its square-integrability clause compares the
same admissible representation with the unitary character of \(Z\)
and the same smooth-dual matrix coefficients on both quotients. The
comparison uses Haar uniqueness to relate the pushforward of the
lattice-quotient measure to the independently chosen measure on
the full central quotient by a finite positive factor.
[Haar and coefficient comparison](../Plancherel/CentralSubgroupComparisonProof.md)

Source. David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026. VII.1.2, first paragraph of the proof,
printed p. 221 (PDF p. 227), with V.2.5, printed p. 107 (PDF p. 113), and
IV.3.1–2, printed p. 99 (PDF p. 105). Registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
