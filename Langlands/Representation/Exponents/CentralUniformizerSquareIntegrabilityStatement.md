# Square integrability modulo the central uniformizer lattice

`Langlands.Aubert.General.RepresentedParabolic.CentralUniformizerSquareIntegrabilityStatement`
states the central-quotient comparison at the start of the proof of
Renard VII.1.2. Let \(G\) be connected reductive over a nonarchimedean
local field \(k\), and let \(a\colon A_G\to G\) be an actual split
component. The subgroup \(C_{A_G}\) is the image in \(G(k)\) of the
cocharacters of \(A_G\) evaluated at the chosen uniformizer. It is
`RenardCartan.C0 A a`, the image of `CocharacterUniformizer.CA k A`
under the actual point homomorphism.
[Uniformizer subgroup](../Plancherel/RenardUniformizerSection.md)

The proposition asserts that \(C_{A_G}\) is closed in \(G(k)\) and that
\(Z(G(k))/C_{A_G}\) is compact. For any smooth complex representation
and independently chosen Haar measures on the Borel quotients
\(G(k)/C_{A_G}\) and \(G(k)/Z(G(k))\), it then identifies square
integrability modulo the lattice with square integrability modulo the
full center. Both published predicates include admissibility and a
unitary character of the full abstract center acting on the
representation. The character on the lattice is its restriction, and
the comparison concerns the norms of the same smooth-dual matrix
coefficients on the two quotients.
[Coefficient definitions](../Plancherel/CentralSubgroupCoefficients.md) · [Full-center definition](../MatrixCoefficient/ModuloCenter.md)

The source uses the compactness of \(Z(G(k))/A_G(k)\) and the section
decomposition \(A_G(k)={}^{0}\!A_G(k) C_{A_G}\), with compact norm
kernel \({}^{0}\!A_G(k)\). Closedness of the subgroup is made explicit
here for the comparison of the quotient measures. Once closedness and
compactness are established, the published
`centralSubgroupCoefficientLpComparison` gives the equivalence for
arbitrary Haar normalizations.
[General central-quotient comparison](../Plancherel/CentralSubgroupComparisonStatement.md)

Source. David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026. VII.1.2, first paragraph of the proof,
printed p. 221 (PDF p. 227), with V.2.5, printed p. 107 (PDF p. 113), and
IV.3.1–2, printed p. 99 (PDF p. 105). Registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
