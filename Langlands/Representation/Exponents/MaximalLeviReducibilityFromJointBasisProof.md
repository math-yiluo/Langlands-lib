# Maximal-Levi reducibility from a joint compact basis

`maximalLeviReducibilityFromJointBasis` derives the represented reducibility
criterion from `JointSpecialCompactBasisExistenceStatement` at field universe
\(u\). If the normalized induction of an irreducible supercuspidal
representation from a maximal proper rational parabolic is reducible, the
criterion gives a rational point outside the Levi that normalizes it. It also
gives an isomorphism between the conjugate inducing representation and its
twist by a positive unramified character. The inducing carrier universe
\(v\) is independent of \(u\).
[Statement](MaximalLeviReducibilityFromJointBasisStatement.md)

The proof uses `maximalLeviSupercuspidalReducibilityFromInputs`. The joint
basis, standard cocharacters and standard parabolic order give the
Jacquet–Cartan datum, which yields admissibility for irreducibles at both
the inducing universe \(v\) and the induced universe \(\max(u,v)\). The
assembly also uses the theorems on the dynamic description of parabolics,
compactness of the parabolic quotient, unimodularity, standard cocharacters,
root presentations, and endomorphisms and morphisms of the induced
representations.
[Reducibility assembly](MaximalLeviSupercuspidalReducibilityFromInputsProof.md)

For an irreducible supercuspidal representation with unitary central
character, the joint basis, standard cocharacters and the relative root
system give compact support of the descended coefficient norms on the
quotient by the center. The compact-coefficient theorem uses these norms
to construct an invariant positive form, giving unitarizability.
[Coefficient support](SupercuspidalCoefficientCompactSupportReduction.md) ·
[Unitarization](../Unitary/CompactCoefficientProof.md)

For the constituent input, `rationalNormKernelUniformSupport_of_joint` gives
one compact support for the coefficients of the compact representations at
each fixed level of the common norm kernel. The proof takes the Borel Haar
measure on that open kernel and applies `fixedStratum_finite_of_uniformSupport`.
This gives finiteness of the compact-coefficient isomorphism classes with a
nonzero fixed vector at that level, the condition (KF) of VI.3.4. Applying
the constituent reduction to the joint basis and this finiteness at carrier
universe \(\max(u,v)\) supplies the last input of the reducibility theorem.
[Uniform support](../CuspidalSupport/RationalNormKernelSupportGeometry.md) ·
[Fixed-stratum finiteness](../CompactCoefficient/UniformSupportFinitenessProof.md) ·
[Constituent reduction](MaximalLeviUnitarizableConstituentLeafReduction.md)

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026. The criterion is VII.1.3, printed pp. 224–226 (PDF pp.
230–232). The geometric inputs correspond to V.5.1–2, printed pp. 122–123 (PDF
pp. 128–129), and fixed-level finiteness is used in the proof of VI.3.4,
printed p. 146 (PDF p. 152). Registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
