# Freeness of the induced progenerator endomorphism ring

`Langlands.Aubert.General.RepresentedParabolic.inducedProgeneratorEndFree`
proves `InducedProgeneratorEndFreeStatement.{u, v}`. For every actual rational
parabolic \(P=MN\) and every irreducible supercuspidal \(\pi\) of \(M(F)\) with
an irreducible \(\rho_0\) embedded in its restriction to the common norm kernel
\(M(F)^0\), write
\(\Pi_D=\mathrm{c\text{-}Ind}_{M(F)^0}^{M(F)}\rho_0\),
\(R_D=\operatorname{End}_M(\Pi_D)\) and
\(R_\Omega=\operatorname{End}_G(i_P^G\Pi_D)\). The theorem gives injectivity
of \(R_D\to R_\Omega\), finiteness of the set \(W\) of twist-stabilizing
double cosets, and unique expansions in bases of \(R_\Omega\) over \(R_D\)
and over the centre of \(R_D\). The first basis has \(|W|\) elements and
the second is finite. Both use the right action
\(x\cdot a=x\circ i_P^G(a)\). [Statement](InducedProgeneratorEndFreeStatement.md)

The Lean proof applies `inducedProgeneratorEndFree_of_jointSpecialCompact`
to `BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence.{u}`. The
reduction uses the joint special-compact basis to obtain compact
coefficients of the norm-kernel restriction of \(\pi\), which give
projectivity of \(\Pi_D\). Supercuspidality of \(\Pi_D\) comes from
`isSupercuspidal_rationalNormKernelSummandInduction`.
[Reduction](InducedProgeneratorEndFreeReduction.md)
[Joint basis proof](../../BruhatTits/SpecialCompact/JointBasisProof.md)

Injectivity follows from `leviInductionEndEmbedding`. Finiteness of \(W\)
follows from `normalizerDoubleCosets_subset_finite`. For the expansion over
\(R_D\), `inducedProgeneratorEnd_expansion` uses first adjointness to identify
the right \(R_D\)-module \(R_\Omega\) with
\(\operatorname{Hom}_M(r_P^G i_P^G\Pi_D,\Pi_D)\).
The geometric lemma filters the Jacquet module by double cosets. The
successive quotients are projective or zero, so the filtration splits.
The terms indexed by \(W\) give copies of \(\Pi_D\) and the other terms have
zero Hom into \(\Pi_D\). This yields the basis and the unique expansion
\(x=\sum_i b_i\circ i_P^G(a_i)\). The reduction composes this expansion
with the finite expansion of \(R_D\) over its centre using
`leviInducedEndCenterExpansion_of_endExpansion`.
[Basis construction](InducedProgeneratorEndBasis.md)
[Expansion over the centre](NormKernelSummandCenterBasis.md)

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, VI.10.4, printed pp. 209–210 / PDF
pp. 215–216, including the injectivity observation and the first Lemma.
Renard uses second adjointness and projects the geometric-lemma filtration
to the inertial block \(D\). The implemented first-adjunction argument
obtains the same expansion through vanishing of Hom for the other pieces.
The registered source ID is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
