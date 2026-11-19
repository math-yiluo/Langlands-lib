# The relative inverse Herbrand function of a Kummer step

`Langlands.Ramification.Kummer.kummerStepHerbrandPsi` proves
`KummerStepHerbrandPsiStatement` at an arbitrary universe level. Let \(F\)
be a \(p\)-adic field of absolute ramification index \(e_F\), let \(\varpi\)
be a uniformizer, and put \(E=F(\alpha)\) for \(\alpha^p=\varpi\) in the
algebraic closure. With \(b=pe_F/(p-1)\), the theorem gives
\(\psi_{E/F}(x)=x\) on \([-1,b]\) and
\(\psi_{E/F}(x)=px-pe_F\) on \([b,\infty)\). The base field may lack
primitive \(p\)-th roots of unity. [Published statement](KummerTowerStatement.md)

At \(b\), `kummerStepUpperSup` gives \(G_E \vee G_F^b=G_F\).
`herbrandPsiTruncation` turns this equality into the identity on \([-1,b]\),
including \(\psi_{E/F}(b)=b\). [Kummer-step ramification](KummerStepUpperSupProof.md),
[truncation](KummerTruncationProof.md)

For \(y>b\), `kummerStep_upper_le_fixingSubgroup` gives \(G_F^y\le G_E\).
The slope theorem `relativeHerbrandPsi_sub_eq_relIndex` then gives slope
\([I_F : I_F\cap G_E]\) for increments starting at \(y\), where \(I_F\)
is absolute inertia. The published index identity
`fixingSubgroup_relIndex_absoluteInertia_mul` gives
\([I_F : I_F\cap G_E]e_F=e_E\).
`kummerStep_root_ord_and_ramificationIndex` gives \(e_E=pe_F\), so positivity
of \(e_F\) yields slope \(p\). [Slope proof](SlopeProof.md),
[Kummer-step ramification](KummerStepUpperSupProof.md)

For each \(x\ge b\), the proof fixes the increment length \(x-b\).
The increment \(y\mapsto \psi_{E/F}(y+(x-b))-\psi_{E/F}(y)\) is \(p(x-b)\)
for \(y>b\), and it is continuous by `relativeHerbrandPsi_continuous`.
`Set.EqOn.closure` extends the equality to the closed ray \([b,\infty)\).
Evaluating at \(b\) gives
\(\psi_{E/F}(x)=b+p(x-b)=px-pe_F\), using \((p-1)b=pe_F\).
[Continuity proof](ConvexityProof.md)

The step formula specializes to the calculation in the proof of Lemma
`lem:tower` of the operator's *Numerical local Langlands for GL_n, counts on
the two sides and the recommended route* (16 November 2026, registered
`operator-numerical-llc-route-2026-11-16`, lines 1196–1207). The version for an
arbitrary base field uses the upper group profile described in Remark 4.1(i)
of *Formalizing the large external inputs of the local Langlands correspondence
for GL_n* (16 November 2026, registered `operator-external-inputs-plan-2026-11-16`,
lines 586–603). The relative function is the inverse of the one in Serre,
*Local Fields*, IV §3, Remark 2 (printed p. 75, registered
`serre-1979-local-fields`), with the finite-extension convention in
Wintenberger, *Le corps des normes de certaines extensions infinies de corps
locaux; applications*, §1.2.1 (printed p. 62, registered
`wintenberger-1983-field-of-norms`).
