# The cuspidal unit `°e` and the hypotheses of the local kernel step of Proposition VIII.4.1

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI 10.1017/S1474748003000082, literature ID `waldspurger-2003-plancherel`.
Relevant passage: the proof of Proposition VIII.4.1, printed pp. 328–330
(PDF pp. 94–96).

This module belongs to unit 3 ("rank adapter") of Task 7439, revision 2. Its
provenance is **derived**. It contains no new mathematics. It joins modules of
the same task, bundles six existing laws into one definition, and reads one
conjunct off the Library's closed statement of Corollary VIII.3.2.

* `RationalCuspidalUnit` (unit 3, first layer) defines the predicate
  `IsRationalCuspidalUnit` for the properties of `°e`. It derives that predicate
  for `P(1_H)` from six named laws of an arbitrary complex-linear operator `P` on
  the actual rational Schwartz space.
* `RationalCuspidalCentralKernelStep` (unit 2) defines the structure
  `IsRationalCuspidalLevelKernel` for the same properties; this is the
  hypothesis on `°e` of the local kernel step.
* `RationalCuspidalCentralKernelPairing` (a follow-up of unit 2) defines
  `RationalLevelKernelConjugationIntegrable`, the integrability form of VIII.3.2
  at `E`; this is the second hypothesis on `°e` of the local kernel step.
* `RationalCuspidalConjugationStatement` (Library) states the closed
  Corollary VIII.3.2, `RationalCuspidalConjugationIntegrabilityStatement`.

## What the source does

In the case where `χ` is trivial on `A_G ∩ H`, the proof of VIII.4.1 applies the
degree-zero projection of VIII.2 to the characteristic function `e = 1_H`. It
records that `°e ∈ °C_H`, that `°e` is real and that `°e` is supported in `G¹`
(p. 328). With `φ ∗ °e = mes(H) φ` from Lemma VIII.2.3, it builds the kernel
`α_χ` from `°e` and proves that the central level image is finite dimensional
(pp. 329–330). That step needs the diagonal integral of `α_χ` over
`A_G \ G` to converge, which the source deduces from Corollary VIII.3.2
(pp. 329–330). This module proves that `°e`, for an operator with the
laws of VIII.2, satisfies the two hypotheses on `°e` of the kernel step as
formalized in Task 7439: the properties above, and the VIII.3.2 integrability
form at `°e`.

## What this module proves

* `isRationalCuspidalUnit_iff_isRationalCuspidalLevelKernel`: for a measure `μG`,
  an open subgroup `H` and `E` in the actual rational Schwartz space,
  `IsRationalCuspidalUnit hKc hPK ρ μG H.toSubgroup E` holds if and only if
  `IsRationalCuspidalLevelKernel hKc hPK ρ μG H E` holds. The five conjuncts and
  the five fields match one to one. Two of them differ only in form:
  * support in `G¹` is `E x ≠ 0 → x ∈ G¹` in the predicate and
    `x ∉ G¹ → E x = 0` in the structure; these are contrapositives;
  * the reproduction constant is `μG.real H` in the predicate and
    `(μG H).toReal` in the structure; these are equal by definition of
    `Measure.real`.
* `IsRationalCuspidalUnit.isRationalCuspidalLevelKernel`: the forward direction,
  in the form used by consumers.

### The bundled laws (definition, entry declaration)

`IsRationalDegreeZeroOperator hKc hPK ρ μG P` is, for a measure `μG` and a
complex-linear operator `P` on `RationalSchwartzSpace hKc hPK ρ`, the conjunction of
the six laws of `RationalCuspidalUnit`, in this order:
`RationalDegreeZeroRangeLaw`, `RationalDegreeZeroTranslationLaw`,
`RationalDegreeZeroConjLaw`, `RationalDegreeZeroCheckLaw`,
`RationalDegreeZeroTwistLaw` and `RationalDegreeZeroLeftConvolutionLaw μG`.
It adds no condition to them. Its purpose is to give the later instantiation
(`P := degreeZero`) and the assembly a single hypothesis.

### The two hypotheses of the kernel step for `°e` (proved)

* `IsRationalDegreeZeroOperator.isRationalCuspidalUnit`: for a Haar measure `μG`
  and a compact open subgroup `H`, `IsRationalCuspidalUnit hKc hPK ρ μG H.toSubgroup (P e)`,
  where `e = rationalSubgroupIndicator hKc hPK ρ μG H` is the characteristic function
  of `H` in the Schwartz space. This is `isRationalCuspidalUnit_of_degreeZeroLaws`.
* `IsRationalDegreeZeroOperator.isRationalCuspidalLevelKernel`: the same, converted
  to `IsRationalCuspidalLevelKernel hKc hPK ρ μG H.1 (P e)`.
* `RationalCuspidalConjugationIntegrabilityStatement.levelKernelConjugationIntegrable`.
  It assumes the Library's closed statement
  `RationalCuspidalConjugationIntegrabilityStatement` (Corollary VIII.3.2) and the
  structural data that statement quantifies over: `G` connected reductive,
  `IsMaximalSplitTorus i`, `IsGenericCocharacter i ν`, a subgroup `K0` with
  `SimultaneousStandardBasisAt i ν K0`, `IsClosedSubgroup ρ` and
  `IsSplitComponent s`. It also takes Haar measures `muA` and `μG`. It concludes
  `RationalLevelKernelConjugationIntegrable hKc hPK ρ hs muA μG E` for every `E` in
  `rationalCuspidalSubmodule hKc hPK ρ`. That predicate says: for every
  right-invariance instance on `muA`, every Borel structure on `A_G(F) \ G(F)`,
  every quotient measure `muQ` compatible with `μG` and `muA`, and every `f₂` in
  the actual Schwartz space, the descended conjugation pairing
  `q ↦ ∫ E(q̇ g q̇⁻¹) f₂(g) dμG(g)` is `muQ`-integrable. The proof applies the
  statement to the structural data and to the quantified instances, `muQ` and its
  compatibility. It then takes the second conjunct at `f₁ = E`.
* `IsRationalDegreeZeroOperator.levelKernelConjugationIntegrable`: the previous
  item at `E = °e = P(1_H)`, for an operator `P` with the degree-zero laws, a Haar
  measure `μG` and a compact open subgroup `H`. The range law gives
  `°e ∈ rationalCuspidalSubmodule`.

The local kernel step itself (finite dimensionality of
`rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ H.toSubgroup` from these two
hypotheses on `°e`) is not composed here. Unit 2 proves it, and Worker 825's
staged follow-up `RationalCuspidalCentralKernelLocalStep` (candidate
`b46ce0f0-0164-4091-b359-d77221dc0431`) removes its convolution-weight
hypothesis. The composition with that step is a later module of Task 7439, after
that module is in the Library.

## Open hypotheses and their owners

This module assumes no same-rank finiteness, no same-rank reconstruction, no
VIII.4.1 target and no dimension bound. Its theorems assume only the laws bundled
in `IsRationalDegreeZeroOperator`, Haar measures, and, for the two VIII.3.2
theorems, the Library's closed VIII.3.2 statement with its structural data.

* **The operator and its six laws.** The actual degree-zero projection
  `degreeZero` and its strictly-smaller-rank inputs: **Task 7277**; global
  well-founded assembly: **Task 3642**. The range, conjugation, check, twist and
  left-convolution laws for `degreeZero`: **Task 7277** (VIII.2.1–VIII.2.3
  targets). The translation law (the source's "relation évidente"
  `°(ρ(g₁)λ(g₂)f) = ρ(g₁)λ(g₂)°f`) is not among Task 7277's listed targets.
  Worker 3642 (Task 3642) has assigned it to **Task 7277** as a supporting
  compatibility. Instantiating `P := degreeZero` and discharging the laws from the
  published targets: **Task 7439**, unit 3, after Task 7277 publishes.
* `RationalCuspidalConjugationIntegrabilityStatement` (Corollary VIII.3.2): its
  statement is in the Library; its proof is owned by **Task 7500**.
* The structural premise `SimultaneousStandardBasisAt i ν K0` of that statement:
  the Library statement `CuspidalSupport.RationalSpecialVertexCompactInputsStatement`
  supplies such a `K0` for every maximal split torus and generic cocharacter. The
  Library derives it from `JointSpecialCompactBasisExistenceStatement`, owned by
  **Task 4169**. Using it in the closed assembly is Task 7439's work.

The closed target `RationalCuspidalCentralProjectionFiniteStatement` is not proved
here. This module is an intermediate unit; Task 7439's completion still requires
that closed theorem.
