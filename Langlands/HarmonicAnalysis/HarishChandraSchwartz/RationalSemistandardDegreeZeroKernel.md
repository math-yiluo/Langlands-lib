# Lemma VIII.2.1 for the degree-zero operator

Lemma VIII.2.1 (printed p. 321) states that \(f\in\mathcal C(G)\) lies in
\({}^\circ\mathcal C(G)=\{{}^\circ f\}\) if and only if \(f^{(P),\mathrm{Ind}}=0\) for every proper
semistandard parabolic \(P\). The proof has two directions. If all these constant terms
vanish, Lemma VII.1.2 gives \(\psi_f[\mathcal O,P]=0\) for \(P\ne G\), so \(f={}^\circ f\). Conversely,
for \(f={}^\circ f'\), Theorem VII.2.5 gives \(\psi_f[\mathcal O,P]=0\) for \(P\ne G\); for a proper
\(P=MU\) and \(g_1,g_2\in G\) the function \(f_M=f^{(P),\mathrm{Ind}}(g_1,g_2)\) on \(M\) has, by
VII.1.2 and the III.6 diagram (printed p. 322),
\[\hat f_M(\omega',P_M)(m_1,m_2)=\delta_P(m_1)^{-1/2}\delta_P(m_2)^{-1/2}\,
\psi_f[\mathcal O',P'](\omega')(m_1g_1,m_2g_2)=0,\qquad P'=P_MU,\]
so all its Fourier components vanish, and formula (2) of VIII.1 for the smaller group \(M\)
gives \(f_M=0\).
[Waldspurger, *La formule de Plancherel pour les groupes p-adiques* (2003),
pp. 321–322](https://doi.org/10.1017/S1474748003000082)

The operator is `rationalSemistandardDegreeZero` of the module `RationalSemistandardDegreeZero`,
\({}^\circ f=f-\kappa(\psi)\), with all of its parameters and inputs. The kernel is the Library's
`rationalCuspidalSubmodule`: for every proper standard parabolic and every Haar measure on its
unipotent radical, the radical integral of every two-sided translate converges absolutely and
vanishes. Its comparison with vanishing of all normalized proper *semistandard* induced constant
terms is the statement `RationalCuspidalSemistandardComparisonStatement` (for a closed matrix
representation), which is a premise here.

## Declarations

| Declaration | Content |
| --- | --- |
| `RationalSemistandardDegreeZeroInverseInput` | VII.2.5 at the operator's data: the Fourier family of \(\kappa(\psi)\) is \(\psi\) in the full product, for every \(\psi\) of the invariant carrier. |
| `rationalSemistandardProperFourier_invariantSynthesis` | Under it, the proper truncation of \(\kappa(\psi)\) is the proper part of \(\psi\). |
| `rationalSemistandardProperFourier_degreeZero` | The image has zero proper Fourier components. |
| `rationalSemistandardDegreeZero_eq_self_iff` | \({}^\circ f=f\) if and only if the proper truncation of \(f\) vanishes. |
| `rationalSemistandardDegreeZero_idem` | Idempotence \({}^\circ({}^\circ f)={}^\circ f\). |
| `rationalSemistandardDegreeZero_mem_range_iff`, `rationalSemistandardDegreeZero_range_eq_ker` | The range is the set of fixed points and the kernel of the proper truncation. |
| `rationalSemistandardDegreeZero_eq_self_of_mem_cuspidal` | The operator is the identity on `rationalCuspidalSubmodule` (VII.1.2 only). |
| `RationalSemistandardDegreeZeroKernelComparison` | The conclusion: range, fixed points, kernel of the truncation and `rationalCuspidalSubmodule` agree. |
| `rationalSemistandardDegreeZeroKernelComparison_of_detection` | The conclusion from the inverse input and the detection equality. |
| `isWeylInvariant_zero`, `fourierInjectivity_of_synthesisReconstruction` | The zero family is Weyl invariant; at fixed data, the form \(\kappa(\psi_f)=f\) of VIII.1 (2) implies that a Schwartz function with zero Fourier family is zero. |
| `RationalStrictlyLowerRankSynthesisReconstructionStatement` | VIII.1 (2) in the form \(\kappa(\psi_f)=f\) for all groups of strictly smaller relative semisimple rank, with `_mono`, `_zero`, `_of_unquotiented` and the proper-Levi specialization `rationalLocalSynthesisReconstruction_properLevi_of_lowerRank`. |
| `RationalSourceFourierData` | Source-normalized Fourier and synthesis data on a group: exactly the data over which the local reconstruction target is quantified, with `SchwartzSpace`, `fourierFamily` and `eq_zero_of_fourier_eq_zero` (the zero case of local reconstruction at these data). |
| `RationalSemistandardLeviFourierData.SourceFourierTransferAt` | The change of normalization on a Levi model for one function: zero Fourier family at the outer-Levi data gives membership of the same function in the source-normalized Schwartz space with zero Fourier family there. |
| `RationalSemistandardLeviFourierData.eq_zero_of_sourceReconstruction` | Local reconstruction on the Levi model, the change of normalization and zero Fourier family at the outer-Levi data give zero. |
| `rationalSemistandardProperFourier_ker_eq_cuspidal_of_lowerRankReconstruction` | Detection, applying strictly lower-rank reconstruction to each \(f^M\). |
| `RationalSemistandardDegreeZeroKernelStatement`, `rationalSemistandardDegreeZeroKernel` | The conditional VIII.2.1 target with all premises, and its proof. |
| `rationalSemistandardDegreeZeroInverseInput_of_synthesisInverse` | The inverse input from `SynthesisInverse.SynthesisInverseStatement`. |
| `rationalSemistandardProperFourier_ker_eq_cuspidal`, `RationalSemistandardLeviFourierData.eq_zero_of_fourier_eq_zero`, `rationalSemistandardProperFourier_ker_eq_cuspidal_of_lowerRankInjectivity` | Auxiliary reduction of detection to injectivity of each Levi Fourier family at the outer-Levi data, and to strictly lower-rank injectivity at arbitrary data. |

## The elementary projector algebra

The algebraic part uses only `RationalSemistandardDegreeZeroInverseInput`, the product form of
the second assertion of VII.2.5 at the data of the operator. The proper truncation is the
actual Fourier family followed by `rationalSemistandardThetaProperPart`, which is idempotent.
Hence the truncation of \(\kappa(\psi)\) is the proper part of \(\psi\), and for the lift
\(\psi\) of \(f\), which is already the truncation of \(\psi_f\), the truncation of
\({}^\circ f=f-\kappa(\psi)\) is zero. If the truncation of \(f\) vanishes, the lift is zero and
\({}^\circ f=f\). These two facts give the fixed-point criterion, idempotence and
`LinearMap.range = LinearMap.ker` of the truncation. With the detection equality
`ker = rationalCuspidalSubmodule`, they give `RationalSemistandardDegreeZeroKernelComparison`.
The detection equality is a separate input; the kernel equality is not used to prove itself.

`rationalSemistandardDegreeZeroInverseInput_of_synthesisInverse` obtains the inverse input from
the VII.2.5 target `SynthesisInverse.SynthesisInverseStatement` and its premises (source compact,
I.1 quotient Haar normalization `SourceLeviQuotientHaar`, nonnegativity and dense positivity of
the density), at the normalization of that target: one compact `K` is the Iwasawa compact of the
Schwartz space, the source compact `K0` and the compact of every packet; the ambient measure is
`RationalDynamicSource.ambientHaar K hKc`, of mass one on `K`; and the cocharacter presentations
are those of `C`. It is `SynthesisInverse.fourier_synthesis` applied to each element of the
carrier.

The identity on the kernel needs neither VII.2.5 nor reconstruction: by
`rationalSemistandardCuspidalProperFourierVanishing` (VII.1.2, with the comparison
`RationalCuspidalSemistandardComparisonStatement`, a closed matrix representation and the VII.1.2
analytic inputs at the proper indices) the truncation of a function in
`rationalCuspidalSubmodule` vanishes.

## Detection and the lower-rank inputs

The detection of zero constant terms uses the Library's outer-Levi data
`RationalSemistandardLeviFourierData` at each proper index: a closed connected reductive model
of the literal Levi with a maximal split torus, an Iwasawa compact, a Haar measure and
split-central quotient Haar measures on it; the actual Schwartz function
\(f^M=f^{(P,\mathrm{Ind})}(g_1,g_2)\) pulled back to the model (`constantTerm`); its full Fourier
family (`fourier`); and the coverage of every inner Fourier component by a proper ambient one
through VII.1.2 on both groups and the III.6 transitivity, with the two factors
\(\delta_P(m_j)^{-1/2}\) and the comparison of the final Levi Haar measures and formal degrees.
From the coverage, `RationalSemistandardLeviFourierData.fourier_constantTerm_eq_zero` gives:
if the proper truncation of \(f\) vanishes, the Fourier family of every \(f^M\) at these
data vanishes. The strict rank decrease of each model is the proved
`semistandardProperLeviRank`.

The source then applies formula (2) of VIII.1 on \(M\) to \(f^M\). Formula (2) is stated
with the normalizations of I.1, which the local target
`FourierInversion.RationalLocalSynthesisReconstructionStatement` (the form
\(\kappa(\psi_f)=f\)) fixes: one special compact `K` serving as source compact, Iwasawa compact,
synthesis compact and compact of every packet, a closed matrix embedding with `K` in its
integral height subgroup, the ambient Haar measure of mass one on `K`, the I.1 quotient Haar
normalizations, and the presentations of the Weyl comparison data. `RationalSourceFourierData`
collects these data on one group. The outer-Levi data of `RationalSemistandardLeviFourierData`
are arbitrary, so the target carries, at every proper index, source-normalized data `s p` on
the same Levi model and the change of normalization
`RationalSemistandardLeviFourierData.SourceFourierTransferAt (c p) (s p) (f^M)` for every
\(f\) and every translating pair: if the Fourier family of \(f^M\) at the outer-Levi data
vanishes, then the same function on \(M(F)\) lies in the Schwartz space at `s p` and its
Fourier family there vanishes. Waldspurger uses on \(M\) the inherited compact \(M\cap K\) and
compatible Haar normalizations (I.1, p. 240), so the source needs no such step. In this module
the two data choices are supplied independently, and `SourceFourierTransferAt` records the
transfer of Schwartz membership and Fourier vanishing for the same function that this requires.
It is an explicit premise here and is not proved in this module. For a change of compact open
subgroup alone, with the same minimal parabolic and the same height, `rationalSchwartzSubmodule_eq` (module
`XiCompactComparison`) gives equality of the underlying Schwartz spaces. That covers only part of
the transfer between the two independently chosen data.

`rationalSemistandardProperFourier_ker_eq_cuspidal_of_lowerRankReconstruction` then runs the
source argument on the actual function \(f^M\). The strictly lower-rank premise
`RationalStrictlyLowerRankSynthesisReconstructionStatement (relativeRootRank i)` specializes to
the Levi model (`rationalLocalSynthesisReconstruction_properLevi_of_lowerRank`) and is
evaluated at `s p` (`RationalSourceFourierData.eq_zero_of_fourier_eq_zero`): the transferred
function has zero Fourier family, so it lies in \(C^\infty(\Theta)_{\mathrm{inv}}\) as the zero
element (it is trivially smooth, finitely supported and Weyl invariant), and
\(f^M=\kappa(0)=0\) (`fourierInjectivity_of_synthesisReconstruction`). Thus \(f^M=0\) as a
function, for every proper index and translating pair, which is membership in
`rationalCuspidalSubmodule` (`rationalCuspidal_of_properLeviConstantTerms_eq_zero`). The converse
inclusion is `rationalSemistandardCuspidalProperFourierVanishing` (VII.1.2).

The strictly lower-rank premises are `FourierInversion.RationalStrictlyLowerRankUnquotientedReconstructionStatement`
(formula (2) with the unquotiented source coefficients) and
`RationalStrictlyLowerRankSynthesisReconstructionStatement` (the form \(\kappa(\psi_f)=f\)); the
first implies the second groupwise (`rationalStrictlyLowerRankSynthesisReconstruction_of_unquotiented`).
Both name only groups of relative semisimple rank strictly below `n`, contain no finiteness
assertion, and are vacuous for `n = 0`; their specializations to the literal proper Levis use
the actual rank comparison. None of these predicates mentions `G` itself, so they fit an
induction on the relative semisimple rank: the step for `G` uses them at `relativeRootRank i`.

The two lower-rank inputs of VIII.2 have separate roles. Strictly lower-rank local finiteness
(`RationalStrictlyLowerRankOrbitFinitenessStatement`, a parameter of the operator) gives the
finite support of the proper truncation and so the construction of \({}^\circ f\); it is not used for
detection. Strictly lower-rank synthesis reconstruction is used only to detect zero constant
terms in the reverse direction of VIII.2.1; it is not used for the construction.

The module also keeps an auxiliary reduction. `rationalSemistandardProperFourier_ker_eq_cuspidal`
takes injectivity of each Levi Fourier family at the outer-Levi data directly, and
`rationalSemistandardProperFourier_ker_eq_cuspidal_of_lowerRankInjectivity` obtains it from
`FourierInversion.RationalStrictlyLowerRankFourierInjectivityStatement`, injectivity for all
groups of strictly smaller rank at arbitrary Fourier data. That premise is not the source's
formula (2), and the target does not use it.

## The target

`RationalSemistandardDegreeZeroKernelStatement` asserts `RationalSemistandardDegreeZeroKernelComparison`
for the operator under the following premises, each an explicit hypothesis:

| Premise | Role | Status |
| --- | --- | --- |
| `RationalSemistandardDegreeZeroInverseInput` | VII.2.5, \(\psi_{\kappa(\psi)}=\psi\), at the operator's data; projector algebra | analytic; obtained from `SynthesisInverse.SynthesisInverseStatement` by `rationalSemistandardDegreeZeroInverseInput_of_synthesisInverse` at the source normalization |
| `RationalCuspidalSemistandardComparisonStatement` | `rationalCuspidalSubmodule` is vanishing of all normalized proper semistandard induced constant terms | named comparison target, not proved here |
| `IsClosedSubgroup rho` | closed matrix representation | structural |
| VII.1.2 analytic inputs at every proper index | zero proper truncation on the kernel, hence the identity there | analytic |
| outer-Levi data `c p` at every proper index | the function \(f^M\), VII.1.2 on both groups, III.6, \(\delta_P^{-1/2}\) factors | analytic data, including the nested coverage |
| source-normalized data `s p` and `SourceFourierTransferAt (c p) (s p) (f^M)` for every \(f\), \(g\) | the change of normalization for \(f^M\) | change of normalization introduced by the formalization (the source uses inherited data), not proved here |
| `RationalStrictlyLowerRankSynthesisReconstructionStatement (relativeRootRank i)` | VIII.1 (2) on groups of strictly smaller rank | the induction hypothesis |

The operator's own parameters (lower-rank finiteness, the support comparisons, smoothness,
VII.1.4 covariance, the synthesis data) are inputs of its construction in
`RationalSemistandardDegreeZero`. `rationalSemistandardDegreeZeroKernel` proves the target from
the projector algebra and the detection; the kernel equality is not among the premises. In
relative rank zero the operator is the identity (`rationalSemistandardDegreeZero_eq_id_of_rank_zero`
in `RationalSemistandardDegreeZero`): every semistandard parabolic is `G`, so there is no proper
index and the Levi premises are vacuous.

## Scope

The field is any nonarchimedean local field with finite residue field, of any characteristic; the
group is any affine locally finite type connected reductive group scheme, with no split or
quasi-split assumption. The field and representation-carrier universes are independent.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après Harish-Chandra)*,
Journal of the Institute of Mathematics of Jussieu 2 (2003), 235–333, Lemma VIII.2.1 and its proof,
printed pp. 321–322 (PDF pp. 87–88); Theorem VII.2.5 and VIII.1 (2), printed p. 320; Lemma VII.1.2,
printed p. 315; the normalizations of I.1, printed p. 240. Registered source
`waldspurger-2003-plancherel`.
[DOI](https://doi.org/10.1017/S1474748003000082)
