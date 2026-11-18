# Vanishing of proper Fourier components on the intrinsic cuspidal kernel

The first implication of Waldspurger VIII.2.1 starts from vanishing
of the induced constant terms along all proper semistandard
parabolics. VII.1.2 then makes each proper Fourier component zero.
The index here is the actual full semistandard \(\Theta\) with
independent field and representation-carrier universes. [Waldspurger,
*La formule de Plancherel pour les groupes p-adiques* (2003), pp.
315, 321](https://doi.org/10.1017/S1474748003000082)

`rationalSemistandardFourierFamily_apply_eq_zero_of_constantTermsVanish`
proves the component statement under
`RationalSemistandardConstantTermsVanish`. At each representative
of the unitary orbit, `rationalSemistandardFourierFamily_apply`
identifies the component's value with the actual induced Fourier
tensor. The published
`inducedFourierTransform_eq_zero_of_constantTermInd_eq_zero`
applies to this tensor with the supplied Levi and radical measures.
Two-sided invariance, measure normalizations, compact
factorization, constant term estimates and double integrability
come from `RationalSemistandardFourierAnalyticInputs`. The radical Haar
hypothesis lets us specialize normalized constant-term vanishing at
that measure. The Schwartz-valued constant term in VII.1.2 uses
the same underlying normalized function as the vanishing premise.

`RationalSemistandardCuspidalProperFourierVanishingStatement` uses
the existing `rationalCuspidalSubmodule`. This is the integrable
standard-parabolic presentation of the intrinsic kernel. The
published `RationalCuspidalSemistandardComparisonStatement`, under
the closed matrix model hypothesis, gives the full semistandard
vanishing condition consumed by the component theorem. This
contribution concerns the forward implication. The proof uses
VII.1.2 locally at each proper index, independently of global
Fourier support and lower-rank reconstruction.
