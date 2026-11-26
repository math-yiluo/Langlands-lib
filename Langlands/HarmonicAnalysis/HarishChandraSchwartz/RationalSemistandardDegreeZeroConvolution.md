# Lemma VIII.2.3 for the degree-zero operator

Lemma VIII.2.3 (printed p. 322) states that for \(f_1\in{}^\circ\mathcal C(G)\) and
\(f_2\in\mathcal C(G)\),
\[f_1*f_2=f_1*{}^\circ f_2,\qquad f_2*f_1={}^\circ f_2*f_1 .\]
Its proof reduces both identities to \(f_1*f_\psi=f_\psi*f_1=0\) for every
\((\mathcal O,P)\in\Theta\) with \(P\ne G\) and every \(\psi\in C^\infty(\mathcal O,P)\).
For \(g\in G\) set \(f_1'(h)=\overline{f_1(gh^{-1})}\). Then
\((f_1*f_\psi)(g)=(f_1',f_\psi)_G\) in the conjugate-first convention of the source and
of the Library: the conjugation in the pairing cancels the conjugation in \(f_1'\). VII.2 (1)
expresses this pairing through the Fourier component of \(f_1'\) at \((\mathcal O,P)\),
which vanishes because \(f_1'\in{}^\circ\mathcal C(G)\) (Lemma VIII.2.1). The second
convolution uses the test \(h\mapsto\overline{f_1(h^{-1}g)}\) in the same way.
[Waldspurger, *La formule de Plancherel pour les groupes p-adiques* (2003),
p. 322](https://doi.org/10.1017/S1474748003000082)

Here \(f_1\) ranges over the Library's kernel `rationalCuspidalSubmodule`, not over the
range of the operator. That submodule is the integrable proper-standard presentation: for
every proper standard parabolic and every Haar measure on its unipotent radical, the
radical integral of every two-sided translate of \(f_1\) converges absolutely and vanishes.
The identification of the range of the operator with vanishing of all proper semistandard
induced constant terms is Lemma VIII.2.1 of the source, which is not used here; the
comparison of that semistandard condition with `rationalCuspidalSubmodule` is the
separate statement `RationalCuspidalSemistandardComparisonStatement`. The operator is
`rationalSemistandardDegreeZero` of the module `RationalSemistandardDegreeZero`,
\({}^\circ f=f-\kappa(\psi)\), with all of its parameters and inputs. The convolution is the
Library's `Space.convolution hw` on the actual rational Schwartz space, for an ambient
Haar measure `muG`, right invariant and s-finite; `hw : ConvolutionWeights …` supplies
the absolute integrability and the Schwartz membership of convolutions. The same `muG`
is the ambient measure of the Fourier family that defines the operator.

## Declarations

| Declaration | Content |
| --- | --- |
| `RationalSemistandardDegreeZeroConvolutionStatement` | Both identities for cuspidal \(f_1\) and arbitrary \(f_2\), from VI.3.1 component continuity and the proper-packet vanishing. |
| `rationalSemistandardDegreeZero_convolution` | Proof of that statement. |
| `rationalSemistandardDegreeZero_leftConvolutionLaw` | The law `RationalDegreeZeroLeftConvolutionLaw` of `RationalCuspidalUnit` for the operator, under the same premises. |
| `RationalSemistandardDegreeZeroConvolutionFromFourierStatement` | Both identities, with the packet vanishing replaced by its VII.2 (1)/VII.1.2 inputs. |
| `rationalSemistandardDegreeZero_convolution_of_fourier` | Proof of that statement. |

## Premises

`RationalSemistandardDegreeZeroConvolutionStatement` has two premises:

- `GlobalSynthesis.ComponentContinuityStatement` (VI.3.1): each packet map at each index
  lifts to a continuous map into the Schwartz space with the same values, so that the
  finite sum \(\kappa(\psi)\) is a finite sum of Schwartz functions;
- `GlobalSynthesis.ProperPacketConvolutionVanishingStatement`: for every `f` in
  `rationalCuspidalSubmodule`, every proper semistandard index and every smooth section `v` of its
  component, both raw convolutions of `f` with the actual packet
  `GlobalSynthesis.componentPacket … v`, for `muG`, are zero.

`RationalSemistandardDegreeZeroConvolutionFromFourierStatement` replaces the second
premise by the inputs of the Library's `GlobalSynthesis.properPacketConvolutionFromFourier`:
the statement `RationalCuspidalSemistandardComparisonStatement`, which identifies, for a
closed matrix representation, membership in the proper-standard kernel
`rationalCuspidalSubmodule` with vanishing of all normalized proper semistandard induced
constant terms; the closedness `IsClosedSubgroup rho` of the matrix representation;
the VII.1.2 analytic inputs at each proper index (with a Haar radical measure), VII.1.3
component smoothness of the Fourier family at every index, and the product integrability
`GlobalSynthesis.ProperPacketConvolutionIntegrabilityStatement` of the VII.2 (1) pairing for
both tests \(h\mapsto\overline{f_1(gh^{-1})}\) and \(h\mapsto\overline{f_1(h^{-1}g)}\). The
ambient measure is then also inversion invariant. These are the VII.2 and VII.1.2
dependencies of the packet vanishing; no standard-parabolic result is used for the
semistandard indices.

## Proof

The lift \(\psi\) of \(f_2\) is supported in the proper part \(\Theta-\Theta_G\)
(`rationalSemistandardProperFourierInvariant_support_subset`), and
\({}^\circ f_2=f_2-\kappa(\psi)\), where \(\kappa\) on the invariant carrier is the restriction of
`GlobalSynthesis.schwartzSynthesis`. The Library's `GlobalSynthesis.properSynthesisConvolution`
proves, for every smooth finite-support family supported in the proper part, both
identities with \(f_2-\kappa(v)\) in place of \({}^\circ f_2\): it writes \(\kappa(v)\) as the
finite weighted sum of the Schwartz lifts of its packets and uses linearity of the
convolution in each argument, so that no interchange of integrals is needed. Applying it to
the lift gives the statement. The left law is the first identity evaluated at a point. The
version from Fourier composes this with `GlobalSynthesis.properPacketConvolutionFromFourier`,
which proves the packet vanishing from its inputs.

## Scope

The field is any nonarchimedean local field with finite residue field, of any
characteristic; the group is any affine locally finite type connected reductive group
scheme, with no split or quasi-split assumption, including relative rank zero, where the
operator is the identity and both identities are trivial. The field and representation-carrier
universes are independent.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, Journal of the Institute of Mathematics of Jussieu 2 (2003), 235–333,
Lemma VIII.2.3 and its proof, printed p. 322 (PDF p. 88); VII.2 (1), printed p. 319;
Lemma VII.1.2, printed p. 315. Registered source `waldspurger-2003-plancherel`.
[DOI](https://doi.org/10.1017/S1474748003000082)
