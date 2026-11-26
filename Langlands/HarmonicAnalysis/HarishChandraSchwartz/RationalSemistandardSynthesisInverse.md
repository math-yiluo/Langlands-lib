# Waldspurger VII.2.5: the Fourier family inverts the actual synthesis

This module states the second assertion of Theorem VII.2.5 of Waldspurger
(2003), the component identity \(\psi_{\kappa(\psi)}[\mathcal O,P]=\psi[\mathcal O,P]\),
for the Library's actual invariant spectral space, weighted synthesis and full
Fourier family. It proves two equivalent formulations and the elementary
consequences on the image of `κ`. It does not prove the identity.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
registered as `waldspurger-2003-plancherel`. Printed page = PDF page + 234.

- VII.1, printed pp. 313 and 316 / PDF pp. 79 and 82: for \(f\in\mathcal C(G)\),
  \(\hat f(\omega,P)\) is \(d(\omega)\) times the element of
  \(L(\omega,P)\) given by \((I_P^G\omega)(\check f)\), with
  \(\check f(g)=f(g^{-1})\), and \(\psi_f[\mathcal O,P]\) is the family
  \(\omega\mapsto\hat f(\omega,P)\) on the orbit \(\mathcal O\).
- Theorem VII.2.5, printed p. 320 / PDF p. 86: «Pour
  \(\psi\in C^\infty(\Theta)_{\mathrm{inv}}\) et \((\mathcal O,P)\in\Theta\), on a
  l'égalité \(\psi_{\kappa(\psi)}[\mathcal O,P]=\psi[\mathcal O,P]\).» The proof
  cites Propositions VII.2.1, VII.2.2, Corollary VII.2.3 and Lemma VII.1.4.

## The target

All names are in `Langlands.HarishChandraSchwartz.RationalSemistandard` unless
another namespace is written; the declarations of this module are in
`SynthesisInverse`.

`SynthesisInverseStatement hG a ha mu d hindex C Q hK hPK rho` asserts, for every
`ψ` in `rationalSemistandardThetaInvariantSections C`, every full index
`t : RationalSemistandardTheta a ha mu` (a semistandard parabolic with the
unitary unramified orbit `t.2` of discrete series of its literal Levi modulo
the split center) and every actual inducing representative
`A : UnitaryOrbitRepresentative _ (orbitRepresentative … t.2)` of that orbit,

```
rationalSemistandardFourierFamily hG hi hnu hK hPK rho hsw a ha mu d hdelta hT (κ ψ) t A
  = ψ.val.val t A
```

in the actual coefficient fiber of the normalized induced representation at `A`.
Here `κ = GlobalSynthesis.invariantSynthesis hG a ha mu d C.presentation hindex
Q K hK C hi hfin hK hPK rho hmem hnu hspecial hd hQ`, and the Fourier family is
the Library's full product family: at `A` it is
`rationalSemistandardInducedFourierTransform`, the formal degree times the
coefficient tensor of the normalized induced operator at \(\check f\). No
selected inverse replaces it. The source Haar measure
`RationalDynamicSource.ambientHaar K hK` is right invariant by unimodularity
(`sourceHaar_isMulRightInvariant`), as the family requires.

Every unitary point of every orbit is reached: a point \(\omega\) of the orbit is
the class of some `A`, and the components are coherent under every inducing
equivalence and self-twist (`rationalSemistandardFourierFamily_coherent` and
the definition of the smooth sections). The target applies at every full index
`t`, also where `ψ.val.val t = 0`, and does not assume that the Fourier family
of `κ(ψ)` has finite support.

One compact open `K` is used for the Schwartz weights `rationalXi hK hPK`, for
the Haar measure of mass one on `K`, for the source constants and, through the
premises `hd` and `hQ`, for all compact pictures and scalar data, as in the
published VII.2.1–VII.2.3 targets of `WavePacketPairing`. The cocharacter
presentation of each Levi is `C.presentation`, as in
`Association.AssociationFormulaStatement`.

### Premises

Every input is a premise of the proposition, in this order:

| Premise | Content |
| --- | --- |
| `hi`, `hfin`, `hnu`, `hspecial`, `hd`, `hQ`, `hmem` | the inputs consumed by `invariantSynthesis`: maximal split torus, finite nonempty parabolic fibers, generic cocharacter, special compact, common compact for compact pictures and scalar data, and the VI.3.1 `SchwartzMembershipStatement` |
| `hsw : SquareIntegrableWeight (ambientHaar K hK) …` | the `L²` weight condition of Lemma II.1.5, consumed by the Fourier family |
| `hdelta : ∀ p, ModularNormalization p` | the parabolic modular character is the radical's Haar modulus, consumed by the Fourier family |
| `hT` | the normalized induction of every discrete series of every literal Levi modulo its split center has tempered coefficients for the ambient weights, consumed by the Fourier family |
| `IsSourceCompactAt i K` | `K` is the fixer of a special vertex of an apartment of the torus |
| `∀ p, WavePacketPairing.SourceLeviQuotientHaar a mu p` | the quotient Haar of \(M/A_M\) gives the image of \(K\cap M\) mass one (I.1) |
| `GlobalForm.DensityNonnegative …` | the actual density is real and nonnegative (V.2.1) |
| `GlobalForm.DensityPositiveDense …` | the actual density has positive real part on a dense subset of every orbit |

The density may vanish; no everywhere positivity of the density is a premise.
No premise asserts the inverse identity, the isometry, positivity of the form,
finite Fourier support or a closure property, and the data `C` and `Q` contain
none of these. Irreducibility of tempered parabolic induction is not assumed;
the only irreducibility in the data is the generic one of `OrbitPacketData`,
on a nonempty open set of unramified characters. The setting has the
generality of the dependencies: arbitrary nonarchimedean local fields of any
characteristic, affine locally finite type connected reductive group schemes
of any rank, independent universes `u` and `uV`, the canonical rational-point
topology and complex `SmoothRep`s.

## Equivalent formulations

| Declaration | Content and proof |
| --- | --- |
| `SynthesisInverseProductStatement` | The same premises, concluding `Fourier (κ ψ) = rationalSemistandardThetaInvariantInclusion C ψ` in the full dependent product `RationalSemistandardThetaSections a ha mu`. |
| `synthesisInverse_iff_product` | Equivalence with the pointwise target, by function extensionality in `t` and `A`. |
| `SynthesisInverseTransportStatement` | The same premises, concluding for every full index `t` and every actual square-integrable `π'` whose class lies in `t.2` that the raw Fourier orbit section `rationalSemistandardFourierOrbit` of `κ(ψ)` based at `π'` is `orbitSectionsBaseEquiv … π' … (ψ.val.val t)`. |
| `synthesisInverse_iff_transport` | Equivalence with the pointwise target. Forward: `rationalSemistandardFourierFamily_baseChange` identifies the base change of the family component with the raw section at `π'`. Backward: take `π'` the chosen representative of `t.2` and use injectivity of the linear equivalence `orbitSectionsBaseEquiv`. |

## Consequences on the image of `κ`

The declarations of the section `Consequences` take the inputs and the premises
as hypotheses, together with `h : SynthesisInverseStatement …`. They are
derived from this target alone.

| Declaration | Content and proof |
| --- | --- |
| `fourier_synthesis` | The product identity at the given inputs. |
| `fourier_synthesis_eq_zero` | Where `ψ.val.val t = 0`, the Fourier component of `κ(ψ)` at `t` is zero. |
| `fourier_mem_smooth_of_mem_range` | For `f ∈ LinearMap.range κ`, the Fourier family of `f` lies in the smooth finite-support carrier `rationalSemistandardThetaSmoothSections a ha mu d`: it equals the family of some `ψ`. |
| `fourier_support_finite_of_mem_range` | For `f ∈ LinearMap.range κ`, `rationalSemistandardThetaSupport a ha mu (Fourier f)` is finite. |
| `fourier_mem_invariant_of_mem_range` | For `f ∈ LinearMap.range κ`, the Fourier family of `f` lies in the invariant carrier: it satisfies `IsWeylInvariant C`. |
| `fourierOnRange` | The Fourier family restricted to `LinearMap.range κ`, as a complex-linear map to the invariant carrier. Its membership witnesses are the two preceding theorems, hence come from `SynthesisInverseStatement`. |
| `inclusion_fourierOnRange` | Comparison with the product identity: the inclusion of `fourierOnRange f` into the product is the Fourier family of `f`, by reflexivity. |
| `fourierOnRange_rangeRestrict`, `synthesis_fourierOnRange` | `fourierOnRange` is inverse to `κ` on both sides, as a map onto the range. |
| `invariantSynthesis_injective` | `κ` is injective, from the product identity and injectivity of `rationalSemistandardThetaInvariantInclusion`. |
| `synthesisRangeEquiv`, `synthesisRangeEquiv_symm_apply` | The linear equivalence of the invariant carrier with `LinearMap.range κ` given by `κ`, whose inverse is `fourierOnRange`. |

Finite support is asserted only for Fourier families of elements of the image
of `κ`. This module asserts no finite Fourier support for a general Schwartz
function, no surjectivity of `κ` onto the Schwartz space and no VIII.1 inversion.

## Proof of the target: source route and Library statements

This module states the identity and does not prove it. By linearity the
Fourier family of \(\kappa(\psi)\) is the finite sum, over the support of
\(\psi\), of the source coefficient times the Fourier family of the packet
\(f_{\psi[\mathcal O,P]}\). Corollary VII.2.3 removes the components at indices
whose Levi is not conjugate to that of the packet. At the indices with the same
parabolic, Proposition VII.2.1 gives
\(\hat f_\psi(\omega',P)=\gamma(G\mid M)c(G\mid M)^2\sum_{s}{}^\circ c_{P\mid P}(s,s^{-1}\omega')\psi_{s^{-1}\omega'}\);
Lemma VII.1.4 transfers the computation to the other parabolics with a
conjugate Levi. Invariance of \(\psi\) under the normalized comparisons and the
count of Weyl elements and parabolics give \(\psi[\mathcal O,P]\). The
corresponding statements in the Library, namespace `WavePacketPairing`, are:

| Source | Library statement |
| --- | --- |
| Proposition VII.2.1 | `FourierWeylSumStatement` |
| Proposition VII.2.2 (i), (ii) | `NonconjugatePairingStatement`, `ConjugatePairingStatement` |
| Corollary VII.2.3 | `PointwiseVanishingStatement`, `ComponentVanishingStatement`; `componentVanishing_of_nonconjugatePairing` derives the latter from VII.2.2(i) with `DensityNonnegative`, `DensityPositiveDense`, `OrbitProductIntegrabilityStatement` and Fourier smoothness |
| Lemma VII.1.4 | the covariance \(\psi_f[s\mathcal O,P'](s\omega)={}^\circ c_{P'\mid P}(s,\omega)\psi_f[\mathcal O,P](\omega)\) of `rationalSemistandardFourierFamily`; this module imports no statement of it |

Those statements carry premises that are not premises here: a Levi
normalization with `LeviNormalizationMatches` and `OrbitWeylDescentStatement`
for `FourierWeylSumStatement`, and `ComponentSchwartzMembershipStatement`,
which follows from `hmem` because the synthesis of a family supported at one
index is the packet times the positive source coefficient. A proof
along this route also needs the comparison of the sections
`normalizedWeylSection` of `FourierWeylSumStatement` with the comparison
`C.fiberComparison` defining the invariant carrier, the smoothness of the
Fourier components (`RationalSemistandardFourierFamilySmoothnessStatement`)
where VII.2.3 is derived by detection, and the common-Levi source constants and
Weyl counting used in `Association.associationFormula_of_transport`.
