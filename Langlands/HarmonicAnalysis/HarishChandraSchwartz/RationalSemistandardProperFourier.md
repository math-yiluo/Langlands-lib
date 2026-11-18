# The actual proper Fourier truncation

Waldspurger introduces the family \(\psi\) at the start of VIII.2, on
p. 321. It equals \(\psi_f[\mathcal O,P]\) for \(P\ne G\) and is zero
for \(P=G\). The reference at that point to Remark VII.1.3 refers to
Remark VIII.1.3, on the same page. The ambient index is the full
semistandard \(\Theta\) of §VII.1, and the cutoff uses equality of the
actual parabolic subgroup functor with the whole group. The field and
representation-carrier universes are independent. [Waldspurger, *La
formule de Plancherel pour les groupes p-adiques* (2003), pp. 316–317,
321](https://doi.org/10.1017/S1474748003000082)

`rationalSemistandardProperFourier` composes
`rationalSemistandardFourierFamily` with
`rationalSemistandardThetaProperPart`. Both are complex-linear on the
actual rational-point spaces, so the composition is complex-linear.
The component lemmas give precisely the two source branches. On the
proper branch `rationalSemistandardFourierFamily_apply` evaluates the
component as the existing induced Fourier tensor. The support
identity takes the intersection with the proper part of \(\Theta\),
and the zero criterion is vanishing at every proper component.

The representative change through `orbitSectionsBaseEquiv` uses
the full Fourier base-change theorem on each proper component.
Linearity of the equivalence gives the zero branch. Likewise, the
full coherence theorem supplies the comparison under every inducing
equivalence and self-twist on the proper branch, with the same
inversion-invariance hypothesis on the ambient measure. The zero
component lies in the coherent submodule. The actual \(G\times G\)
action on the raw product acts inside each fiber. The translation
theorem uses VII.1.1(i) for the full family and linearity on the
group branch.

`RationalStrictlyLowerRankProperFourierFiniteSupportStatement` states
finite support of this raw truncation. Its proof specializes
`RationalStrictlyLowerRankOrbitFinitenessStatement` by
`properLeviOrbitFiniteness_of_strictlyLowerRank`, then applies
`finite_rationalProperSemistandardThetaFixed` and
`rationalProperSemistandardFourierFiniteSupport_of_fixedFinite`.
The latter uses the published Fourier support inclusion. Geometric
index finiteness, the proper normal-level fixed-vector implication
and the exact proper-Levi rank comparison remain explicit premises.
The finiteness input concerns ranks strictly below
`relativeRootRank i`. At rank zero the exact rank comparison forces
every parabolic in the index to be \(G\), so the raw truncation
is the zero linear map.

`rationalSemistandardProperFourierSmooth` uses the existing
`rationalSemistandardFourierThetaProperSmoothFamily` with this
proper-only support result and the full component smoothness
target on the supplied component analytic inputs. Its value in the
raw product is definitionally the truncation. The Schwartz
construction uses the published actual compact pictures, modular
normalizations, square-integrable weights and tempered-coefficient
assumptions. The conclusions here are in the raw product and in the
finite-support smooth submodule. The VIII.2 invariant lift uses
VII.1.4 and the comparisons across parabolics. Lower-rank
synthesis reconstruction enters the subsequent VIII.2.1 detection
argument.
