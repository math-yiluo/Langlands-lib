# Čech–de Rham pullback for a morphism on a square-zero reduction

## The reduction

Let \(f\colon X\to\operatorname{Spec}R\) and \(I\subseteq R\) be an ideal.
`quotientBaseMap I` is the closed immersion
\(\operatorname{Spec}(R/I)\to\operatorname{Spec}R\) and
`quotientReduction f I` is the actual fibre product
\(X_{R/I}=X\times_{\operatorname{Spec}R}\operatorname{Spec}(R/I)\), with
first projection `quotientReductionMap f I` \(r\colon X_{R/I}\to X\), a
closed immersion by base change. When \(I^2=0\) the ideal lies in the
nilradical, so the quotient spectrum map is bijective on points;
`quotientReductionMap_surjective` deduces by base change that \(r\) is
surjective. `quotientReductionMap_appLE` shows, for an affine open \(W\) of
\(X\), that the actual map on sections
\(\Gamma(X,W)\to\Gamma(X_{R/I},r^{-1}W)\) is surjective with kernel
\(I\,\Gamma(X,W)\). It uses the affine section comparison for Cartesian
squares, `surjective_and_ker_app`.

## Local lifts

Let \(g\colon Y\to\operatorname{Spec}R\) be smooth, \(I^2=0\), and
\(m\colon X_{R/I}\to Y\) a morphism with \(g\circ m=f\circ r\) over
\(\operatorname{Spec}R\). By the Cartesian property such an \(m\) is the
same as a morphism \(X_{R/I}\to Y_{R/I}\) over \(R/I\).
`exists_lift_on_affineOpen` gives, for every affine open \(W\subseteq X\),
a morphism \(\ell\colon W\to Y\) over \(\operatorname{Spec}R\) whose
restriction to \(r^{-1}W\) is \(m\). Both \(W\) and \(r^{-1}W\) are
affine, and after identifying them with the spectra of their global
section rings the section map is surjective with square-zero kernel. The
lift is then supplied by `smoothThickeningLifting`.

Let \(U\) and \(V\) be affine open covers of \(X\) and \(Y\), and let
\(\beta\) map the indices of \(U\) to those of \(V\) with
\(r^{-1}U_i\subseteq m^{-1}V_{\beta(i)}\) for every \(i\). For separated
\(f\), `localPullbacksOfReduction` chooses a lift on every chart \(U_i\)
and passes to the system of section pullbacks
`LocalPullbacks.ofLocalMorphisms`. On a tuple intersection \(U_\tau\) and a
vertex \(i\) of \(\tau\), the pullback \(s^\tau_i\colon
\Gamma(Y,V_{\beta\tau})\to\Gamma(X,U_\tau)\) is the section map of the lift
chosen on \(U_{\tau(i)}\). Two vertices give pullbacks agreeing modulo
\(I\,\Gamma(X,U_\tau)\), because both reduce to the section map of \(m\).
`localPullbacksOfReduction_reduce_sections` computes this reduced section
map on each tuple intersection.

## The degree-one map

For smooth separated \(f\) and \(g\) and finite covers,
`reductionPullbackH1` is the \(R\)-linear map
\(H^1_{\mathrm{dR}}(Y/R)\to H^1_{\mathrm{dR}}(X/R)\) between the modules
`H1 g V` and `H1 f U` of the module `AffineCechDeRham`. It is
`LocalPullbacks.pullbackH1` for the chosen system. On a degree-one
cocycle \((a,b)\) for \(V\) it is the class of \((a',b')\), where
\[
b'_i=(s^{(i)}_0)^{*}b_{\beta(i)},\qquad
a'_{ij}=s^{(ij)}_0\bigl(a_{\beta(i)\beta(j)}\bigr)
+\iota_{s^{(ij)}_1-s^{(ij)}_0}\bigl(b_{\beta(j)}|_{V_{\beta(i)\beta(j)}}\bigr).
\]
Here \(s^{(ij)}_0\) and \(s^{(ij)}_1\) are the pullbacks to \(U_i\cap U_j\)
through the lifts on \(U_i\) and on \(U_j\). The contraction
\(\iota_\delta\) of the module `AffineCechDeRhamSquareZeroHomotopy` sends
\(c\,dx\) to \(s^{(ij)}_1(c)\,\bigl(s^{(ij)}_1(x)-s^{(ij)}_0(x)\bigr)\).
The Library's complex uses \((\partial b)_{ij}=b_j-b_i\) and the total
differential \((a,b)\mapsto(\partial a,\partial b-da,db)\).
The module `AffineCechDeRhamSquareZeroPullback` verifies, for this
convention, that the corrected cochain of a cocycle is a cocycle and that
a total boundary goes to the total boundary of the pulled-back function.

## Choices of lifts and the Hodge step

The covers and \(\beta\) are fixed. For any family of lifts \(\ell_i\) of
\(m\) on the charts \(U_i\), `reductionPullbackH1_eq_of_localMorphisms`
identifies `reductionPullbackH1` with the map induced by that family.
`pullbackH1_ofLocalMorphisms_eq` states that two arbitrary families
induce the same map. Section pullbacks from two families on the same
intersection agree modulo the extended ideal. Hence
`LocalPullbacks.pullbackH1_eq_of_congruent` applies: the two corrected
cocycles differ by the total boundary of the contractions of the original
one-forms.

Suppose \(m\) lifts to \(\gamma\colon X\to Y\) over
\(\operatorname{Spec}R\) with \(\gamma\circ r=m\). Surjectivity of \(r\)
gives \(U_i\subseteq\gamma^{-1}V_{\beta(i)}\). The section maps of
\(\gamma\) are congruent to the local pullbacks, so the induced map agrees
with that of `LocalPullbacks.ofMorphism`. All vertices of that system
give the same map, so the overlap contractions vanish. A class
\((0,b)\) with \(b\) closed thus goes to the class of a compatible closed
form. `reductionPullbackH1_maps_hodgeF1_of_lift` concludes that
`hodgeF1 g V` maps into `hodgeF1 f U`.

The file fixes the covers. It contains no comparison between different
compatible covers. It also does not compare the map with the pullback on
the cohomology of the reductions.

## Source correspondence

In Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura
varieties*, revised 14 March 2021, the proof of Proposition 2.1.6.4 on
printed pp. 133–135 (PDF pp. 161–163) constructs the map from lifts
\(\tilde f_\alpha\) on affine charts with \(f(U_\alpha)\subseteq V_\alpha\).
The differential on \(C^1\) is
\((\partial y^{(1,0)},-dy^{(1,0)}+\partial y^{(0,1)},dy^{(0,1)})\), and
Lan's correction is
\(x^{(1,0)}_{\alpha\beta}=\tilde f^*_\alpha(y^{(1,0)}_{\alpha\beta})
+T_{\alpha\beta}(y^{(0,1)}_\beta)\), where
\(T_{\alpha\beta}\circ d=\tilde f^*_\alpha-\tilde f^*_\beta\).
On printed p. 129 Lan defines \(\partial\) as the alternating sum, as the
Library does. The verification on printed p. 134 instead expands the
degree-zero differential as \((\partial y)_{\alpha\beta}=y_\alpha-y_\beta\),
the opposite sign; its degree-one differential is the alternating sum.
The map \((a,b)\mapsto(-a,b)\) carries the Library's degree-one cocycles
and boundaries to those of the p. 134 verification. It carries the formula
above to Lan's formula, because \(-\iota_{s_1-s_0}=\iota_{s_0-s_1}\) for
congruent pullbacks. With the alternating-sum convention of p. 129 the
contraction must be taken against \(s_1-s_0\), as it is here.
Independence of the lifts corresponds to Lan's remark on printed p. 135
that modifying \(T\) by a coboundary does not change the map.

The Hodge statement for a global lift is derived. With a global lift the
corrected map is the pullback along \(\gamma\), which preserves the
summand \(C^{0,1}\) defining the first step of (2.1.6.5) on printed p. 135.
The retained source is `lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
