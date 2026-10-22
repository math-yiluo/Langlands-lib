# Weil–Deligne pair L-factors and the reflected L-ratio

This module constructs pair L-factors from the actual tensor product of
Weil–Deligne representations and the reflected quotient
\[
  R_{A,c}(X)=\frac{L(A^\vee,c/X)}{L(A,X)}.
\]
It supplies a rational function, proves intrinsic invariance, and gives
unit-valued evaluations on the common regular domain. The coefficient
field \(K\), group \(G\), norm character \(\nu:G\to K^\times\), normal
subgroup \(I\), and element \(g\in G\) are explicit inputs. Coefficient,
group, and carrier universes are independent. No topology, semisimplicity,
or characteristic-zero assumption is needed for the algebraic part.

## Reciprocal substitution

`Langlands.LocalFactor.RationalReflection.reflectedVariable c` is
\(c/X\in K(X)\), with \(c\in K^\times\). The proof
`variable_transcendental` shows that it is transcendental: algebraicity
of \(c/X\) would imply algebraicity of \(c(c/X)^{-1}=X\), contradicting
the transcendence of the rational-function variable.

`subst c` uses `RatFunc.liftAlgHom` to extend polynomial evaluation at
\(c/X\) to an actual \(K\)-algebra homomorphism of \(K(X)\).
`subst_polynomial` proves that it agrees with polynomial evaluation.
`subst_X` and `subst_variable` show that it exchanges \(X\) and \(c/X\).
`subst_subst` proves the involution on a numerator/denominator
presentation, using compatibility of algebra evaluation with an
algebra homomorphism. `equiv c` packages this as an algebra
automorphism with itself as inverse. This also ensures that substitution
preserves nonzero rational functions.

## Actual tensor, dual, and rational factors

Write
\[
  P_A(X)=\det(1-Xr_A(g)\mid(\ker N_A)^I),\qquad L(A,X)=P_A(X)^{-1}.
\]
These are the published `eulerPolynomial` and `rationalLFactor` in
`Langlands.LocalFactor.WeilDeligne`.

`pairLFactor A B I g` is `rationalLFactor` of
`WeilDeligneRepresentation.tensor A B`. In particular it uses the
actual tensor carrier, diagonal group action, and monodromy
\(N_A\otimes 1+1\otimes N_B\). Its Euler operator acts on the
inertia-fixed kernel of that full monodromy. The construction does not
replace this space by a tensor product of separate kernels.

`reflectedDualLFactor` applies `subst c` to the L-factor of the
published actual dual. That dual has the inverse-element dual action
and monodromy \(-N_A^{\mathsf t}\).
`rationalLRatio` divides this reflected factor by the original factor.
The three nonvanishing lemmas use the published nonvanishing of
`rationalLFactor`, preservation of nonzero elements by the substitution,
and nonvanishing of a quotient.

`rationalLRatio_eq` proves the exact identity
\[
  R_{A,c}(X)=\frac{P_A(X)}{P_{A^\vee}(c/X)}.
\]
The proof unfolds the two reciprocals, moves inversion through the
algebra homomorphism, applies `subst_polynomial`, and uses
`inv_div_inv`.

`pairLFactor_eq_of_equiv` applies the published `tensorEquiv` and
L-factor invariance. Each tensor leg allows its own carrier universe;
the two equivalent representatives within a leg have the same universe,
as required by `tensorEquiv`. `rationalLRatio_eq_of_equiv` allows
independent source and target carrier universes and applies
`dualEquiv` together with L-factor invariance. `pairLFactorClass`
and `rationalLRatioClass` descend these constructions to the genuine
pair-isomorphism classes. Their `classOf` formulas are definitional.
`rationalLRatio_eq_of_coset` proves invariance under replacing \(g\)
by \(h\) with \(hg^{-1}\in I\), using that property of each L-factor.

## Regular values and the spectral reflection

`LRatioRegularPoint A I g c` consists of \(z\in K^\times\) such that
\(P_A(z)\ne0\) and \(P_{A^\vee}(c/z)\ne0\). On this domain,
`regularLRatioValue` is the quotient of the two published regular
L-values, with codomain \(K^\times\). `regularLRatioValue_eq` proves
that its underlying scalar is
\[
  \frac{P_A(z)}{P_{A^\vee}(c/z)}.
\]
This explicitly evaluates the same numerator and denominator as
`rationalLRatio_eq`; no general `RatFunc.eval` comparison theorem is
asserted here. The domain intentionally requires both individual
L-factors to be regular. It is not claimed to be the largest domain of
the ratio after cancellation. No value is assigned at either individual
pole or at \(z=0\).

For \(K=\mathbf C\) and \(q>0\), the published `spectralParameter`
is the unit \(\exp(-s\log q)=q^{-s}\).
`reflectionScale q hq` is its value at \(1\), and
`coe_reflectionScale` proves that it equals \(q^{-1}\).
`spectralParameter_one_sub` proves the unit identity
\[
  q^{-(1-s)}=\frac{q^{-1}}{q^{-s}}
\]
by reducing to `Complex.exp_sub` and the equality of the exponents.

`SpectralLRatioRegularPoint` requires nonvanishing of the Euler
denominators at \(q^{-s}\) for \(A\) and at \(q^{-(1-s)}\) for
\(A^\vee\). Its `toRegular` map uses the spectral identity.
`spectralLRatioValue` is the actual quotient
\(L(1-s,A^\vee)/L(s,A)\) on this domain, and
`spectralLRatioValue_eq_regular` identifies it with the regular
rational-expression value. The proof unfolds the evaluations and
rewrites the spectral identity; proof fields disappear by proof
irrelevance. `pairSpectralLValue` applies the published spectral
evaluation to the actual tensor pair, with its own regular-domain proof.

## Sources, provenance, and scope

The registered source is John Tate, “Number theoretic background,”
in the Corvallis proceedings (1979), Part II, literature ID
`tate-1979-number-theoretic-background`, SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The original pages were read directly.

Tate §§4.1.1–4.1.5, printed p.20 / PDF p.29, provide the
Weil–Deligne action and tensor monodromy; the negative-transpose dual
is derived from dualizing that action, as documented in the imported
`Langlands.WeilDeligne.Dual`. Section 4.1.6, printed p.21 / PDF p.30,
gives the Euler reciprocal on the inertia-fixed monodromy kernel.
Sections 3.5.1–3.5.4, printed p.16 / PDF p.25, provide the spectral
twist and the dual \(1-s\) convention in a global functional-equation
setting. They are not cited as a proof of a local gamma-factor theorem.

The reflected ratio and rational substitution automorphism are derived
algebraic constructions from these conventions. The safe evaluation
domains, quotient descent, and their proofs are implementation
obligations. The direct project imports are
`Langlands.LocalFactor.WeilDeligne`, `Langlands.WeilDeligne.Dual`,
and `Langlands.WeilDeligne.SumsTensor`; their actual constructions are
reused without changes.

A local-field specialization must supply \(q=\#k_F\), actual inertia,
and geometric Frobenius \(\Phi\) satisfying \(\nu(\Phi)=q^{-1}\).
This generic module neither chooses those inputs nor proves their
existence. It constructs the L-ratio needed for a gamma factor, but
supplies no epsilon system, full gamma factor, local functional
equation, or epsilon existence theorem. The quotient determinant
correction remains in the imported WD factor framework and is not
silently absorbed into this L-ratio.
