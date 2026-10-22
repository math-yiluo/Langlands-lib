# Weil–Deligne invariant quotient and local-factor constructions

`Langlands.LocalFactor.WeilDeligne` constructs the actual quotient
\(Q=V^I/(\ker N)^I\), its induced action, and the determinant correction.
It uses the parameter owner's `WeilDeligneRepresentation` and
`inertiaKernelRepresentation`. Coefficients range over a field, the group
is arbitrary, and the coefficient, group and carrier universes are
independent. A normal subgroup \(I\) and an element \(g\) are explicit.
The spectral-value section specializes only the coefficient field to
\(\mathbf C\).

## Actual subquotient and conductor correction

`inertiaRepresentation` is the representation on the actual subspace
\(V^I\). `kernelInInvariants` is the inverse image of \(\ker N\) under
the inclusion \(V^I\hookrightarrow V\). Its membership theorem says
exactly \(Nv=0\). `kernelInInvariants_stable` uses the parameter owner's
proved monodromy-kernel stability, derived from covariance. The ambient
action on \(V^I\) comes from normality. These facts construct
`quotientRepresentation` using Mathlib's quotient action and prove that
`quotientProjection` is an intertwiner.

`kernelInInvariantsEquiv` reorders the two subtype conditions to give
an explicit linear equivalence with the parameter owner's
`inertiaKernelRepresentation I A`. The quotient dimension
`conductorCorrection` therefore satisfies both
\[
 \dim Q+\dim(\ker N)^I=\dim V^I,\qquad
 \dim Q=\dim V^I-\dim(\ker N)^I.
\]
The first equality follows from quotient rank–nullity and the explicit
equivalence; it also justifies the natural-number subtraction in the
second equality. This is the monodromy correction. The ordinary Artin
conductor is not redefined or supplied as an unexplained scalar here.

## Euler factor and quotient determinant

`kernelOperator` is the action of \(g\) on the actual
\((\ker N)^I\). `eulerPolynomial` is its basis-independent
\(\det(1-Xg\mid(\ker N)^I)\), reusing `Langlands.LocalFactor.Euler`.
Its constant coefficient is proved to be one. `rationalLFactor` is the
reciprocal in `RatFunc K`, and is nonzero.

`regularLValue` takes a `RegularPoint` whose denominator is nonzero,
and its determinant formula is proved. With positive real input \(q\),
`spectralLValue` evaluates at
\(\exp(-s\log q)=q^{-s}\), only on `SpectralRegularPoint`.
There is no everywhere-finite complex-valued L-function at the poles.

`quotientOperator` is the induced action on \(Q\).
`quotientDeterminant` is \(\det(-g\mid Q)\). It is nonzero: the negative
operators for \(g\) and \(g^{-1}\) multiply to the identity, so their
determinants multiply to one. `quotientConstantCorrection` packages
this proved nonzero value as a unit.

`quotientCorrectionPolynomial` is the monomial
\[
 C_{A,I,g}(X)=\det(-g\mid Q)\,X^{\dim Q}.
\]
Its evaluation theorem proves, for every scalar \(z\), that
\(C_{A,I,g}(z)=\det(z(-g)\mid Q)\). Thus it is precisely
the spectral determinant \(\det(-Xg\mid Q)\).
`quotientCorrection` embeds the nonzero polynomial into `RatFunc K`;
`quotientCorrectionValue` gives its unit-valued evaluation at a
nonzero variable, with both the polynomial and determinant comparison
proved. At \(X=1\) the polynomial is the constant determinant
correction.

## Intrinsic invariance and normalization

A morphism of pairs commutes with monodromy, so its restriction to
invariants maps the kernel subspace into the target kernel subspace.
`quotientMap` uses that proved fact to induce an actual quotient
intertwiner. An inverse pair morphism supplies the inverse quotient
map, giving `quotientEquiv`. `kernelEquiv` likewise restricts the pair
equivalence to the two nested invariant/kernel conditions. Both
constructions allow independent source and target carrier universes.

These equivalences prove invariance of the quotient dimension, Euler
polynomial, rational L-factor, quotient determinant and its polynomial
and rational corrections. The proofs use equality of finite dimensions
and invariance of the characteristic polynomial and determinant under
linear conjugacy. `conductorCorrectionClass`, `rationalLFactorClass`,
`quotientDeterminantClass` and `quotientCorrectionClass` then descend
to the parameter owner's genuine pair-isomorphism classes.

The subgroup \(I\) acts trivially on \(V^I\), and this is proved to
descend to \(Q\). Its action on the inertia-fixed kernel is also
trivial. Consequently, if \(hg^{-1}\in I\), the kernel and quotient
operators, L-factor and quotient corrections agree for \(h\) and \(g\).
These are the intrinsic independence results needed when changing a
Frobenius lift within the same inertia coset.

If \(N=0\), the subspace `kernelInInvariants` equals all of \(V^I\).
The quotient dimension is zero, its determinant correction is one,
and the rational quotient correction is one. These are proved
reductions, not fields assumed of a local-factor record.

## Source and dependency boundary

The source is Tate, “Number theoretic background,” Corvallis proceedings
(1979), §4.1.6, printed page 21 (Part II PDF page 30). The retained
registered original is `tate-1979-number-theoretic-background`,
SHA-256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The original formula page was inspected directly. It defines the
Euler reciprocal on \(V_N^I\), the dimension correction to the
conductor, and the determinant on \(V^I/V_N^I\) multiplying the
ordinary epsilon constant. The subspace, quotient, conjugacy and
descent proofs above are intrinsic implementation obligations.

The named element \(g\) is interpreted as geometric Frobenius only
after specializing to the actual local Weil group, inertia and norm
character. In that specialization the convention must be
\(q=\#k_F\) and \(\nu(\Phi)=q^{-1}\). This generic module neither
chooses such an element nor proves the local Weil construction.

The direct project imports are `Langlands.WeilDeligne.Kernels` and the canonical
`Langlands.LocalFactor.Euler.Definitions`. Integration changes the former
`Langlands.LocalFactor.Euler` import to that path without changing any
mathematical declaration.

The dependencies `Langlands.Weil.Representation.Invariants`,
`Langlands.WeilDeligne.Basic` and `Langlands.WeilDeligne.Kernels` are
published in the current Library. Their Lean SHA-256 values are respectively
`6b8ce494e92094357b8035f0a2c782cd67be997a7eb420f01a0ae0b7e78bd87f`,
`2359916cf05537665a83a6f5e75c55f2698577b47d9777f6431262fd1b595fbf`
and
`fc80f9ec895d5bfbc1ae4b397c799aa657eac45b2a4154be30a0fc8f5d560da6`.
All three dependencies are preserved without edits and are not
resubmitted by this contribution.

No epsilon-system existence, reciprocity, Fourier self-dual measure,
functional equation or tensor-factor theorem is assumed or proved
here. The determinant correction is an actual constructed factor;
the full nonabelian epsilon function still needs its separately
specified constant system and existence theorem. In particular,
Tate's auxiliary expression \(\epsilon(V)t^{a(V)}\) must not be
silently identified with the full fixed-character spectral twist,
which also contains the additive-character conductor contribution.
This module does not complete the broad arithmetic definition task.
