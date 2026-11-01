# The joint integral Harris Rosati and normalized determinant locus

This is an internal intersection construction from the actual finite Harris
Rosati locus and the global normalized Harris determinant locus. The
arithmetic fields and algebra have universe zero. The family base `S` is a
locally noetherian scheme over `Spec F`, and `B/S` is a supplied abelian
scheme with a supplied actual action `a` of the positive Harris integral
order. The chosen dual, its evaluation and geometry, the tensor and Picard
statements, and an actual map `lam : B ⟶ Bᵛ` are explicit inputs.

A supplied scheme `H/S`, with comparison `e`, represents the underlying
actual relative-Hom presheaf from `B` to its chosen dual on the full locally
noetherian test category. No existence theorem for `H` is asserted.
The rational action used for the determinant is specifically
`D.harrisHodgePELRationalAction C B a`, the published unique extension of the
rationalization of the supplied integral action. There is no independent
rational action input.

Write `R/S` for the actual integral Rosati locus and `Zdet → S` for the
global determinant inclusion of that rational action.
`integralCMEquationLocus` is the scheme pullback of `R → S` and `Zdet → S`.
`integralCMEquationLocusι` is its structural map to `S`.
If `H/S` is separated, both inclusions being intersected are closed
immersions. Base change and composition then make the joint inclusion a
closed immersion, and local finite type over `S` makes its source locally
noetherian.

For every locally noetherian test `T/S`, the test's chosen dual, evaluation,
geometry, and the Picard and dual base-change statements remain explicit.
The map to that dual is exactly the base change of `lam` followed by the
canonical dual comparison. `integralCMEquationLocus_factors_iff_basis`
identifies factorization of `T → S` through the joint locus with the
conjunction of:

- the published `IntegralRosatiBasisEquations` for the actual base-changed
  integral action and that canonically transported map;
- the published `HarrisTaylorCMRationalLieDeterminantCondition` for the
  rational extension of the same base-changed integral action.

For the forward implication, compose a factorization with the two pullback
projections. The Rosati classification and determinant classification give
the two conditions. For the reverse implication, the same classifications
provide maps to the two loci; their common structural map gives a map to
the pullback. The rational-extension base-change theorem identifies the
action in the determinant classification with the displayed one.
`integralCMEquationLocus_unique_factors_iff_basis` adds uniqueness under
separatedness of `H/S`, using the monomorphism of the joint inclusion.

With actual dual additivity on the test family,
`integralCMEquationLocus_factors_iff` replaces the finite Rosati predicate
by the equations on the entire integral order, using the published
integer-basis criterion. Finally,
`integralCMEquationLocus_factors_involutionCompatible` applies the published
rationalization and finite-basis theorem: every factorization gives
`IsInvolutionCompatible` for the positive auxiliary involution and the
rationalized transported map, together with the exact determinant condition.
This last implication does not assert its converse.

The construction does not supply a polarization, an integral lift of an
arbitrary rational action, an ambient moduli scheme, or a rational-isogeny
comparison. It proves neither smoothness nor projectivity nor the host
normalized CM representability statement. It can be applied to a family
carrying the actual universal integral action once the displayed inputs
are supplied for that family.
