# Transport of Weil–Deligne factor constructions

`Langlands.LocalFactor.WeilDeligne.Transport` constructs the comparison of
the existing Weil–Deligne factor objects under an explicit group equivalence
`e : H ≃* G`. Worker 40 authored this derived construction.

For a field `K`, a group character `ν : G →* Kˣ`, a pair
`A : WeilDeligneRepresentation K G ν`, and a normal subgroup `I` of `G`,
write
\[
 A_e=\operatorname{restrict}(e,A),\qquad J=e^{-1}(I).
\]
Here `A_e` is precisely the existing
`WeilDeligneRepresentation.restrict e.toMonoidHom A`. It retains the vector
space and monodromy operator and precomposes the action with `e`; its covariance
character is explicitly `ν.comp e.toMonoidHom`. The subgroup `J` is the actual
`I.comap e.toMonoidHom`, whose normality is inferred. The original action is
evaluated at `e h` when the transported action is evaluated at `h : H`.
Coefficient, source-group, target-group and carrier universes are independent.

## Actual invariant and quotient equivalences

`invariantsEquiv` identifies the `J`-invariants of the restricted representation
with the restriction of the `I`-invariant representation. Its forward and inverse
maps retain the underlying vector. For the forward map, an arbitrary `i : I`
has inverse image `e.symm i` in `J`, so the vector is fixed by `i`. For the inverse
map, an element of `J` has image in `I`. The linear identities and intertwining
equations then follow directly from the unchanged vectors and reindexed action.

Applying this construction to the existing monodromy-kernel representation gives
`kernelEquiv`, an equivalence on the actual fixed kernels. The private
`kernel_map` lemma proves that `invariantsEquiv` maps the subspace cut out by
`Nv = 0` exactly to the corresponding subspace inside the original invariants.
`quotientEquiv` uses `Submodule.Quotient.equiv` to construct the induced
representation equivalence
\[
 V^J_{A_e}/(\ker N)^J_{A_e}\ \simeq_K\ V^I_A/(\ker N)^I_A.
\]
Its intertwining equation follows by checking the quotient generators.
`quotientEquiv_mk` records that it commutes with the actual quotient projections.

## Preserved factors and evaluation domains

For every `h : H`, the following identities are proved with the left side
evaluated on `(A_e,J,h)` and the right side on `(A,I,e h)`:

- `conductorCorrection_restrict` preserves the dimension of the quotient.
- `eulerPolynomial_restrict` preserves
  `det(1 - X r(h) | (ker N)^J)`.
- `rationalLFactor_restrict` preserves its reciprocal in `RatFunc K`.
- `quotientDeterminant_restrict` preserves `det(-r(h) | V^J/(ker N)^J)`.
- `quotientCorrectionPolynomial_restrict` preserves the monomial
  `det(-r(h) | Q) X^(dim Q)`, which evaluates to `det(-z r(h) | Q)`.
- `quotientCorrection_restrict`, `quotientConstantCorrection_restrict`
  and `quotientCorrectionValue_restrict` preserve the rational correction,
  the constant determinant unit and its value at any supplied unit `z : Kˣ`.

The dimension identity uses the quotient linear equivalence. The Euler and
negative determinant identities use conjugacy by the kernel and quotient
equivalences, respectively. The polynomial, rational and unit identities follow
from those identities and the existing factor definitions.

`regularPointEquiv` constructs an equivalence between the two regular domains.
Its forward and inverse maps keep the scalar coordinate; the Euler-polynomial
identity transports the nonvanishing certificate in both directions.
`regularPointEquiv_val` exposes that coordinate identity, and
`regularLValue_restrict` proves equality of the unit-valued reciprocal evaluations.

For complex coefficients and the same explicit positive real input `q`,
`spectralRegularPointEquiv` similarly preserves `s` and the condition that the
Euler denominator at `exp(-s log q)` is nonzero. Its `_val` lemma and
`spectralLValue_restrict` give the coordinate and value identities.
Neither equivalence assigns a finite value at a pole or extends evaluation
through a cancellation. The spectral quotient-correction identity is already
the specialization of `quotientCorrectionValue_restrict` to
`LocalFactor.spectralParameter q hq s`.

## Source correspondence and scope

The retained original is Tate, “Number theoretic background,” Corvallis
proceedings (1979), §4.1.2, printed page 20 (Part II PDF page 29), for the pair
and covariance relation; §4.1.6, printed pages 20–21 (PDF pages 29–30), for the
fixed monodromy kernel, Euler reciprocal, conductor correction and negative
determinant on the invariant quotient. Source ID:
`tate-1979-number-theoretic-background`; retained PDF SHA-256:
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
Those pages were read directly for this unit.

The new transport constructions are derived algebraic identities of the existing
objects in `Langlands.WeilDeligne.Restriction` and
`Langlands.LocalFactor.WeilDeligne`. They are not asserted to be a separately
stated theorem of Tate. The generic algebraic formulation uses an arbitrary
field and group; it does not impose the characteristic-zero and open-inertia
conditions of Tate's arithmetic setting, since these reindexing identities do
not use them.

The group equivalence is essential: this unit makes no invariance claim for
restriction to an arbitrary proper subgroup. It does not construct an arithmetic
Weil-group comparison, identify inertia for a field embedding, establish a norm
comparison, or identify residue cardinalities. An arithmetic application must
supply those identifications; geometric Frobenius must satisfy the project's
normalization `ν(Φ) = q⁻¹`. The spectral statements use the same `q` on both sides.

This unit does not transport ordinary epsilon systems, additive characters or
Haar measures, and it proves no system existence or local functional equation.
The quotient correction is only one component of the full epsilon factor.
It is a prerequisite for a later arithmetic attachment and does not complete
the broad local-factor task.
