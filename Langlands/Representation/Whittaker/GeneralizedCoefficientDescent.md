# Descent between full-transpose smoothing maps

This internal prerequisite constructs the actual endomorphism between two
smoothing maps when the first is surjective and its kernel is contained in the
second's kernel. It uses the published smoothing, smooth contragredient,
quotient-linear-map, admissible duality and Schur constructions. No external
theorem is transcribed.

## Setting and hypotheses

The group \(G\) is a Hausdorff, locally compact, totally disconnected
topological group with its Borel measurable structure. Its universe and that of
the complex representation space \(V\) are independent. The carrier \(V\) has
only its additive group and complex module structures. The representation
\(\rho\) is smooth, and \(\ell_1,\ell_2\) belong to its full algebraic dual.
Neither functional is assumed smooth.

The constructions, evaluation lemmas and uniqueness lemma require that the
measure \(\mu\) be finite on compact sets and right invariant. They explicitly
assume that \(S_{\ell_1}\) is surjective and
\(\ker S_{\ell_1}\subseteq\ker S_{\ell_2}\).
The final scalar lemma additionally assumes left invariance, positivity on
nonempty open sets, admissibility and irreducibility of \(\rho\), and
\(\ell_1\ne0\). It derives surjectivity, so it has no separate surjectivity
premise. No result in this file requires inversion invariance.

## The descended map

Write \(S_\ell(f)\) for `smoothFunctional μ ρ hρ ℓ f`. The map
`smoothFunctionalDescentLinear` first identifies the actual smooth dual with
the quotient of test functions by \(\ker S_{\ell_1}\), then applies the map
induced by \(S_{\ell_2}\). Thus it satisfies
\(A(S_{\ell_1}(f))=S_{\ell_2}(f)\).
The implementation composes `Submodule.liftQ` with the inverse of
`LinearMap.quotKerEquivOfSurjective`. Kernel inclusion is precisely the
well-definedness condition for the quotient map.
`smoothFunctionalDescentLinear_apply` proves the displayed interpolation
identity using the two quotient evaluation laws.

With the existing convention \(R_a f(x)=f(xa)\), right-translation covariance
says \(S_\ell(R_a f)=\rho^\vee(a)S_\ell(f)\).
Every smooth-dual vector is \(S_{\ell_1}(f)\); the interpolation identity and
this covariance give
\[
 A\bigl(\rho^\vee(a)S_{\ell_1}(f)\bigr)
 =S_{\ell_2}(R_a f)
 =\rho^\vee(a)A(S_{\ell_1}(f)).
\]
Thus `smoothFunctionalDescent` bundles \(A\) as an endomorphism of the actual
smooth contragredient. `smoothFunctionalDescent_apply` exposes the same
interpolation identity for this bundle, and `smoothFunctionalDescent_unique`
proves that every intertwiner satisfying that identity equals the constructed
one. Its proof tests equality on the surjective image of \(S_{\ell_1}\).

## Scalar consequence

For an admissible irreducible representation and nonzero \(\ell_1\), the
published separation helper proves that \(S_{\ell_1}\) is surjective.
The private cofinality lemma applies
`Hecke.TestFunction.commonCompactOpenBiInvariance` to the empty test-function
family: every open subgroup contains a compact open subgroup.
`isAdmissible_smoothContragredient_of_compact_cofinal` and
`CompactSplitting.isIrreducible_smoothContragredient` then give admissibility and
irreducibility of the smooth dual.

`admissibleSchur_scalarEndomorphism` makes the constructed endomorphism
\(A=c\,\mathrm{id}\). Evaluating on every \(S_{\ell_1}(f)\) yields
\(S_{\ell_2}=cS_{\ell_1}\).
Linearity gives \(S_{\ell_2-c\ell_1}=0\), and the published Haar local-unit
faithfulness lemma `smoothFunctional_eq_zero_iff` gives
\(\ell_2=c\ell_1\). Nonvanishing of \(\ell_1\) makes scalar multiplication
injective in the scalar and proves uniqueness.
This is `existsUnique_smul_of_smoothFunctional_ker_le`. It allows
\(\ell_2=0\), in which case the unique scalar is zero.

## Scope

The kernel inclusion is an explicit premise here. This file neither derives it
from an anti-involution nor proves the generalized-coefficient kernel
criterion, Whittaker distribution invariance, or multiplicity one.
