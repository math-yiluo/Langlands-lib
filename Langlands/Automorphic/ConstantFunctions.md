# Actual constant automorphic functions and their operator realization

The namespace `Langlands.Automorphic.ConstantFunctions` constructs actual
constant complex-valued functions on the full adelic general linear group and
proves every condition needed to make them automorphic forms. It then
constructs their one-dimensional subspace as an `OperatorRealization`,
preserved by the actual finite translations, standard infinite compact
translations and genuine enveloping differentials.

The input is any number field `F : Type uF` and any natural rank `n`. There
is no positive-rank hypothesis or extra existence input. The values are in
`ℂ`, and `uF` is arbitrary.

## Constant functions and genuine differentiation

`archimedean F n` is the complex linear map sending `c` to the function with
value `c` on the actual infinite adelic matrix group. The function belongs to
`ArchimedeanGL.SmoothFunctions`: its smoothness is real smoothness in the
published mixed real/complex matrix coordinates.

`smoothDifferential_archimedean` proves that the published directional
derivative kills each such function. The coordinate extension appearing in
the actual `fderiv ℝ` formula is still globally constant, so the derivative
is zero. Tensor-product induction then gives
`complexSmoothLieAction_archimedean` for the whole complexified Lie algebra.

`envelopingAction_archimedean` proves the exact formula

```text
envelopingAction a (archimedean c) = archimedean (augmentation a * c).
```

Here `augmentation` is the already published algebra homomorphism from the
genuine enveloping algebra to `ℂ` that kills the Lie generators. The proof
lifts `a` through the actual tensor-algebra quotient and uses its scalar,
generator, sum and product induction cases. This establishes the formula for
the implemented differential action.

## All defining automorphic conditions

`continuous F n` sends `c` to the continuous rational-left-invariant function
on the full adelic group with value `c`. `continuous_injective` evaluates at
the identity to prove injectivity. All full adelic right translations fix it.

`finiteSmooth F n` gives the same function in
`FiniteSmoothRationalFunctions F n`. Every infinite slice is the preceding
real-smooth constant function; the whole finite adelic group fixes it.
`finiteSmoothSlice_finiteSmooth` and
`finiteSmoothRightAction_finiteSmooth` state these identities explicitly.
`finiteSmoothEnvelopingAction_finiteSmooth` transports the augmentation
formula through the faithful family of actual infinite slices.

`isCenterFinite_finiteSmooth` proves finite-dimensionality of the common
center orbit of the entire slice family. Each orbit vector lies in the
range of the single complex linear map `finiteSmooth`, so its span is a
subspace of a finite-dimensional space. This is finiteness of the common
orbit, rather than a collection of separate slice-wise claims.

`isInfiniteFinite_continuous` uses the same range argument for the orbit of
any subgroup of the infinite adelic group, hence in particular the standard
compact subgroup. `isAutomorphicForm_finiteSmooth` combines these results
with the published equivalence between finite smoothness and actual finite
level and with `HasPolynomialGrowth.const` on every infinite slice.

`form F n : ℂ →ₗ[ℂ] AutomorphicForms F n` is the resulting actual form
constructor. `evaluate_form` evaluates it to `c` at every full adelic group
element. Evaluation at the identity proves `form_injective` and the concrete
nonvanishing assertion `form_one_ne_zero`. Finite and compact translations
fix these forms; `automorphicEnvelopingAction_form` retains the augmentation
formula on the original form carrier.

## An actual one-dimensional realization

`invariant_range_finiteSmooth` proves invariance of the constant line under
the whole concrete automorphic operator algebra. It applies the published
generator criterion `operator_invariant_iff`: finite and compact
translations fix constants, and enveloping differentials preserve the line
by their proved augmentation formula. The criterion then gives closure
under all elements of the generated subalgebra of actual endomorphisms.

`stableForm` views exactly the same forms in the stable carrier, using the
published identification `stableAutomorphicEquiv`. Its underlying finite
smooth function is still `finiteSmooth c`. `realization F n` has underlying
subspace equal to the range of `stableForm`; the preceding invariance
argument proves that it is an `OperatorRealization`.

`scalarEquiv F n` is a complex linear equivalence

```text
ℂ ≃ₗ[ℂ] (realization F n).Space.
```

It is constructed from the injectivity of `stableForm` onto its actual
range. `formInclusion_scalarEquiv` identifies its embedded form with
`form c`, and `evaluate_scalarEquiv` evaluates the represented function to
`c` everywhere. `scalarEquiv_symm_apply` identifies the inverse with
evaluation at the identity. `realization_finrank` proves that this actual
subspace has complex dimension one.

`finiteRepresentation_scalarEquiv` and
`compactRepresentation_scalarEquiv` identify the restricted finite and
compact actions with the identity on scalars.
`envelopingAction_scalarEquiv` identifies the actual restricted enveloping
action with multiplication by `augmentation a`. Consequently
`realization_hasInfinitesimalCharacter` gives the augmentation restricted to
the enveloping center. `realization_isRegularAlgebraic` combines it with the
published highest-weight-zero regular algebraic character construction.

## Provenance and scope

This is an internal construction and proof from the published actual
function spaces, differential operators and automorphic conditions. Its
inputs and conventions are those of `Langlands.Automorphic.RegularAlgebraic`
and `Langlands.Automorphic.FullOperatorRealization` and their imports. The
calculus and quotient-induction steps use the pinned Mathlib implementations
of `fderiv`, tensor products, tensor algebras and the universal enveloping
algebra. No additional original-literature assertion is used.

The realization is an actual embedded subspace of the published
automorphic space; its scalar equivalence does not replace that carrier by
an arbitrary type. No new function-space topology, irreducibility theorem,
cuspidality assertion, general Hecke-character realization or spectral
decomposition is claimed in this module. The formulas also cover rank zero.
