# Compact fixed vectors and actual infinitesimal invariants

This internal construction differentiates compact translation on an actual
automorphic operator realization. It constructs the complex-linear map

```text
S.compactRepresentation.invariants
  → LieModule.maxTrivSubmodule ℂ (CompactComplexLieAlgebra F n) S.Space
```

that retains the underlying vector. Its infinitesimal membership proof uses the
published compact tangent curves and scalar derivatives of smooth functions.
The map is proved injective.

## Parameters and actual carriers

The namespace is `Langlands.Automorphic.OperatorRealization`. The number field
`F : Type u` has arbitrary universe `u`, and `n : ℕ` has no positivity
restriction. For every `S : OperatorRealization F n`, `S.Space` is its actual
subspace of `StableAutomorphicFunctions F n`, which is the maximal subspace of
actual automorphic forms preserved by the concrete finite, compact, and
enveloping operators. No nonzeroness or irreducibility of this subspace is
assumed.

The group is the full `standardInfiniteCompact F n`, acting by the published
`S.compactRepresentation`. Its invariant submodule consists of vectors `f`
satisfying `S.compactRepresentation k f = f` for **every** compact element `k`.
The Lie algebra is the actual scalar extension

```text
CompactComplexLieAlgebra F n = ℂ ⊗[ℝ] compactLieSubalgebra F n.
```

Its action is the already constructed `S.compactLieAction`, obtained by
restricting `S.complexLieAction` along the actual compact inclusion. The target
is Mathlib's maximal trivial Lie submodule for this same action; membership is
exactly `∀ Y, ⁅Y, f⁆ = 0`. No replacement representation or Lie action is
introduced. No topology on `S.Space` or assertion of a vector-valued derivative
there is needed; all derivatives below are scalar real derivatives with values
in `ℂ`.

## Scalar differentiation

`compactCurve_evaluate_deriv` takes a real Lie element `X`, a curve
`c : ℝ → standardInfiniteCompact F n`, and the hypotheses

```text
c 0 = 1
HasDerivAt (fun t => coordinates ((c t).val)) (realLieAlgebraToMatrix X) 0.
```

For every `f : S.Space`, infinite adelic point `a`, and finite adelic point `b`,
it proves that the real derivative at zero of

```text
t ↦ evaluate (S.toContinuous (S.compactRepresentation (c t) f)) (pair a b)
```

is

```text
evaluate (S.toContinuous (S.complexLieAction (complexify X) f)) (pair a b).
```

Here `complexify X = 1 ⊗ X`. The curve hypothesis concerns the derivative of
the actual matrix coordinates; it does not assume differentiation of the
representation or the desired formula. The proof applies the published
`ArchimedeanGL.compactCurve_right_deriv` to the actual smooth infinite slice
`finiteSmoothSlice F n b f.val.val`. The group-action evaluation formula and
the adelic product formula identify the translated function. The published
`evaluate_finiteSmoothEnvelopingAction` and
`ArchimedeanGL.envelopingAction_real_generator` identify its derivative with
the genuine restricted Lie action.

## Vanishing on compact fixed vectors

`evaluate_complexLieAction_compact_real_eq_zero` assumes that `f` belongs to
the full compact invariant submodule and that
`X : compactLieSubalgebra F n`. It proves that every evaluation at `pair a b`
of `S.complexLieAction (complexify X.val) f` is zero.

The proof obtains the curve and both coordinate hypotheses from the published
theorem `ArchimedeanGL.compactTangentCurve F n X`. Fixedness makes its scalar
orbit equal to the constant function with value `evaluate f (pair a b)`.
`HasDerivAt.congr_of_eventuallyEq` transfers the constant function's zero
derivative, and uniqueness of the scalar derivative identifies the actual
Lie-action evaluation with zero.

`complexLieAction_compact_real_eq_zero` then proves the actual vector equality

```text
S.complexLieAction (complexify X.val) f = 0.
```

It uses the injective linear inclusion `S.toContinuous`, extensionality of
the actual function carriers, and the fact that every adelic point is the pair
of its infinite and finite projections.

`compactLieAction_eq_zero_of_fixed` extends this result to every
`Y : CompactComplexLieAlgebra F n`. Tensor-product induction reduces a simple
tensor `z ⊗ X` through `compactComplexInclusion_tmul` to the scalar multiple
`z • complexify X.val`. Complex linearity of `S.complexLieAction` then gives
zero. Additivity treats sums. Thus the complex compact annihilation is proved
from full group fixedness without a supplied infinitesimal compatibility
certificate.

## Constructed inclusion

`compactFixedLieInclusion` is the complex-linear map displayed above. Its value
at an invariant vector `f` is the same underlying `f.val`, with membership in
the target supplied by `compactLieAction_eq_zero_of_fixed` and the published
identity `S.compact_lie_eq`. Its additivity and scalar compatibility are
subtype equalities.

The accompanying results are:

| Declaration | Content |
| --- | --- |
| `compactFixedLieInclusion_coe` | The underlying vector of the image is `f.val`. |
| `compactFixedLieInclusion_injective` | The inclusion is injective, by equality of underlying vectors. |
| `evaluate_compactFixedLieInclusion` | Every adelic evaluation is unchanged. |

## Provenance and scope

This is an internal derivation from the published actual automorphic operator
realizations and compact analytic differentiation infrastructure. Its imported
project modules are `OperatorCompactCompatibility` and
`ArchimedeanCompactGroupFiniteProof`; Mathlib supplies the invariant submodule,
maximal trivial Lie submodule, and elementary derivative uniqueness. The new
construction adds the proved analytic membership and identity inclusion between
these existing objects. It makes no new identification with an external
literature definition or theorem.

Only the forward inclusion from full compact fixed vectors to compact Lie
invariants is asserted. The full compact group can have disconnected components,
and no converse or equality of invariant spaces is claimed. This unit does not
construct general algebraic coefficient attachments, differentiate equivariance
on higher alternating cochains, prove preservation of horizontality by the
coefficient differential, or construct relative cohomology. It also does not
prove that the operator core is the entire automorphic form space. These remain
separate obligations.
