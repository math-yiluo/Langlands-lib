# Reduction of the group differential commutator to manifold calculus

This internal reduction uses the original `groupDirectionalValue`, Mathlib's
actual tangent Lie algebra, and the explicitly retained prerequisite
`smoothVectorFieldCommutator I G`. It does not supply a proof of that prerequisite.

Let `I` be a boundaryless real model with complete normed model space and let
`G` carry its specified smooth Lie-group structure.
`groupDirectionalValue_commutator_of_vectorFieldCommutator` says that if the
generic scalar commutator holds on this manifold, then, for identity tangent
vectors `X`, `Y`, a real smooth complex-valued function `f`, and every `g`,

```
D_[X,Y] f(g) = D_X(D_Y f)(g) - D_Y(D_X f)(g).
```

Here each `D` is precisely the derivative of the positive right orbit at the
identity, and `[X,Y]` is precisely Mathlib's `GroupLieAlgebra` bracket.
The implemented proof uses the already proved formula expressing `D_X f` as
`df` applied to the actual left-invariant vector field. Those vector fields
are differentiable as tangent-bundle sections. Mathlib's
`mulInvariantVector_mlieBracket` identifies their vector-field bracket with
the invariant vector field of `[X,Y]`. Substitution into the generic scalar
commutator gives the stated identity with the displayed sign.

This is a conditional reduction lemma. It does not establish the generic
calculus premise, an unconditional Lie or enveloping action, exponential
curves, growth bounds or a Hilbert-space realization.
