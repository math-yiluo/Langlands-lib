# Pullback of actual compact induction by an automorphism

Author: Worker 76.

This module constructs
`Langlands.Induction.precomposeCompactInducedEquiv` on the published actual
compactly induced function spaces. Let `R : Type uR` be a commutative ring,
`G : Type uG` a topological group, `H : Subgroup G`, and
`α : G ≃ₜ* G` a continuous multiplicative equivalence with continuous inverse.
The supplied condition is

```text
hα : ∀ x : G, α x ∈ H ↔ x ∈ H.
```

For every `R`-module `V : Type uV` with an additive commutative group and every
representation `σ : Representation R H V`, the constructor is

```text
Representation.Equiv
  ((compactInduced H σ).comp α.toMonoidHom)
  (compactInduced H (automorphismInducing H α hα σ)).
```

Here `automorphismInducing H α hα σ` is exactly
`σ.comp (subgroupAutomorphism H α hα).toMonoidHom`. The subgroup automorphism is
the published restriction of `α` to `H`, with its actual subspace topology.
Thus the coefficient action at `h : H` is `σ(α(h))`.
The domain has the original compact-function carrier and the original ambient
action pulled back through `α`. The codomain has this pulled-back coefficient
action and the ordinary right-translation action of `G`. The field, group,
coefficient and module universes are not identified. No smoothness hypothesis
on `σ`, closedness of `H`, Hausdorffness or local compactness is required.

## Maps and quotient support

The forward and inverse evaluation formulas are

```text
E(f)(x)      = f(α(x)),
E.symm(k)(x) = k(α.symm(x)).
```

They are the laws `precomposeCompactInducedEquiv_eval` and
`precomposeCompactInducedEquiv_symm_eval` for this same constructor, stated
using the published `Induction.eval` and compact subtypes.

`automorphismSmoothEquiv` specializes the existing
`precomposeSmoothInducedEquiv` to the canonical subgroup restriction. That
published construction proves covariance, linearity, inverse identities and
the existence of a uniform open right stabilizer in both directions. Its
stabilizer is the comap of the original open stabilizer under `α`, or under
`α.symm` for the inverse.

For a smooth induced function `f`, the proved equality
`quotientSupport_automorphismSmoothEquiv` says

```text
quotientSupport(E(f)) = quotientAutomorphism H α hα ⁻¹' quotientSupport(f).
```

These are the actual projected nonzero supports in `LeftQuotient H`, whose
cosets are `H * x`. The quotient automorphism is the published homeomorphism
`[x] ↦ [α(x)]`. The proof uses quotient induction on a representative `x` and
the existing `quotientMap_preimage_quotientSupport` to reduce both sides to
`f(α(x)) ≠ 0`. The homeomorphism's compact-preimage equivalence then proves
`compactSupport_automorphismSmoothEquiv_iff`.

The compact equivalence restricts the smooth equivalence using this exact
compactness equivalence. In the inverse direction the smooth inverse law
identifies its transported support with the support of the supplied compact
function. Additivity and scalar compatibility are pointwise. The two inverse
identities follow from the smooth inverse identities and subtype extensionality.
Ambient equivariance follows from

```text
f(α(x) * α(g)) = f(α(x * g)).
```

Thus the constructor includes the actual representation-equivariance field.

## Naturality in the coefficient representation

Let `W : Type uW` be any other additive commutative `R`-module and let
`T : σ.IntertwiningMap τ`. The definition `automorphismInducingMap` keeps the
same underlying linear map and uses the original intertwining identity at
`subgroupAutomorphism H α hα h`. The theorem
`precomposeCompactInducedEquiv_natural` proves, for every compact function `f`,

```text
E_τ(compactInducedMap H T f)
  = compactInducedMap H (automorphismInducingMap H α hα T) (E_σ(f)).
```

Evaluation of either side at `x` is `T(f(α(x)))`, so extensionality proves the
identity. The modules `V` and `W` can have independent universes. This is the
stated naturality equation on all coefficient intertwiners; this module does
not package a separate category-theoretic natural isomorphism.

## Provenance and scope

This is an internal construction from the published modules
`Representation.Induction.InverseTranspose`,
`Representation.Induction.CompactQuotientProof`, and
`Analysis.Local.QuotientAutomorphismStatement`, together with Mathlib's
homeomorphism compactness equivalence. It extends the existing smooth
precomposition construction by restricting to the actual compact-support
submodules. It introduces no new quotient or replacement support condition,
and makes no claim to reproduce a separately stated theorem in the literature.

The intended use is automorphism transport in the relative orbit integral.
No integral transformation formula, Haar scaling law or parabolic-orbit
Jacquet comparison is proved here. Those remain separate obligations of the
parent task. This module changes none of its imported Lean/Markdown pairs.
