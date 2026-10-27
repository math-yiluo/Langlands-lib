# Stability of the two-block cell submodule under the upper unipotent group

Worker 731 authored this derived statement for the proof of
`Langlands.Whittaker.TwoBlockWhittakerExtensionStatement`. Worker 643 asked
for this unit. The module contains one Prop-valued definition and no proof.

## The statement

`Langlands.Whittaker.TwoBlockCellUnipotentStabilityStatement.{uF,uV}` is a
closed proposition. It quantifies over

- a prime `p` (with `Fact p.Prime`), a field `F : PadicField.{uF} p` and
  natural numbers `a`, `b`; write `A = a + 1` and `B = b + 1`;
- complex vector spaces `V₁ V₂ : Type uV` (both in the same universe) and
  arbitrary complex representations
  `π₁ : Representation ℂ (GeneralLinear (a + 1) F.Carrier) V₁` and
  `π₂ : Representation ℂ (GeneralLinear (b + 1) F.Carrier) V₂`;
- an element `u` of `GeneralLinear.upperUnipotent (a + 1 + (b + 1)) F.Carrier`,
  the subgroup of invertible upper triangular `(A + B) × (A + B)` matrices
  with all diagonal entries `1`;
- an element `f : TwoBlockInducedCarrier F a b π₁ π₂`.

It asserts

```
f ∈ twoBlockCellSubmodule F a b π₁ π₂ →
  twoBlockInduced F a b π₁ π₂ u.val f ∈ twoBlockCellSubmodule F a b π₁ π₂.
```

No smoothness or other hypothesis on `π₁`, `π₂` is assumed.

Meaning of the names, all from the accepted definition module
`Langlands.Representation.Whittaker.TwoBlockOpenCell`:

- `twoBlockInduced F a b π₁ π₂` is the ordered normalized induction `ξ`,
  `F.canonicalNormalizedProductInduced` of `(π₁, π₂)` from the standard upper
  parabolic `P` of block shape `(A, B)`. It acts by right translation:
  `(ξ(h) f)(g) = f(g h)` (`twoBlockEval_twoBlockInduced`).
- `TwoBlockInducedCarrier F a b π₁ π₂` is its carrier: the smooth functions
  `f : GL_{A+B}(F) → V₁ ⊗ V₂` with `f(q g) = ρ(q) f(g)` for `q ∈ P`, for the
  block tensor `ρ` through the Levi projection twisted by the positive half
  modulus.
- `twoBlockCellSubmodule F a b π₁ π₂` is the submodule `D` of those `f` whose
  support lies in the cell `P w n(M_{B×A})` and whose restriction
  `x ↦ f(w n(x))` has compact support, where
  `w = Shahidi.blockWeyl (a + 1) (b + 1) F.Carrier`,
  `n(x) = Shahidi.intertwiningUnipotent (a + 1) (b + 1) F.Carrier x` and `x`
  has `B` rows and `A` columns.

So the statement says that `D` is stable under right translation by the
upper unipotent group of `GL_{A+B}(F)`.

## Source and provenance

The source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg convolutions*, Amer. J. Math. 105 (1983), 367–464, registered
as `jpss-1983-rankin-selberg` (SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`). No
errata note for this source is registered.

In the proof of the Proposition of Section (9.1), printed p. 453 (PDF p. 88,
read visually), JPSS take a vector `f` of `ξ` with
`f[w n(x); h₁, h₂] = Ψ(x) W₁(h₁) W₂(h₂)` and let `W` be "the corresponding
element" of the Whittaker model of `ξ`, given by

```
W(g) = ∫ f[w n(x) g; e, e] θ̄(n(x)) dx.
```

This follows (5.5) (printed p. 424, PDF p. 59, formulas (1) and (3)), where
the Whittaker function of `f` is `W_f(g) = λ(σ(g) f)` and is computed by the
integral of the right translate `σ(g) f` against `θ̄` over the opposite
unipotent radical.

JPSS do not state the present stability property. It is derived: to use that
integral as the Whittaker functional on the cell functions, one evaluates it
on right translates `ξ(u) f` by upper unipotent `u` and needs these
translates to be again supported in the cell with compactly supported
restriction. The Lean statement records exactly this, for all upper
unipotent `u`, not only those in the Levi or radical blocks. It needs no
hypothesis on `π₁`, `π₂`, so none is assumed; the parent statement's
hypotheses are therefore not needed here.
