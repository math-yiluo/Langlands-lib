# Sections of the two-block cell with prescribed restriction

Worker 731 authored this derived statement for the proof of
`Langlands.Whittaker.TwoBlockWhittakerExtensionStatement`. Worker 643 asked
for this unit and agreed to its exact form. The module contains one
Prop-valued definition and no proof.

## The statement

`Langlands.Whittaker.TwoBlockCellSectionStatement.{uF,uV}` is a closed
proposition. It quantifies over

- a prime `p` (with `Fact p.Prime`), a field `F : PadicField.{uF} p` and
  natural numbers `a`, `b`; write `A = a + 1` and `B = b + 1`;
- complex vector spaces `V₁ V₂ : Type uV` (both in the same universe) and
  arbitrary complex representations
  `π₁ : Representation ℂ (GeneralLinear (a + 1) F.Carrier) V₁` and
  `π₂ : Representation ℂ (GeneralLinear (b + 1) F.Carrier) V₂`.

It assumes `IsSmooth π₁` and `IsSmooth π₂`, where `GL_A(F)` and `GL_B(F)`
carry the topology induced by `F.canonicalTopologicalData.topology` on
`F.Carrier`. `IsSmooth` is the Library's predicate: every vector is fixed by
some open subgroup.

With that topology installed, it asserts: for every
`Ψ : SchwartzBruhat (Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier)` and every
`v : PiTensorProduct ℂ (Shahidi.pairCarrier V₁ V₂)` there is an element
`f : TwoBlockInducedCarrier F a b π₁ π₂` such that

```
f ∈ twoBlockCellSubmodule F a b π₁ π₂ ∧
  ∀ x, twoBlockRestriction F a b π₁ π₂ f x = Ψ x • v.
```

Meaning of the names, all from the accepted definition module
`Langlands.Representation.Whittaker.TwoBlockOpenCell`:

- `TwoBlockInducedCarrier F a b π₁ π₂` is the actual carrier of the ordered
  normalized induction `F.canonicalNormalizedProductInduced` of
  `(π₁, π₂)` from the standard upper parabolic `P` of block shape `(A, B)`:
  the smooth functions `f : GL_{A+B}(F) → V₁ ⊗ V₂` with
  `f(q g) = ρ(q) f(g)` for `q ∈ P`, where `ρ` is the block tensor through
  the Levi projection twisted by the positive half modulus.
- `twoBlockRestriction F a b π₁ π₂ f x` is `f(w n(x))`, with
  `w = Shahidi.blockWeyl (a + 1) (b + 1) F.Carrier` and
  `n(x) = Shahidi.intertwiningUnipotent (a + 1) (b + 1) F.Carrier x`, for
  `x` with `B` rows and `A` columns.
- `twoBlockCellSubmodule F a b π₁ π₂` is the submodule `D` of those `f` whose
  support lies in the cell `P w n(M_{B×A})` and whose restriction
  `x ↦ f(w n(x))` has compact support.

`Ψ x • v` is the complex scalar `Ψ x` times the tensor `v`. The element `f`
depends on `Ψ` and `v`. The statement asserts neither uniqueness of `f` nor
any linearity or continuity in `(Ψ, v)`.

## Source and provenance

The source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg convolutions*, Amer. J. Math. 105 (1983), 367–464, registered
as `jpss-1983-rankin-selberg` (SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`). In the
proof of the Proposition of Section (9.1), printed p. 453 (PDF p. 88, read
visually), JPSS say that, as in (5.5), there is a vector `f` in the space of
`ξ` with

```
f[w n(x); h₁, h₂] = Ψ(x) W₁(h₁) W₂(h₂),
```

with `w = [[0, 1_{r₁}], [1_{r₂}, 0]]`, `n(x) = [[1_{r₂}, x], [0, 1_{r₁}]]`,
`x` of size `r₂ × r₁` and `Ψ` a Schwartz–Bruhat function. Here `r₁ = A` and
`r₂ = B`. No errata note for this source is registered.

The Lean statement is derived from that sentence as follows.

- JPSS realize `ξ` on functions of `(g, h₁, h₂)` with values in `ℂ`, through
  the Whittaker models of `π₁` and `π₂`. The Library's induced carrier
  instead takes values in `V₁ ⊗ V₂`. The source's value
  `Ψ(x) W₁(h₁) W₂(h₂)` corresponds to the value `Ψ(x) • (v₁ ⊗ v₂)` at
  `w n(x)`, where `W₁`, `W₂` are the Whittaker functions of `v₁`, `v₂`.
- The Lean statement allows every tensor `v`, not only pure tensors. This is
  a generalization: a pure tensor is a special case.
- JPSS do not state the support of `f` explicitly; the construction "as in
  (5.5)" (printed pp. 424–425) produces a function supported in the cell. The
  conclusion `f ∈ twoBlockCellSubmodule` records that support and the
  compact support of the restriction, which is automatic since `Ψ` has
  compact support.
- JPSS work with representations that have Whittaker models, and the parent
  statement assumes `RankinSelberg.IsOfWhittakerType`, whose first component
  is `IsAdmissible`, which includes `IsSmooth`. This statement assumes only
  smoothness, which is all the construction uses. Whittaker functions do not
  enter it.
- The field topology is the canonical one, matching
  `Whittaker.TwoBlockWhittakerExtensionStatement`, and `Ψ` has the type of
  the function produced by
  `HarmonicAnalysis.PadicMatrixFourierSliceStatement` with `a` and `b` as
  here.
