# Function-preserving composed-to-flattened normalized induction

Authors: Worker 6 and Worker 373 (the exact target and prior interface probe).

`Langlands.Parabolic.ComposedFlattenedInductionStatement.{uF,uV}` is a
closed proposition definition stating a comparison of two existing direct
induced representations. This file states the comparison and supplies no proof.

For every prime `p`, every `F : PadicField.{uF} p`, compatible topological
data `T`, rank `n`, ordered block shape `B : BlockShape n`, refinement
`S : BlockRefinement B`, complex module `V : Type uV`, and representation
`σ : Representation ℂ (Geometric.refinedLevi F.Carrier B S) V`, it asserts
the existence of a complex linear `GeneralLinear n F.Carrier`-equivariant
equivalence

```lean
(T.normalizedComposedInduced B S σ).Equiv
  (T.normalizedParabolicInduced (B.flatten S)
    (σ.comp (Geometric.flattenedLeviEquiv F.Carrier B S).toMonoidHom))
```

whose forward and inverse maps preserve the underlying functions pointwise:

```lean
∀ f (g : GeneralLinear n F.Carrier),
  Induction.eval _ _ (E f) g = Induction.eval _ _ f g
```

and

```lean
∀ f (g : GeneralLinear n F.Carrier),
  Induction.eval _ _ (E.symm f) g = Induction.eval _ _ f g.
```

The first formula quantifies over the composed carrier, and the second over
the flattened carrier. These formulas specify the actual map on functions,
beyond the existence of an abstract representation equivalence.

## Subgroups and coordinates

Write `C = B.flatten S` and `e = Geometric.flattenedLeviEquiv F.Carrier B S`.
The composed parabolic is `Parabolic.composedParabolic F.Carrier B S`:
the inverse image of `Geometric.refinedParabolic F.Carrier B S` under the
outer block projection, viewed inside `GeneralLinear n F.Carrier`.
Thus its matrices are upper triangular in outer blocks and are upper
triangular in the prescribed inner blocks on each outer diagonal.
Its map `Parabolic.composedLeviProjection` first extracts the outer
diagonal blocks and then their inner Levi components. Its codomain is the
actual subgroup `Geometric.refinedLevi F.Carrier B S` of `B.Levi F.Carrier`.

Flattening lists the fine blocks in their original outer-then-inner order.
The equivalence `e : C.Levi F.Carrier ≃* refinedLevi F.Carrier B S`
groups those fine matrices into outer blocks, with the necessary transports
of the finite matrix index types. It has the published ambient formula

```lean
B.leviEmbedding F.Carrier (e m).val = C.leviEmbedding F.Carrier m.
```

This is `Geometric.flattenedLeviEquiv_embedding`. The coordinate identity
`GeneralLinear.BlockShape.index_index_eq_flatten` identifies each nested
matrix position with its flattened position. It supplies the coordinate
data for the general comparison
`GeneralLinear.BlockShape.composedParabolic_eq_of_coordinates`: the
composed and flattened parabolics are the same ambient subgroup.
The associated `parabolicRefinementEquiv` preserves the ambient matrix.
The general projection comparison is
`GeneralLinear.BlockShape.composedLeviProjection_parabolicRefinementEquiv`;
after identifying its coordinate Levi equivalence with `e`, it expresses
the intended specialized formula

```text
composedLeviProjection (the same matrix q) = e (C.leviProjection q).
```

These general geometry results and the explicit components of `e` provide
the route for the future proof. This statement file does not add a
specialized subgroup or projection theorem. The flattened inducing
representation is exactly `σ.comp e.toMonoidHom`, on the same module `V`.

## Function carriers and normalization

Both constructions use `Induction.SmoothFunctions`: the smooth vectors
inside the module of all covariant functions from `GeneralLinear n F.Carrier`
to `V`. Each such function has one open subgroup fixing the entire
function under right translation. Equivalently, for that subgroup `K`,
`f(x k) = f(x)` for every `x` and every `k ∈ K`. No topology on `V` is
required, and no compact-support condition is imposed.

For the composed carrier, covariance is

```text
f(q g) = δ_comp(π_comp(q))^(1/2) • σ(π_comp(q))(f(g)),
```

where `π_comp` is `composedLeviProjection` and
`δ_comp = T.composedLeviModulus B S`. The normalizing scalar is the
canonical positive square root, embedded in `ℂˣ`, implemented by
`T.composedLeviHalfModulus B S` and inflated by
`T.composedParabolicHalfModulus B S`. The full character is the product
`T.refinedOuterModulus B S * T.refinedLeviModulus B S`: the outer
block modulus restricted to the refined Levi, times the inner moduli.

For the flattened carrier, covariance is

```text
f(q g) = δ_C(π_C(q))^(1/2) • σ(e(π_C(q)))(f(g)),
```

where `π_C = C.leviProjection F.Carrier` and
`δ_C = T.leviModulus C`. This is the existing explicit determinant
modulus
`δ_C(m) = ∏_{k<l} |det m_k|^(C.size l) / |det m_l|^(C.size k)`,
using the normalized absolute value of `F`. Both actions are right
translation, `(h · f)(g) = f(g h)`.

The future proof requires the full flattened modulus identity

```lean
(T.composedLeviModulus B S).comp e.toMonoidHom =
  T.leviModulus (B.flatten S).
```

Its shared statement is
`Langlands.Parabolic.FlattenedRefinementModulusStatement`. A proof of this
identity will make the positive half characters agree; the subgroup and
projection identifications then allow the same underlying function and
the same open stabilizer to satisfy either covariance condition.
The existing `T.composedLeviHalfModulus_eq` only splits the composed half
character into its outer and inner factors. It does not supply the full
flattened comparison. Neither a modulus equality nor an induction
equivalence is a theorem-valued premise of the present statement.

## Scope and source correspondence

The universes `uF` and `uV` are independent; both induced carriers live in
`Type (max uF uV)`. The representation `σ` is arbitrary: it need not be
smooth, irreducible, admissible, finite dimensional, or of finite length.
Smoothness is imposed on the induced function carrier by the construction.
Every ordered refinement is retained, including the empty rank-zero
shape. There is no hypothesis `0 < n` or identification of the two universes.

The source motivation is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10
(1977), 441–472, registered as `bernstein-zelevinsky-1977-induced-i`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The retained original was read directly in text and page images:

- Section 1.8(a), printed p.444 (PDF index 5), defines induction by
  positive-half-modulus covariance, a uniform open right stabilizer,
  and right translation.
- Proposition 1.9(c) and its following explanation, printed p.445
  (PDF index 6), state transitivity for composed subgroup data and
  require compatibility of the normalizing factors.
- Sections 2.2–2.3, printed p.446 (PDF index 7), describe the standard
  block Levi subgroups of `GL_n` by ordered partitions and refinements;
  Proposition 2.3(c) states the corresponding transitivity.

This is an internal coordinate formulation motivated by those passages.
The source compares iterated induction with direct induction in its smooth
representation categories. The present statement compares two direct
constructions using different coordinates for the same refined parabolic.
Its identity-on-functions formulas, arbitrary nonsmooth input, independent
Lean universes, and rank-zero case are internal specifications, not assertions
that these extensions are stated verbatim in the paper.

The constructions here use the source's smooth induction `I`, without
compact support. Section 2.3 uses compact induction `i`; the source's
compactness observation and Proposition 1.9(e) relate the two for
parabolics. This statement neither proves that relation nor identifies
the explicit determinant modulus with the Haar module of conjugation.
It states no nested induction transitivity, character-twist compatibility,
or general natural equivalence of functors.
