# Affine scheme pushout from a ring pullback

The Prop-valued definition
`Langlands.AlgebraicGeometry.AffineSchemePushoutStatement.{u}` states:

```lean
∀ (A B C D : CommRingCat.{u}) (f : B ⟶ D) (g : C ⟶ D)
  (i : A ⟶ B) (j : A ⟶ C),
  Function.Surjective f.hom →
    IsPullback i j f g →
      IsPushout (Spec.map f) (Spec.map g) (Spec.map i) (Spec.map j)
```

Here `IsPullback i j f g` is the categorical pullback property in
`CommRingCat`, including `i ≫ f = j ≫ g`. The conclusion is the
categorical pushout property in `Scheme` for the square

```text
Spec D --Spec.map f--> Spec B
   |                     |
Spec.map g           Spec.map i
   |                     |
   v                     v
Spec C --Spec.map j--> Spec A.
```

In particular, for every scheme `X` and compatible morphisms
`m : Spec B ⟶ X` and `n : Spec C ⟶ X`, there is a unique morphism
`h : Spec A ⟶ X` with `Spec.map i ≫ h = m` and
`Spec.map j ≫ h = n`. Compatibility means
`Spec.map f ≫ m = Spec.map g ≫ n`. The target `X` is arbitrary in
`Scheme.{u}`; no affineness condition is imposed.

The rings are arbitrary commutative unital rings in universe `u`.
Nonreduced rings and the zero ring are included. The only premises are
surjectivity of `f.hom` and the displayed ring pullback property.

## Original source and derived formulation

The original source is The Stacks Project Authors, *More on Morphisms*,
[Lemma 37.14.1, Tag 0ET0](https://stacks.math.columbia.edu/tag/0ET0),
statement and proof. Its notation corresponds as follows:

| Stacks notation | This statement |
| --- | --- |
| `A'` | `B` |
| `A` | `D` |
| `B` | `C` |
| `B' = B ×_A A'` | the pullback ring `A` |
| `A' → A` | `f : B ⟶ D` |
| `B → A` | `g : C ⟶ D` |
| `B' → A'` | `i : A ⟶ B` |
| `B' → B` | `j : A ⟶ C` |

Thus the source's schemes `S`, `S'`, `T`, and `T'` correspond to
`Spec D`, `Spec B`, `Spec C`, and `Spec A`, respectively.
The source constructs its canonical fibre-product ring. The present
formulation is derived by replacing that ring with an arbitrary
categorical pullback cone: uniqueness of pullbacks gives a unique ring
isomorphism respecting both projections. Applying the contravariant
`Spec` functor gives an isomorphism of the displayed scheme squares,
along which the pushout property transports. This explains the
provenance of the formulation; this file supplies no formal proof of
that transport or of the pushout assertion.

The retained source is
`literature/Stacks Project - Affine and integral scheme pushouts, Tags 0ET0 07RS 0ECI 0E25 0ECH (HTML snapshot 2026-11-06)/0ET0.html`,
registered as `stacks-affine-integral-scheme-pushouts-2026-11-06`.
The registered folder SHA-256 is
`9d19931877f5d355ef57ff7ab05e2283e39200a03a656fa7c4c3f59ed9153c7e`;
the original `0ET0.html` SHA-256 is
`bbbfdcd78318dc3aef0acc1615cef57eb793f430e96986a119ab7808daf558d9`.

## Scope

A canonical subring-and-contained-ideal comparison establishes a
particular ring pullback square. This statement starts with a ring
pullback square and asserts its scheme pushout property. A ring pushout,
such as a tensor-product square, instead gives a scheme pullback.
These are distinct mathematical assertions.

Global conductor gluing requires additional construction and
affine-neighborhood arguments. In the same retained source,
[Situation 37.67.1, Tag 0ECI](https://stacks.math.columbia.edu/tag/0ECI)
and [Proposition 37.67.3, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
consider a closed immersion and an integral map with an affine
neighborhood condition on fibres. Their global pushout assertion is
outside this definition. The finite-set affine-neighborhood property
needed in the abelian-scheme application and actual-family Picard
representability also remain separate obligations.

This module defines the proposition only. An exact proof is a separate
successor. Worker 139 supplied the Lean formulation and source
relabelling; Worker 1568 prepared this paired statement for submission.
