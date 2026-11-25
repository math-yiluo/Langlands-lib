# Statement: normal idempotent endomorphisms of a group with almost simple geometric fibres, over any base

`Langlands.GroupScheme.RelativeAlmostSimpleNormalIdempotentStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports
[`Reductive.AlmostSimple`](AlmostSimple.md) (for `IsAlmostSimple` and, through it,
`IsReductive` and `geometricFiber` from [`Reductive.Basic`](Basic.md)) and
[`AffinePoints`](../AffinePoints.md) (for the point functor `affinePointFunctor`, the
point groups `affinePoints` and the maps `affinePointMap`).

It is a derived statement. Mathematically it is the case `B = A` of
[`Reductive.WeilFactorIdempotentRigidityStatement`](WeilFactorIdempotentRigidityStatement.md),
written directly for `G` instead of for the Weil restriction `R_{A/A}(G)`. Informally: if
`G` has almost simple geometric fibres, then over any base change `T` the only normal
idempotent endomorphisms of `G_T` are "the identity over an open and closed part of
`Spec T` and trivial over its complement", one for each idempotent `e` of `T`.

## Statement and quantifiers

The proposition quantifies over

- a commutative ring `B : Type u`;
- a group scheme `G : GroupScheme (Spec B)`;

and assumes

1. `IsReductive G` ([`Reductive.Basic`](Basic.md)): `G` is smooth and affine over
   `Spec B` and its geometric fibres are pseudo-reductive;
2. for every point `s` of `Spec B`, `IsAlmostSimple (geometricFiber G s)`
   ([`Reductive.AlmostSimple`](AlmostSimple.md)): every geometric fibre is semisimple,
   noncommutative, and has no smooth connected closed normal subgroups other than `1` and
   itself.

No separate `IsAffine` or `LocallyOfFiniteType` hypothesis is needed: the point functor
`G.affinePointFunctor` is defined for every group scheme over `Spec B`.

Then it quantifies over

- a `B`-algebra `T : CommAlgCat (CommRingCat.of B)`;
- a natural transformation `θ` from the functor `Under.forget T ⋙ G.affinePointFunctor`
  to itself. Objects `X : Under T` are `B`-algebras `X.right` with a `B`-algebra map
  `X.hom : T ⟶ X.right`, that is, `T`-algebras; the functor sends `X` to the group
  `G(X.right)` of points of `G` with coefficients in `X.right`. So `θ` is an endomorphism
  of the group functor of `G` restricted to `T`-algebras, i.e. an endomorphism of the base
  change `G_T` over `Spec T`.

It assumes

3. `θ ≫ θ = θ` (idempotence);
4. for every `X : Under T` and points `h x` of `G(X.right)`,
   `θ.app X (h * x * h⁻¹) = h * θ.app X x * h⁻¹` (normality: `θ` commutes with every
   inner automorphism, over every `T`-algebra).

The conclusion is that there is exactly one `e : T` such that `e` is idempotent and, for
every `X : Under T` and every point `x` of `G(X.right)`, writing `e' = X.hom.hom e` for
the image of `e` in `X.right`,

- the image of `θ.app X x` under the quotient map `X.right → X.right ⧸ (1 - e')` equals
  the image of `x`, and
- the image of `θ.app X x` under the quotient map `X.right → X.right ⧸ (e')` is `1`.

Images of points are taken with `G.affinePointMap` along the `B`-algebra quotient maps
`Ideal.Quotient.mkₐ B`.

Since `X.right = X.right ⧸ (1 - e') × X.right ⧸ (e')`, the factor `X.right ⧸ (1 - e')`
being the one where `e'` becomes `1`, the conclusion says that `θ` is the identity over
`Spec (T e)` and trivial over `Spec (T (1 - e))`, and that this `e` is unique. (When `G` is
affine, a point of `G` over `X.right` is determined by its two images, so the two
conditions determine `θ`.)

## Mathematical content and correctness

Over an algebraically closed field `k` (`T = k`), `G_k` is almost simple. The image of a
normal endomorphism `θ` of `G_k` is a smooth connected normal subgroup, so it is `1` or
`G_k`; in the second case the idempotent surjection `θ` is the identity, because
`θ ∘ θ = θ` and `θ` is an epimorphism onto the reduced group `G_k`. So `θ` is `1` (`e = 0`)
or the identity (`e = 1`), and `e` is unique because `G_k` is nontrivial. Over a general
`T`, the statement asserts that these fibrewise choices form an open and closed subset of
`Spec T` and that `θ` is determined by them, including over non-reduced `T`. At first
order this is automatic: an idempotent deformation `id + εc` or `1 + εc` of `id` or `1`
satisfies `2εc = εc`, resp. `εc = 0`.

Mathematically the statement is the case `B = A` of
`WeilFactorIdempotentRigidityStatement`, under the identifications `R_{A/A}(G) = G` and
`A ⊗_A T = T`; no formal comparison of the two Lean statements is made here. It is
intended, together with
[`Reductive.WeilAbelianImageTrivialityStatement`](WeilAbelianImageTrivialityStatement.md),
as the input of a formal deduction of `WeilFactorIdempotentRigidityStatement` for general
finite étale `B`: one restricts a normal idempotent endomorphism of `R_{B/A}(G')` to the
`B ⊗_A T`-algebras and the factor of `R_{B/A}(G')` given by the graph idempotent of the
multiplication `B ⊗_A X → X`, which is `G'` itself.

## Source and provenance

Provenance: derived. The statement is not stated in this form in the literature. It is
the intrinsic form, for a single group with almost simple geometric fibres, of the step in
the uniqueness argument of

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014, registered as
`conrad-2014-reductive-group-schemes` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`), printed page
numbers equal to one-based PDF page numbers:

- Proposition 6.4.4, p.232, and its proof, pp.232–233: an isomorphism `∏ G′_i ≃ ∏ G′′_j`
  of products of absolutely simple groups permutes the factors, by the identification of
  the absolutely simple factors with the simple factors of the product over a field
  (Theorem 5.1.19).

The relation is as follows. Over a base where `S′ = ∐_{i ∈ I} S`, `R_{S′/S}(G′) = ∏ G′_i`,
and the factor `G′_i` is the image of a normal idempotent endomorphism; the present
statement says that such endomorphisms of a single `G′_i` are locally on the base `1` or
the identity, which is what makes the factors rigid in families.

## Scope

All rings are in universe `u`; the base is affine. The proposition says nothing about
non-idempotent or non-normal endomorphisms, and nothing about groups whose geometric
fibres are not almost simple.
