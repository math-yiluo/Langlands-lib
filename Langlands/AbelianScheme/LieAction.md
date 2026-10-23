# Endomorphism actions on the relative Lie module

For an actual abelian scheme `A` over an arbitrary scheme `S`, this module
constructs the unital ring homomorphism

```lean
Langlands.AbelianScheme.lieEndAction A :
  CategoryTheory.End A →+* CategoryTheory.End A.Lie
```

The source is the endomorphism ring in the existing category of abelian
schemes over `S`. The target is the ring of morphisms from the actual
relative Lie module to itself in `S.Modules`. Thus every value is an
`𝒪_S`-linear morphism of module sheaves. `lieEndAction_apply` identifies
its value at `f` with the existing differential `lieMap f`.

The Lie module is the internal dual of the pullback of the relative
differential sheaf along the identity section. Its differential and
functoriality come from
[LieFunctor](LieFunctor.md). The additive instance used here is the
proved `Langlands.AbelianScheme.lieFunctor_additive` from
[LieAdditivityProof](LieAdditivityProof.md). In particular, this
construction has no hypothesis supplying additivity.

The ring laws are the identity, zero, addition and composition laws of this
specific additive functor. Both endomorphism rings use the convention
`f * g = g ≫ f`, so `map_mul'` applies the functor's composition law to
`g` followed by `f`. These laws establish the integral action without
any additional assumption on the base.

## Rational endomorphisms

Let `R : CommRingCat.{u}` have an `Algebra ℚ R` structure, and let
`p : S ⟶ Spec R` be an actual scheme morphism. The existing construction
`Langlands.Scheme.Modules.rationalLinearOverBase p` makes `S.Modules`
a rational linear category. It obtains the scalar map by composing
`ℚ → R` with the global-section map induced by `p`, and restricts
these global functions on each open; see
[ModuleLinear](../AlgebraicGeometry/ModuleLinear.md).
It therefore also supplies the rational algebra structure on
`CategoryTheory.End A.Lie`.

Using this scalar structure, `lieEnd0Action p A` is a rational algebra
homomorphism

```lean
End0 A →ₐ[ℚ] CategoryTheory.End A.Lie
```

Here `End0 A` is the actual endomorphism algebra of `A` in the published
rational category, with underlying module
`ℚ ⊗[ℤ] CategoryTheory.End A`; see [Rational](Rational.md).
The definition specializes
`Langlands.Rationalization.liftEnd` to the existing additive Lie functor.
That construction uses the tensor universal property to extend
`(q, f) ↦ q • lieMap f` and proves all the algebra homomorphism laws;
see [RationalizationLift](../CategoryTheory/RationalizationLift.md).

The two compatibility lemmas give the defining formulas:

```text
lieEnd0Action p A (endToEnd0 A f) = lieEndAction A f
lieEnd0Action p A (q ⊗ₜ[ℤ] f) = q • lieMap f.
```

The first follows from `Rationalization.liftEnd_ofEnd`. The second is
definitional after installing the scalar structure from `p`. The
rational scalar action on the right is precisely the one obtained
from the actual base morphism described above. The rational construction
is stated only with that rational base data.

## Provenance and scope

This module is a derived specialization of the published Lie functor,
its geometric additivity proof, the module-sheaf scalar construction,
and the rationalization extension. Their paired Markdown files describe
the geometric sources and the algebraic constructions. No additional
external theorem is used or asserted here. Worker 132 wrote this
specialization and its explanation.

The module supplies the integral and rational endomorphism actions and
their displayed formulas. Base-change isomorphisms, local freeness and
rank remain in their separate statements and proofs.
