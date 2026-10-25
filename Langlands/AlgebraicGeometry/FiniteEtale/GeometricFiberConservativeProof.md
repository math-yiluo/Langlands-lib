# Conservativity of one geometric fibre

`Langlands.AlgebraicGeometry.FiniteEtale.geometricFiberConservative` proves
the published proposition `GeometricFiberConservative s hfin` from
`Langlands.AlgebraicGeometry.FiniteEtale.MonoEpiConservativeStatements`.
Its conclusion unfolds to `(fiberFunctor s hfin).ReflectsIsomorphisms`.
It retains the complete parameter list, in this order:

```lean
{S : Scheme.{u}} [ConnectedSpace S] [IsLocallyNoetherian S]
{Ω : Type u} [Field Ω] [IsAlgClosed Ω]
(s : Spec (.of Ω) ⟶ S)
(hfin : ∀ Y : Cover S, Finite (Fiber s Y))
```

Here `Cover S` is the published full subcategory of `Over S` on finite
étale structure morphisms, `Fiber s X` consists of actual morphisms
`Over.mk s ⟶ X.obj`, and the fibre functor acts by postcomposition. The
statement pair and its imports are unchanged. The proof adds no instances
and assumes no Galois-category structure or classification by continuous
actions. Local noetherianity is retained in the main theorem's signature
but is unused; `hfin` supplies the finite-set packaging of the functor.
The two helper theorems require neither of these parameters.

## Surjectivity from one geometric fibre

`cover_surjective_of_fiber_surjective s f h` takes a cover morphism
`f : X ⟶ Y` and surjectivity of
`fun x : Fiber s X => x ≫ f.hom`. It proves `Surjective f.hom.left` for
the underlying scheme morphism.

Write `q : Y ⟶ S` for the structure morphism and `g : X ⟶ Y` for the
underlying morphism. The slice equation is `g ≫ q = X.obj.hom`.
`IsFinite.of_comp` and `Etale.of_comp` show that `g` is finite étale.
Both `g` and `q` are therefore open and closed maps on underlying spaces.
Consequently the complement of the image of `g` is clopen in `Y`, and
its image

```text
bad = q '' (range g)ᶜ
```

is clopen in `S`.

The point `s(default)` does not lie in `bad`. Indeed, a point `y` of `Y`
above it lifts to a morphism `a : Spec Ω ⟶ Y` over `s` by
`Scheme.exists_fac_of_etale_of_isSepClosed`, since `q` is étale and `Ω`
is algebraically closed, hence separably closed. Surjectivity on the actual
geometric fibre lifts `a` through `g`. Evaluating that lift at the point
of `Spec Ω` shows that `y` belongs to `range g`. This contradicts the
definition of `bad` if `y` was a missed point.

In a connected space a clopen set is empty or the whole space
(`isClopen_iff`). The omitted point excludes the second possibility, so
`bad` is empty. A point missed by `g` would give a point of `bad`,
which proves surjectivity.

## Monomorphisms from one geometric fibre

`cover_mono_of_fiber_injective s f h` takes injectivity of the same
postcomposition map and proves `Mono f.hom.left` in `Scheme`.
As above, the underlying map `g` is finite étale.

Let `P = X ×_Y X`, with structure map to `S` obtained from the first
projection followed by the structure map of `X`. Base change and
composition make `P` a finite étale cover of `S`. The diagonal of `g`
defines a cover morphism `d : X ⟶ P`.

For any geometric point `a` of `P` over `s`, its two projections give
points `a₁` and `a₂` of `X` over `s`. They have the same composite with
`g` by the pullback equation. Fibre injectivity gives `a₁ = a₂`.
The pullback universal property then shows that `a` is the diagonal
image of `a₁`. Thus the diagonal is surjective on the specified
geometric fibre, and the first helper makes it surjective as a scheme
morphism.

Since `g` is étale, it is formally unramified, so its diagonal is an
open immersion. Mathlib supplies flatness and monicity of this diagonal.
`Flat.isIso_of_surjective_of_mono` makes the diagonal an isomorphism,
and `pullback.isIso_diagonal_iff` proves that `g` is a monomorphism.
This argument uses equality of morphisms from `Spec Ω`, including
their field data.

## Reflection of isomorphisms

The main theorem constructs the `ReflectsIsomorphisms` witness. If the
fibre map of `f` is an isomorphism in `FintypeCat`, then
`ConcreteCategory.bijective_of_isIso` makes the underlying postcomposition
map bijective. The two helpers give a surjective monomorphism of schemes.
It is étale by the same postcomposition argument and hence flat.
`Flat.isIso_of_surjective_of_mono` now makes the underlying scheme map
an isomorphism. Finally, `isIso_of_reflects_iso` for `Over.forget S`
and for the full-subcategory `inclusion S` transfers this to an
isomorphism in `Cover S`.

The module uses `backward.isDefEq.respectTransparency.types false`,
as does the imported finite-limit and coproduct proof module, to allow
instance search through the morphism-property constructions.

## Provenance

This is an internal proof of the derived conservativity obligation
isolated by the statement module. Its geometric setting is Edixhoven,
van der Geer and Moonen, *Abelian Varieties*, preliminary draft,
Chapter X §3, Definitions (10.25)–(10.26), printed p.150 (PDF p.154),
and Theorem (10.28), printed p.151 (PDF p.155). Registered source:
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The exact target is an internal field obligation towards the
classification theorem, rather than a verbatim assertion at those
locations. The implemented route uses Mathlib's étale lifting theorem,
clopen images, and the diagonal criterion; it introduces no axioms.

Worker 446 authored this proof pair.
