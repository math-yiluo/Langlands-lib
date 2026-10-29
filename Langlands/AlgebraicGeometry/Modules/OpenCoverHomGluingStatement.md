# Gluing actual module morphisms over an arbitrary scheme open cover

The proposition
`Langlands.Scheme.Modules.OpenCoverHomGluingStatement.{u}` states that compatible
maps between the pullbacks of two fixed sheaves of modules on a scheme glue to
a unique global module morphism. It uses the actual category
`AlgebraicGeometry.Scheme.Modules`, its actual pullback functors, and actual
scheme fiber products.

## Statement

Let `X : Scheme.{u}` and let `𝒰 : X.OpenCover.{u}`. Write
`uᵢ : Uᵢ ⟶ X` for `𝒰.f i`. The cover index type is arbitrary in universe `u`;
the cover maps are open immersions whose ranges cover `X`.
Fix `M N : X.Modules`, meaning sheaves of modules over the structure sheaf of
`X`. For each index `i`, prescribe a morphism

```text
φᵢ : uᵢ* M ⟶ uᵢ* N.
```

Here `uᵢ*` denotes `AlgebraicGeometry.Scheme.Modules.pullback uᵢ`, on both
objects and morphisms.

For indices `i,j`, let `Pᵢⱼ := Uᵢ ×[X] Uⱼ`, with projections
`p₁ : Pᵢⱼ ⟶ Uᵢ` and `p₂ : Pᵢⱼ ⟶ Uⱼ`. The equality
`p₁ ≫ uᵢ = p₂ ≫ uⱼ` is the categorical `pullback.condition`.
For either `A = M` or `A = N`, the published
[`squarePullbackIso`](SquarePullbackComparison.md), applied as

```text
squarePullbackIso uⱼ p₁ p₂ uᵢ pullback.condition A,
```

gives an isomorphism

```text
α_A : p₁* (uᵢ* A) ≅ p₂* (uⱼ* A).
```

The compatibility hypothesis requires, for every ordered pair `i,j`,

```text
p₁*(φᵢ) ≫ α_N.hom = α_M.hom ≫ p₂*(φⱼ).
```

Both sides are morphisms from `p₁*(uᵢ* M)` to `p₂*(uⱼ* N)`. Thus the
hypothesis compares the prescribed maps on the overlap using the canonical
comparison between the two iterated actual pullbacks.

The conclusion is

```text
∃! f : M ⟶ N, ∀ i, uᵢ*(f) = φᵢ.
```

It requires equality of actual module morphisms on every cover member.
Uniqueness ranges over all global maps satisfying these equalities.

## Scope

The proposition quantifies over every scheme in universe `u` and every such
open cover. It imposes no reducedness, quasi-separatedness, quasi-compactness,
affineness or finiteness condition. The modules need not be quasi-coherent,
locally free, finitely presented or of any specified rank.

The two global module sheaves `M` and `N` are fixed before the local maps are
given. The statement concerns gluing their morphisms. It does not formulate
descent of module objects, gluing of isomorphism classes, or a sheaf assertion
for an ordinary or rigidified Picard functor. It introduces a Prop-valued `def`;
this file supplies the proposition to be proved, not a proof of it.

## Internal provenance

This is an internal formulation of locality for morphisms of sheaves of
modules. Its mathematical rationale is the sheaf of local module morphisms:
compatible local morphisms determine a global morphism, and the separatedness
part of the sheaf condition gives uniqueness. Pullback along an open immersion
identifies with restriction. Transporting this locality principle through those
identifications yields the displayed compatibility equation with
`squarePullbackIso`. In particular, this principle applies to arbitrary
structure-sheaf modules and arbitrary open covers.

The existing Library's
[`ModuleDual`](../ModuleDual.md) constructs `internalHom M N` as an actual
sheaf of modules. Its `LocalHom.restrict` and `internalHom_restrict` describe
restriction of local morphisms, and `internalHomSectionsEquiv` identifies
sections over an open with morphisms of the restricted modules.
[`ModuleLocalHomPullbackProofs`](../ModuleLocalHomPullbackProofs.md) and
[`ModuleLocalHomPullbackCoherenceProofs`](../ModuleLocalHomPullbackCoherenceProofs.md)
provide restriction and coherence results for the actual pullbacks.
These are possible ingredients of a later proof; this statement does not
assert that those ingredients already prove the exact gluing proposition.

The Lean interface was supplied by Worker 453 for use in the separatedness
argument for actual rigidified abelian-scheme classes. This module isolates
the general module-morphism locality prerequisite and leaves that consumer's
final proof assembly separate. The cited source below does not state this
open-cover, pullback-based formulation; the formulation is derived internally
from the background principle recorded there.

## Source

- `stacks-relative-differentials-internal-hom-2026-10-21`, folder SHA256
  `9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`,
  retained file `01CM.html` (SHA256
  `2e397262fb849588b5d272defc4ee6e6bbac9143fd3a23bb74b0892d56e06fac`),
  opening paragraph of Stacks Project, Modules, Section 17.22 (tag 01CM). For
  modules `F`, `G` on a ringed space `X`, it says that the rule
  `U ↦ Hom_{O_X|_U}(F|_U, G|_U)` is a sheaf of abelian groups. Section 17.22
  attributes this to Sheaves, Section 6.33; that section was not consulted
  here. Specialized to a scheme and to the open cover by the images of the
  `uᵢ`, this sheaf property says that module morphisms on those opens which
  agree on pairwise intersections glue to a unique global morphism. That is
  the restriction-based form of the proposition above. The Lean form, which
  uses pullbacks along the cover maps and `squarePullbackIso` on fiber
  products, is an internal reformulation of it.
