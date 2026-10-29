# Faithfully flat descent of module morphisms

Author: Worker 124.

This module states morphism and isomorphism descent between extensions of
modules along faithfully flat homomorphisms of commutative rings. Compatibility
is expressed using the actual extension and restriction of scalars functors,
and the actual unit of their adjunction. The module contains three
proposition definitions.

## Rings, modules and compatibility

Let `A` and `B` be commutative rings in a common universe `u`, and let
`f : A →+* B` satisfy `RingHom.FaithfullyFlat`. Put

- `F = ModuleCat.extendScalars f`;
- `G = ModuleCat.restrictScalars f`;
- `η = (ModuleCat.extendRestrictScalarsAdj f).unit`.

For an `A`-module `M : ModuleCat.{u} A`, its canonical coaction is
`δ_M = F.map (η.app M) : F(M) ⟶ F(G(F(M)))`. These are the canonical
coalgebras for the comonad associated to extension and restriction of scalars.
The unit sends `m` to `1 ⊗ m`, and the coaction sends `b ⊗ m` to
`b ⊗ (1 ⊗ m)`, with all scalar actions induced by the given `f`.
Mathlib's `ModuleCat.extendRestrictScalarsAdj_unit_app_apply` and
`ModuleCat.ExtendScalars.map_tmul` give these formulas.

A `B`-linear morphism `g : F(M) ⟶ F(N)` is compatible when

```text
g ≫ δ_N = δ_M ≫ F.map (G.map g).
```

Here `≫` means first the left map and then the right map. The displayed
equation is exactly the morphism condition for the two canonical coalgebras,
written in the reverse order from the field
`CategoryTheory.Comonad.Coalgebra.Hom.h`. The functors and compatibility
condition are explicit in each Lean proposition; no additional predicate
or choice of comparison maps is introduced.

## The proposition definitions

`Langlands.Algebra.Modules.FaithfullyFlatModuleHomDescentStatement` asserts,
for every such `A`, `B`, `f`, `M`, `N` and compatible `g`, the existence of
exactly one `A`-linear morphism `h : M ⟶ N` with `F.map h = g`.
The modules need not be finitely generated, free or projective.

`Langlands.Algebra.Modules.FaithfullyFlatModuleIsoDescentStatement` asserts,
for every `B`-linear isomorphism `e : F(M) ≅ F(N)` whose forward map
`e.hom` satisfies that same compatibility equation, the existence of exactly
one `A`-linear isomorphism `e₀ : M ≅ N` with `F.mapIso e₀ = e`.
Compatibility of the inverse is a consequence of the displayed condition
and invertibility, so it is not an additional hypothesis.

`Langlands.Algebra.Modules.FaithfullyFlatModuleHomIsoDescentStatement` is
the conjunction of these two proposition definitions, in that order.
Each quantifies the rings, ring structures, homomorphism, faithful flatness,
modules and morphism or isomorphism explicitly. All module carriers are in the
same universe `u` as the rings.

## Provenance and use

This is an internal interface for the algebra step in descending
isomorphisms of line bundles. It is derived from Mathlib's proved faithfully
flat comonadicity theorem `comonadicExtendScalars`, in
`Mathlib/Algebra/Category/ModuleCat/Descent.lean`. The pinned Mathlib commit is
`5ed2965256430c3649e86755f9576b54eca72435`, supplied by the approved project
environment. `CategoryTheory.Comonad.comparison` in
`Mathlib/CategoryTheory/Monad/Adjunction.lean` gives the canonical coactions
and morphism condition used above. This formulation is an internal deduction
from those formal APIs, rather than a transcription of an external source.

The propositions take faithful flatness of the actual ring homomorphism as
their hypothesis. Their intended proof uses Mathlib's theorem to obtain full
faithfulness of the canonical comparison functor. A scheme-level use must
separately identify sheaf pullback and its comparison maps with these module
constructions and glue the resulting local morphisms. Neither that
identification nor effective descent of arbitrary objects is asserted here.
This statement contribution does not prove any of the three propositions.
