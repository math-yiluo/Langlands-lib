# Gluing closed subschemes along an open cover

Author: Worker 1535.

This module proves that closed subschemes defined on the members of an open
cover of a scheme glue to one closed subscheme. The gluing data is a
condition on points, so no ideal sheaf is glued. All schemes are arbitrary
`Scheme.{u}` and the cover may be indexed by any `ι : Type u`. There is no
quasi-compactness, separatedness, affineness or finiteness assumption.

## Setting

Fix a scheme `X` and a condition `P z` on morphisms `z : Z ⟶ X` from
arbitrary schemes `Z` (points of `X` with values in `Z`). The hypothesis
`hP` says that `P` is stable under precomposition: `P z` implies
`P (a ≫ z)` for every `a : Z' ⟶ Z`.

* `subfunctor P hP : Scheme.{u}ᵒᵖ ⥤ Type u` sends `Z` to the type of
  morphisms `z : Z ⟶ X` with `P z`, with restriction by precomposition.
* `isSheaf_subfunctor hP hloc` proves that this presheaf is a sheaf for the
  Zariski topology on schemes, provided `P` is local on the source in the
  following pointwise sense (`hloc`): if every point `p` of `Z` has an open
  neighbourhood `U` with `P (U.ι ≫ z)`, then `P z`. The section over a
  cover is obtained by gluing the given morphisms with
  `Scheme.Cover.glueMorphisms`. It satisfies `P` by `hloc`, applied to the
  images of the cover members.
* `IsChart P v c`, for `v : V ⟶ X` and `c : L ⟶ V`, states that for every
  `z : Z ⟶ V`, `P (z ≫ v)` holds if and only if `z` factors through `c`.
  When `v` is an open immersion and `c` is a closed immersion, this says
  that `c` is a closed subscheme of the open subscheme `V` representing `P`
  over `V`.

## Main theorem

`exists_isClosedImmersion` takes:

* a family of open immersions `v i : V i ⟶ X` whose ranges cover `X`
  (`hcov`),
* closed immersions `c i : L i ⟶ V i` with `IsChart P (v i) (c i)` for
  every `i` (`hc`),
* the locality hypothesis `hloc` above.

It produces a scheme `L₀` and a closed immersion `c₀ : L₀ ⟶ X` such that,
for every scheme `Z` and every `z : Z ⟶ X`, `P z` holds if and only if `z`
factors through `c₀`.

## Proof

The proof applies Mathlib's local representability criterion for Zariski
sheaves, `AlgebraicGeometry.Scheme.LocalRepresentability.representableBy`
(Stacks Project, Tag 01JJ), to the sheaf `subfunctor P hP`.

* `chart hP hc : yoneda.obj L ⟶ subfunctor P hP` is the morphism given by
  the point `c ≫ v`. This point satisfies `P` by `isChart_self`.
* `exists_factor` proves that for a point `y : T ⟶ X` with `P y`, the
  restriction of `y` to the open `y ⁻¹ᵁ v.opensRange` factors through
  `c ≫ v`. First lift that restriction through the open immersion `v`. The
  chart condition then factors the lift through `c`.
* `isOpenImmersion_chart` proves that `chart hP hc` is relatively
  representable by open immersions (`IsOpenImmersion.presheaf`). Its
  pullback along a point `y` of `subfunctor P hP` over `T` is the open
  subscheme `y ⁻¹ᵁ v.opensRange` of `T`. The pullback square is checked
  objectwise as a pullback of types, using that `c ≫ v` is a monomorphism.
* `isLocallySurjective_chart` proves that the induced morphism from the
  coproduct of the `yoneda.obj (L i)` is locally surjective for the Zariski
  topology. A point `ξ` over `T` is covered by the opens
  `ξ ⁻¹ᵁ (v i).opensRange`, and on each of them `ξ` lifts to `L i` by
  `exists_factor`.

The criterion then gives a scheme `L₀` representing `subfunctor P hP`. Its
universal point is the morphism `c₀ : L₀ ⟶ X`, which satisfies `P`. The
representing bijection is precomposition with `c₀`, which gives the stated
factorization criterion. The bijection is injective, so `c₀` is a
monomorphism. Being a closed immersion is local on the target, so it is
checked on the cover by the `V i`. The pullback of `c₀` along `v i` is
isomorphic to `L i` over `V i`, so the projection to `V i` is the closed
immersion `c i` up to isomorphism. In one direction, the projection
satisfies `P` after composition with `v i` and so factors through `c i`.
In the other, `c i ≫ v i` satisfies `P` and so factors through `c₀`. The two
composites are identities, because `c₀` and `c i` are monomorphisms.

## Provenance

These are internal lemmas for the construction of the moduli of closed
torus subgroups. They state the standard fact that closed subschemes
glue along an open cover, phrased through the functor of points they
represent. The gluing itself is Mathlib's implementation of Stacks Project
Tag 01JJ. The Lean proof is the argument described above.
