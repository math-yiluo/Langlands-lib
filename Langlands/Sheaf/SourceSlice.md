# Source changes for diagrams on slice sites

Author: Worker 13.

This module compares restriction of a reachable global sheaf diagram from one
source slice with reindexing that same diagram. The comparison is constructed,
natural in the global diagram, and compatible with identity and composition.

## Provenance and inputs

This is an internal categorical construction from
[SliceMap](SliceMap.md), using Mathlib's actual `Under.forget`, `Under.map`,
whiskering functors and `NatIso.ofComponents`. It does not introduce a new
literature assertion. At the pinned Mathlib commit, the source definitions are
in `Mathlib/CategoryTheory/Comma/Over/Basic.lean` (the `Under` namespace) and
`Mathlib/CategoryTheory/Sites/Over.lean` (the induced slice topologies,
`overPullback`, `overMapPullback` and their standard comparisons).

Let `C : Type uC` have `Category.{vC} C`, let `J` be a Grothendieck topology
on `C`, and let `A : Type uA` have `Category.{vA} A`. Let the index category
`I : Type uI` have `Category.{vI} I`, and fix `Y : I ⥤ C`. All six
universes are independent. Fix a global sheaf diagram `F : I ⥤ Sheaf J A`.
There is no limit, pullback, sheafification, covering or torsor hypothesis.

Write `Y_k = Y.obj k`, `L_k = J.overPullback A Y_k`, and
`P_f = J.overMapPullback A (Y.map f)` for `f : k → l`.

## The two source changes

`sourceSliceDiagram J A Y k F` is the functor

```text
Under.forget k ⋙ F ⋙ L_k : Under k ⥤ Sheaf (J.over Y_k) A.
```

An object of `Under k` is an arrow `k → i`. The value is `L_k(F_i)`;
its transitions are the restrictions of the original transitions of `F`.

For `f : k → l`, `sourceSliceRestriction J A Y f` postcomposes an
entire `Under l` diagram with `P_f`, changing its slice from `Y_l` to
`Y_k`. The functor `sourceSliceReindex J A Y f` precomposes an entire
`Under k` diagram with `Under.map f : Under l ⥤ Under k`. This sends
an arrow `a : l → i` to `f ≫ a : k → i` and retains its target and
every triangle map.

`sourceSliceChangeIso J A Y f F` compares these constructions:

```text
sourceSliceRestriction(f).obj (sourceSliceDiagram(l,F))
  ≅ sourceSliceReindex(f).obj (sourceSliceDiagram(k,F)).
```

At `i : Under l`, this is precisely
`(overPullbackMapIso J A (Y.map f)).app (F.obj i.right)`.
For `U : Over Y_k`, both section objects are `F_i(U.left)`. The forward
and inverse section maps are identities, as recorded by
`sourceSliceChangeIso_hom_app_hom_app` and its `_inv_` counterpart.
The naturality in `i` is the naturality of `overPullbackMapIso` applied
to `F.map c.right`.

`sourceSliceDiagramFunctor` makes the construction functorial in `F`.
`sourceSliceChangeFunctorIso` assembles the comparisons into a natural
isomorphism of functors with domain `I ⥤ Sheaf J A`. Its naturality
proof checks sections: both routes are the same component of the original
global diagram morphism, composed with identities.

## Coherence

`sourceSliceChangeIso_id` states the component equation for change along
`𝟙 k`. Its right side first uses `overMapPullbackCongr` for the
functor law `Y.map (𝟙 k) = 𝟙 Y_k`, then the standard
`overMapPullbackId` comparison. After reindexing, the target is still
`L_k(F_i)`, because `Under.map` retains `i.right`.

For `f : k → l`, `g : l → m` and `i : Under m`,
`sourceSliceChangeIso_comp` states

```text
P_f.map (change(g,F).hom.app i)
  ≫ change(f,F).hom.app ((Under.map g).obj i)
 =
overMapPullbackComp(Y.map f,Y.map g).hom.app (L_m(F_i))
  ≫ overMapPullbackCongr((Y.map_comp f g).symm).hom.app (L_m(F_i))
  ≫ change(f ≫ g,F).hom.app i.
```

Thus the successive and direct maps have the same endpoints after applying
the actual slice composition comparison and the functor's composition law.
The direct and successively reindexed diagrams retain the same targets and
transition maps under `Under.forget`. These component equations determine
the diagram transformations. The proofs evaluate on sections and simplify
the standard comparisons and identity maps.

## Scope

This compares diagrams obtained by restricting global sheaves. It neither
asserts descent of arbitrary slice sheaves to the global site nor makes a
geometric base-change assertion. It constructs no particular scheme,
cohomology group, inverse limit or comparison with another geometric site.
The index category can be arbitrary; no filtering or cofinality is used.

Formal environment: Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. All intrinsic functoriality,
invertibility and coherence obligations are proved without new axioms or
proof holes.
