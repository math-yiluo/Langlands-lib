# Lifting fibre morphisms and actual point fibres

This is an internal construction from Mathlib's `ULiftHom` and the published
`PseudofunctorPointFiber` construction. It does not invoke an external
algebraicity theorem. All base, fibre-object and fibre-morphism universes are
arbitrary and independent.

For a contravariant category-valued pseudofunctor `F` on a category `C`,
`homLift.{w} F` has fibre `ULiftHom.{w} (F.obj X)` at `X`. The objects are the
original objects and each morphism is its explicit `ULift`. The functor
`liftFunctor` applies the original pullback functor to the underlying morphism
and lifts the result. The identity and composition comparisons come from
`liftNatIso`, which lifts the components of the original comparison. The three
pseudofunctor coherence equations follow by evaluating the original equations,
projecting through `ULift.down`, and reducing identity transports. No coherence
is replaced by a new assumption.

For any objects `ξ` over `U` and `η` over `T`, `pointsEquiv ξ η Z` identifies the
actual point type of the lifted pseudofunctor over `Z → T` with
`ULift.{w} (PseudofunctorPointFiber.Points F ξ η Z)`. It keeps the actual map
`Z.left → U` and applies `ULiftHom.down.mapIso` to the actual isomorphism.
The inverse keeps the same map and uses `ULiftHom.up.mapIso`. The inverse
identities follow from the corresponding identities on the underlying
isomorphism components. In particular, this equivalence does not discard or
quotient the isomorphism data.

`pullIso_down` proves that forgetting the morphism lift commutes with the
coherent isomorphism pullback. Its proof substitutes the two prescribed
composite base maps, reduces `mapComp'` to `mapComp`, and compares the
isomorphism components. `pointsEquiv_restrict` applies this identity to every
morphism in the entire slice `Over T`.

Finally, `presheafIso` assembles the point equivalences into a natural
isomorphism

```
PseudofunctorPointFiber.presheaf (homLift.{w} F) (objUp ξ) (objUp η)
  ≅ PseudofunctorPointFiber.presheaf F ξ η ⋙ uliftFunctor.{w}.
```

Its naturality is exactly `pointsEquiv_restrict`; thus it compares the whole
presheaves and all their restriction maps. When `C` is a category of schemes
over a base, every slice test is retained, including empty, nonreduced and
non-quasi-compact schemes. This construction changes only the morphism universe.
It supplies no stack descent, represented point fibre, scheme atlas or Picard
algebraicity existence theorem.
