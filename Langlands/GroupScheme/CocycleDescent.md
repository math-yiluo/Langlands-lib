# Descent of fibrewise trivial cocycles along fpqc refinements

Authors: Worker 303.

This internal helper extends the natural cocycles of
`Langlands.GroupScheme.TorsorCocycle` and the refinements of
`Langlands.GroupScheme.CocycleRefinement`. It imposes no field, reductivity or
smoothness hypothesis. Fix a base scheme `S`, a group scheme `G` over `S`, covers
`V W : Over S` and a morphism `r : V ⟶ W` over `S`. Call a cocycle
`ζ : Cocycle G V` *fibrewise trivial along `r`* when `ζ.toFun a b = 1` for every
test object `Z` and all `a b : Z ⟶ V` with `a ≫ r = b ≫ r`.

## Results

- `Cocycle.toFun_eq_of_comp_eq`: if `ζ` is fibrewise trivial along `r`, then
  `ζ.toFun a b = ζ.toFun a' b'` whenever `a ≫ r = a' ≫ r` and `b ≫ r = b' ≫ r`.
  The cocycle identity gives
  `ζ(a, b) = ζ(a, a') ζ(a', b') ζ(b', b)`, and the outer factors are `1`.
- `Cocycle.exists_refine_eq_of_comp_eq`: if moreover the underlying scheme map
  `r.left` is quasi-compact, flat and surjective, there is a cocycle
  `ν : Cocycle G W` with `ν.toFun (a ≫ r) (b ≫ r) = ζ.toFun a b` for all tests
  and all `a b : Z ⟶ V`. In other words, `ζ` is the refinement of `ν` along `r`.
- `Cocycle.isTrivial_of_comp_eq`: under the same hypotheses, if every cocycle
  on `W` is trivial, then `ζ` is trivial. If `f : W ⟶ G.X` trivializes `ν`,
  then `r ≫ f` trivializes `ζ`.

## Proof of the descent

The value of `ζ` at the universal pair is a morphism
`ζ₀ : V ⊗ V ⟶ G.X`, where `⊗` is the fibre product over `S`. The map
`(r ⊗ₘ r).left` is quasi-compact, flat and surjective, because these
properties are stable under the fibre product of maps over `S`
(`MorphismProperty.pullbackMap`). Hence it is an effective epimorphism of
schemes. By the first result, `ζ₀` takes equal values on any two points of
`V ⊗ V` with the same image in `W ⊗ W`. Effective descent therefore gives a
morphism `ν₀ : W ⊗ W ⟶ G.X` with `(r ⊗ₘ r) ≫ ν₀ = ζ₀`; it lies over `S`
because `(r ⊗ₘ r).left` is an epimorphism. Set
`ν.toFun a b = lift a b ≫ ν₀`. Naturality is composition with `lift`.

For the cocycle identity it suffices to check it on the universal triple
`(W ⊗ W) ⊗ W`. The map `((r ⊗ₘ r) ⊗ₘ r).left` is again quasi-compact, flat and
surjective, hence an epimorphism. After precomposition with it, the identity
becomes the cocycle identity of `ζ` on the universal triple of `V`, which
holds. The identity on an arbitrary triple `a b c : Z ⟶ W` follows by
composing with `lift (lift a b) c`.

## Provenance

Internal. This is the elementary descent argument for cocycles along an fpqc
refinement, implemented with Mathlib's effective-epimorphism descent for
quasi-compact, flat and surjective morphisms of schemes. It follows the
pattern of `Cocycle.IsTrivial.of_refine` in
`Langlands.GroupScheme.CocycleRefinement`, applied to the cocycle itself rather
than to a trivializing cochain. It is used in
`Langlands.GroupScheme.SimplyConnected.LocalGaloisCocycleVanishingUnramifiedReduction`
with `r` the projection `Spec M ⊗ Spec E ⟶ Spec E`. The module proves no
cohomology vanishing.
