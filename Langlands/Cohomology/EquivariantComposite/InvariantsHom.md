# Invariants and maps from the trivial representation

Let `R` be a commutative ring and `G` a group, both in universe `u`.
This internal helper supplies the additive comparison needed by the global
composite statement. It is derived from Mathlib's invariants adjunction and
its APIs for additive functors, linear maps, and homology; it makes no new
claim from external literature.

`trivialHomInvariantsAddEquiv R G M` identifies equivariant maps from the
trivial representation on `R` to `M` with the invariant submodule of `M`,
viewed as an additive group. The map evaluates an intertwiner at `1`.
Its inverse sends an invariant vector `m` to the map `r ↦ r • m`.
The implementation composes the additive form of `Rep.invariantsAdjunction`,
`ModuleCat.homAddEquiv`, and `LinearMap.ringLmapEquivSelf`. Additivity of the
trivial-representation functor is obtained from the adjunction and the
additivity of invariants.

`invariantsHomIso R G` packages the inverse equivalences as a natural
isomorphism

```
Rep.invariantsFunctor R G ⋙ forget₂ (ModuleCat R) AddCommGrpCat
  ≅ preadditiveCoyoneda.obj (op (Rep.trivial R G R)).
```

Naturality says that applying an intertwiner to an invariant vector agrees
with postcomposing its corresponding map from the trivial representation.
For the forward evaluation maps this is a definitional equality.

For every complex shape `c` and degree `i`, `invariantsHomologyIso R G c i`
identifies the underlying additive group of the homology of termwise
invariants with the homology of termwise additive Hom from the trivial
representation. It is natural in the complex. The proof uses exactness of
`forget₂ (ModuleCat R) AddCommGrpCat` to commute forgetting with homology,
then applies `invariantsHomIso` termwise and takes homology. The first step
uses the inverse of the published `LeftExactHomology.homologyNatTrans`.

There are no topological, finiteness, injectivity, or derived-category
hypotheses. This module does not itself assert the full derived comparison.
