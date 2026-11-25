# Gluing supplied local solutions

This internal construction glues the underlying quotient schemes of supplied
local solutions. It uses the exact comparison maps of
`LocalSolutionComparison` and Mathlib's relative scheme gluing.

Let `p : S ⟶ B` be a surjective étale morphism, `G` a group scheme over `S`,
and `D : Datum p G` an actual Čech descent datum. Let `𝒰` be a locally
directed open cover of `B`, with a category structure on its index type.
For every index `i`, assume an actual solution `s i` of
`D.baseChange (𝒰.f i)`. No affineness or quasi-compactness assumption is used.

Write `Vᵢ = S ×[B] Uᵢ`, with projections `qᵢ : Vᵢ ⟶ S` and
`rᵢ : Vᵢ ⟶ Uᵢ`. The restricted covering group is `qᵢ*G`; its quotient
projection is `(s i).schemeProj`.

The cover `cover` is the pullback of `𝒰` to `S`. For a transition `i ⟶ j`,
`coverMap` is its transition `Vᵢ ⟶ Vⱼ`. Its two projection equations are
`coverMap_fst` and `coverMap_snd`. The induced map between restricted covering
groups, `groupMap`, is defined using the actual iterated-pullback comparison.
Its projection equations identify it with the corresponding transition of
`groupCover`, the further pullback cover of `G.X.left`. These cover and group
map constructions do not require étaleness or surjectivity.

For each transition, `map` is the underlying scheme map furnished by
`Datum.localSolutionMap`. The theorem `proj_map` states

```
πᵢ ≫ map(i ⟶ j) = groupMap(i ⟶ j) ≫ πⱼ.
```

The theorem `map_square` says that this map and the two local structure maps
form a pullback square over `Uᵢ ⟶ Uⱼ`. The original cover's étaleness and
surjectivity imply those properties for `rᵢ`, which are precisely the covering
hypotheses needed by the local comparison theorem.

The transition identity and composition laws are proved by precomposing with
the smaller quotient projection, an epimorphism, and comparing the two
projections of the induced covering-group maps. Consequently `functor`
is an actual functor of local quotient schemes, `natTrans` gives their maps
to the base charts, and `data` is Mathlib's `RelativeGluingData`.

Now also assume `Small.{u} 𝒰.I₀` and `Quiver.IsThin 𝒰.I₀`, where all the
schemes lie in universe `u`. Mathlib's relative gluing supplies the colimit
scheme `X` and structure map `X ⟶ B`; `obj` is this actual object of `Over B`.
The theorem `proj_compatible` combines the quotient transition equations
with the colimit cocone equations. It permits gluing the maps
`πᵢ ≫ colimit.ι i` over `groupCover`, yielding
`proj : G.X.left ⟶ X`. The theorem `local_proj` gives its exact recovery
on every restricted covering group.

Finally `square` proves

```
IsPullback G.X.hom (proj D 𝒰 s) p (obj D 𝒰 s).hom.
```

The proof checks the square on the pulled-back open cover of `S`. Each local
square is obtained by pasting the quotient square of `s i` with Mathlib's
cartesian chart square for the relative gluing, and using `local_proj`.

This module constructs an underlying quotient square from supplied local
solutions. It does not prove invariance under `D.source` and `D.target`
(`LocalSolutionGluing.relation` in `LocalSolutionEffectivity` proves it),
nor choose the local solutions, reconstruct the global group, or prove the
quasi-split inner-form existence statement
`RelativeQuasiSplitInnerFormExistenceStatement`. Its provenance is internal:
the implemented arguments are consequences of the imported local comparison,
epimorphism cancellation, and Mathlib's actual scheme gluing construction.
