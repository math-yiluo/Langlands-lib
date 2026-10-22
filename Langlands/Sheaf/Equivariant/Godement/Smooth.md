# The smooth equivariant Godement complex

Author: Worker 61. Built on Worker 13's smooth sheaf category
(`Langlands.Sheaf.Equivariant.Smooth`), smooth part and abelian structure
(`Langlands.Sheaf.Equivariant.SmoothPart`,
`Langlands.Sheaf.Equivariant.SmoothAbelian`), on Worker 61's coinduction
(`Langlands.Sheaf.Equivariant.Coinduction`) and underlying comparison
(`Langlands.Sheaf.Equivariant.Godement.Underlying`), and on the published
ordinary Godement construction `Langlands.Sheaf.Godement` and the iterated
cokernel complex `Langlands.Cohomology.CokernelComplex`.

Let `R` be a commutative ring and `G` a topological group acting on a
topological space `X` by continuous translations, with `R`, `G` and `X` in one
universe `u`. Assume `HasStableNeighbourhoods G X`: every point has
arbitrarily small open neighbourhoods stabilized by open subgroups. Smooth
sheaves are the objects of `SmoothTopologicalSheaf R G X`: equivariant
`R`-module sheaves whose sections are locally fixed by open subgroups. Write
`Z` for the published ordinary Godement degree-zero functor
`Sheaf.Godement.zeroFunctor (Cohomology.Flasque.spacePoints (TopCat.of X))
(ModuleCat R)`, the product over all points `x` of `X` of the skyscraper
sheaves of the stalks at `x`, and `η` for its published coaugmentation.

## The adjoint pair

`smoothForget R G X` forgets smoothness and equivariance. It is the inclusion
`smoothInclusion` of smooth sheaves followed by `toSheaf`, and lands in
ordinary sheaves of `R`-modules on `X`. `smoothCoinduction R G X` is
coinduction followed by Worker 13's smooth part `smoothCoreflector`.
`smoothCoinductionAdjunction` composes Worker 13's adjunction
`smoothAdjunction : smoothInclusion ⊣ smoothCoreflector` with the
coinduction adjunction `coinductionAdjunction : toSheaf ⊣ coinduction`, using
Mathlib's `Adjunction.comp`. It proves `smoothForget ⊣ smoothCoinduction`.

`smoothForget_faithful` records that `smoothForget` is faithful, since both
factors are. `smoothForget_additive` records that it is additive: the
inclusion of a full subcategory is additive (Mathlib), and so is `toSheaf`
(the published `toSheaf_additive`). `smoothCoinduction_additive` follows
from Mathlib's `Adjunction.right_adjoint_additive`.

## Degree zero and the coaugmentation

`smoothZeroFunctor R G X` is the composite `smoothForget ⋙ Z ⋙
smoothCoinduction`, an endofunctor of smooth sheaves.
`smoothCoaugmentation R G X : 𝟭 ⟶ smoothZeroFunctor R G X` is the unit of
the adjunction followed by `smoothCoinduction` applied to `η` at the
underlying sheaf. `smoothCoaugmentation_app` identifies each component with
the adjoint, under the adjunction's hom-equivalence, of `η` at the
underlying sheaf. Equivalently, `smoothForget_map_smoothCoaugmentation`
states that after forgetting, the component followed by the counit is `η` at
the underlying sheaf.

`mono_coaugmentation_toSheaf` shows that `η` is monic at every sheaf that
underlies an equivariant module sheaf. The published `zeroIso_comm`
identifies `toSheaf` of the equivariant Godement coaugmentation, followed by
an isomorphism, with `η` at the underlying sheaf. The equivariant
coaugmentation is monic (the published `mono_coaugmentation`), and `toSheaf`
preserves monomorphisms because it preserves pullbacks (the published
`Limits` module). `mono_smoothCoaugmentation_app` deduces that every
component of the smooth coaugmentation is monic. After forgetting, the
component followed by the counit is the monomorphism `η`, so the forgotten
component is monic. A faithful functor reflects monomorphisms.

## The complex

`smoothComplexFunctor R G X` is the published iterated-cokernel complex
`CokernelComplex.functor` for `smoothZeroFunctor` and
`smoothCoaugmentation`, computed in the abelian category of smooth sheaves
(Worker 13's `smoothTopologicalSheaf_abelian`). Degree zero is the degree-zero
functor applied to the sheaf (`smoothComplex_X_zero`). Degree `n + 1` is the
degree-zero functor applied to the cokernel of the previous map.
`smoothAugmentation` is the map from the sheaf into degree zero. It equals the
coaugmentation component (`smoothAugmentation_eq`), composes to zero with
the first differential (`smoothAugmentation_d`), and is monic.

## Provenance and scope

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished
1995–1996 manuscript), section 1.5, printed p.10, adapts the Godement
resolution of SGA 4 XVII 4.2 to the étale site of `X(G)`. It fixes a
discrete set `I` with a surjection onto `X` and a geometric point over each
image, giving a morphism of sites `ν : Top(I) → X(G)_ét`. It sets
`C^0(F) = ν_* ν^*(F)` with the adjunction morphism `F → C^0(F)`, and
`C^{m+1}(F) = C^0(Coker d^{m-1})`. Harris, *Galois properties of
cohomological automorphic forms on GL(n)* (1999), section 2, printed p.304,
uses this smooth `G`-equivariant version of the Godement flasque resolution
for étale sheaves of smooth modules. Worker 61 read these passages in the
original.

The present construction is derived for the ordinary-topological transport
site with all points of `X` (`I = X`, ordinary stalks) and smooth equivariant
module sheaves. Here `ν^*` takes the stalks of the underlying sheaf at the
points. Its right adjoint `ν_*` into smooth sheaves is the ordinary pushforward
from the points followed by the right adjoint of forgetting, which is
`smoothCoinduction`. Hence `ν_* ν^*` is `smoothZeroFunctor`, and Berkovich's
adjunction morphism is `smoothCoaugmentation`. The module proves this
right-adjoint description only in the form of the adjunction and the
identities above. A morphism `F ⟶ smoothZeroFunctor E` corresponds to a
morphism from the underlying sheaf of `F` to `Z` of the underlying sheaf of
`E`, that is, to a family of stalk maps at all points.

The module asserts no exactness of `smoothZeroFunctor` (Berkovich 1.5 (ii),
Harris Fact 3), no flasqueness or softness (Berkovich 1.5 (i) and
Proposition 1.5.1), and no exactness of the complex or comparison with
derived compactly supported cohomology. These remain separate statements. The
setting is not Berkovich's analytic étale site, and geometric points are
replaced by ordinary points of the topological space.

Source registrations:
Berkovich,
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
Harris 1999, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above and Mathlib's
`CategoryTheory.Adjunction.Additive`, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
