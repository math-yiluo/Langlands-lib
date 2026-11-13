# Statement: restricting the group gives morphisms of sites `X(H)_qét → X(G)_qét`

Author: Worker 21.

This module states, without proof, that for a continuous homomorphism
`f : H → G` and a `G`-space `X`, restriction `U(G) ↦ U(H)` defines morphisms
of sites `X(H)_qét → X(G)_qét` and `X(H)_ét → X(G)_ét`. The statement is the
proposition
`Langlands.Analytic.SaturatedAtlasPresentation.RestrictionSiteMorphismStatement`.

## Original source

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.2, printed p.3:

> any morphism φ : X′(G′) → X(G) gives rise in the evident way to morphisms
> of sites X′(G′)_qét → X(G)_qét and X′(G′)_ét → X(G)_ét and to morphisms of
> the corresponding topoi. For a quasi-étale (resp. étale) sheaf F′ on
> X′(G′), the value of φ_*F′ on U(G) over X(G) is F′((X′ ×_X U)(G′))

This module states the case of the morphism `X(H) → X(G)` given by `f` and the
identity of `X`. That morphism is `SpaceWithOperators.resLift` in module
`SpacesWithOperators`, the fixed-`K` part of Berkovich's category `𝒜n^op`.
Here `X′ = X`, so `X′ ×_X U = U`, and Berkovich's formula reads
`φ_*F′(U(G)) = F′(U(H))`. The functor of sites is therefore restriction
`U(G) ↦ U(H)`. For general morphisms of `𝒜n^op` the functor needs fibre
products `X′ ×_X U`, which the Library does not have in general; they are not
stated here.

Examples are Berkovich's morphisms `a : X(G_d) → X(G)` and `b : X → X(G)` of
Example 1.1.3 (printed p.3), with `f` the identity `G_d → G` and the trivial
homomorphism `{1} → G`.

## Statement

`RestrictionSiteMorphismStatement : Prop`. For every complete ultrametric
normed field `K : Type u`, groups with topologies `G : Type z` and
`H : Type z'`, every continuous homomorphism `f : H →ₜ* G` and every `G`-space
`X : GSpace.{u, v, v} K G`:

1. `EquivariantQuasiEtaleSite.res f : Qét(X(G)) ⥤ Qét(X(H))` (module
   `EquivariantQuasiEtaleSite`) is representably flat (Mathlib's
   `RepresentablyFlat`) and continuous (Mathlib's `Functor.IsContinuous`) for
   `equivariantQuasiEtaleTopology X` and
   `equivariantQuasiEtaleTopology ((GSpace.res f).obj X)`;
2. `EquivariantEtaleSite.res f : Ét(X(G)) ⥤ Ét(X(H))` (module
   `EquivariantEtaleSite`) is representably flat and continuous for
   `equivariantEtaleTopology X` and
   `equivariantEtaleTopology ((GSpace.res f).obj X)`.

"Morphism of sites" is rendered as in the Library's
`SetInducedSpace.MorphismOfSitesStatement`: continuous and representably flat,
the conditions under which Mathlib's `Mathlib.CategoryTheory.Sites.Pullback`
treats a functor as a morphism of sites in the sense of SGA 4 IV 4.9.

## Notes

- The Library already proves that restriction preserves and reflects
  coverings (`EquivariantQuasiEtaleSite.map_res_mem_equivariantQuasiEtalePrecoverage_iff`
  and its étale analogue). For a representably flat functor, Mathlib's
  `Functor.isContinuous_iff_coverPreserving` makes continuity the same as
  preserving covering sieves. The open part of the statement is mainly
  representable flatness: for `V(H)` over `X(H)`, the category of pairs
  `(U(G), V → U)` over `X` must be cofiltered. The expected proof uses
  products `U₁ ×_X U₂` with the diagonal action and equalizers of
  `G`-morphisms over `X`.
- Berkovich works with topological groups. The Library's sites only need
  groups with topologies, and the statement is quantified the same way.
- This is a `lean.statement`: nothing is proved here.
