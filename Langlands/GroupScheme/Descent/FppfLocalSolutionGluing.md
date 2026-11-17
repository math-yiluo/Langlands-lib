# Gluing supplied local solutions of fppf data over a directed open cover

This module is the fppf analogue of the published module
`Langlands.GroupScheme.Descent.LocalSolutionGluing`. It reuses that module's
cover constructions (`LocalSolutionGluing.cover`, `coverMap`, `groupMap`,
`groupCover`), which need no hypothesis on `p`. All schemes lie in an
arbitrary universe `u`.

Let `p : S ⟶ B` be surjective, flat and locally of finite presentation, `G`
an actual group scheme over `S`, and `D : Datum p G`. Let `𝒰` be a locally
directed open cover of `B`, with a category structure on its index type.
Suppose each `i` has a solution `s i` of `D.baseChange (𝒰.f i)`. Write
`Vᵢ = S ×_B Uᵢ`. The projection `rᵢ : Vᵢ ⟶ Uᵢ` is a base change of `p`, hence
again an fppf surjection, as `FppfLocalSolutionComparison` requires.

- `map hij`: for `i ⟶ j`, the map between the local quotient schemes given by
  `Datum.fppfLocalSolutionMap`. `proj_map` is the identity
  `(s i).schemeProj ≫ map hij = groupMap hij ≫ (s j).schemeProj`, and
  `map_square` says that `map hij` is a pullback of `Uᵢ ⟶ Uⱼ`.
- `map_id` and `map_comp` follow by cancelling the epimorphism
  `(s i).schemeProj` and comparing pullback projections of the group maps.
  Hence `functor` is a functor from the index category to schemes, `natTrans`
  collects the structure maps to the charts, and `data` is a Mathlib
  `RelativeGluingData` (its `equifibered` field is `map_square`).
- Assume further `Small.{u} 𝒰.I₀` and `Quiver.IsThin 𝒰.I₀`. Mathlib's relative
  gluing gives the colimit, and `obj : Over B` is the glued scheme with its map
  to `B`. `proj_compatible` makes the maps `(s i).schemeProj ≫ colimit.ι i`
  agree on overlaps of `groupCover`, so they glue to
  `proj : G.X.left ⟶ (obj …).left`. `local_proj` recovers each local piece.
- `square`: `IsPullback G.X.hom proj p (obj …).hom`. This is checked on the
  pulled-back open cover of `S`. There each square is the quotient square of
  `s i` pasted with Mathlib's cartesian chart square of the gluing.

Like the published module, this one does not prove invariance of `proj` under
the relation; `FppfLocalSolutionEffectivity` does that. Provenance is
internal: the published étale arguments with `FppfLocalSolutionComparison`.
