# Effective gluing of supplied local fppf solutions

This module is the fppf analogue of the published module
`Langlands.GroupScheme.Descent.LocalSolutionEffectivity`. All schemes lie in
an arbitrary universe `u`. The setting is that of `FppfLocalSolutionGluing`:
`p : S ⟶ B` is surjective, flat and locally of finite presentation, `D` is a
Čech datum for `G`, and `𝒰` is a locally directed open cover of `B` with a
small, thin index category. Each `s i` is a solution of
`D.baseChange (𝒰.f i)`.

- `move_proj_of_chart`: let `a : Z ⟶ G.X.left` be a test point, `b : Z ⟶ S`
  a second point with the same image in `B`, and `z : Z ⟶ Uᵢ` a chart
  coordinate of that image. Then `a` and its transport `D.move a b h` have
  the same image under the glued projection `proj`. Lift both to the
  restricted covering group over `Vᵢ = S ×_B Uᵢ`. The published
  `move_reindex_fst` identifies the transport of the restricted datum with
  `D.move`. The published `SchemeSolution.move_proj` applies to `s i`, and
  `local_proj` connects the result to `proj`.
- `relation`: `D.source ≫ proj = D.target ≫ proj`. This is checked on the
  pullback of `𝒰` to the relation scheme, where every point has a chart
  coordinate, using `move_proj_of_chart` and the published `move_relation`.
- `schemeSolution : SchemeSolution D` packages the glued object, `proj`, the
  pullback square of `FppfLocalSolutionGluing.square` and `relation`.
- `solution : Solution D` is `(schemeSolution D 𝒰 s).fppfSolution` from
  `FppfSchemeSolutionGroup`.

Provenance is internal: these are the published étale arguments with the fppf
group reconstruction. There is no literature assertion.
