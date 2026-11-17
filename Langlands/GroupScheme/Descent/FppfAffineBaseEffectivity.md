# fppf descent of affine groups over an affine base

All schemes lie in an arbitrary universe `u`. Let `B` be affine, let
`p : S ⟶ B` be surjective, flat and locally of finite presentation, and let
`G` be an actual group scheme over `S` with affine structure map. Let
`D : Datum p G` be a Čech datum. Neither `S` nor `G.X.left` needs to be
affine, and `p` need not be quasi-compact.

- `fppfAffineBaseSolution : Solution D`. The published
  `Langlands.AlgebraicGeometry.affineFppfRefinement` gives an affine scheme
  `V` with a map `V ⟶ S` whose composite `V ⟶ B` is flat, surjective and
  locally of finite presentation. The base change of `G` to `V` is affine,
  being affine over the affine `V`. So the published `Datum.affineSolution`
  (module `AffineDatumGroup`) solves the refined datum `D.refine (V ⟶ S)`.
  `Datum.fppfSolutionOfRefinement` (module `FppfReverseRefinement`) turns
  this into a solution of `D`.
- `fppfAffineBaseSolution_isAffine`: the descended group scheme has an affine
  underlying scheme, since it is the object of the affine solution.

This is the fppf analogue of the published `EtaleAffineBaseEffectivity`.
Provenance is internal: the published affine fpqc descent and fppf
refinement, combined through `FppfReverseRefinement`.
