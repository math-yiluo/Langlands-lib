# Effective fppf descent of affine group schemes over an arbitrary base

All schemes lie in an arbitrary universe `u`. This module proves that every
Čech datum of an actual group scheme with affine structure map, along a
surjective flat map locally of finite presentation, has a solution. The base
is arbitrary. It is the fppf analogue of the published module
`Langlands.GroupScheme.Descent.EtaleEffectivity`.

- `FppfLocalSolutionGluing.fppfObj_isAffineHom`: in the setting of
  `FppfLocalSolutionGluing`, if every local solution `s i` has an affine
  structure map, then so does the glued object over `B`. Being affine is
  Zariski-local on the target. Over each chart `Uᵢ`, the glued object
  restricts, through Mathlib's cartesian chart square of the gluing, to the
  structure map of `s i`. `fppfSolution_isAffineHom` transfers this to the
  reconstructed group scheme, which has the same underlying object.
- `Datum.fppfSolution : Solution D` for `D : Datum p G` with `p` surjective,
  flat and locally of finite presentation and `G.X.hom` affine. Take the
  published directed affine open cover `B.directedAffineCover`. Each
  restriction of `D` lies over an affine chart, the restricted cover is again
  an fppf surjection, and the restricted group has affine structure map. So
  `fppfAffineBaseSolution` solves each restriction, and
  `FppfLocalSolutionGluing.solution` glues these local solutions.
- `Datum.fppfSolution_isAffineHom`: the descended group scheme has affine
  structure map.

No quasi-compactness of `p` or of `B` is assumed. Provenance is internal: the
published étale effectivity argument with the fppf modules above.
