# Comparing actual solutions over nested base restrictions along fppf maps

This module is the fppf analogue of the published module
`Langlands.GroupScheme.Descent.LocalSolutionComparison`. All schemes lie in an
arbitrary universe `u`.

- `Solution.descendHomOfFppf_schemeProj`: let `s : Solution D` and
  `t : Solution F` be solutions over an fppf surjection `p`, and let `f` be a
  compatible homomorphism of the groups over `S`. Descending `f` commutes with
  the quotient maps `schemeProj` (published `Solution.schemeProj`):
  `s.schemeProj ≫ (descendHomOfFppf s t f hf) = f ≫ t.schemeProj` on
  underlying schemes. The recovery square of `FppfHomDescent` gives
  `s.iso.inv ≫ p*(descended map) = f ≫ t.iso.inv`. Composing with the first
  pullback projection gives the claim. `descendIsoOfFppf_schemeProj` is the
  same statement for isomorphisms.

Now let `D : Datum p G` with `p : S ⟶ B` arbitrary. Take a smaller restriction
of the datum through `r : W ⟶ E`, with `r` surjective, flat and locally of
finite presentation, sitting over a larger restriction through `t : V ⟶ C`.
The maps `v : W ⟶ V` and `c : E ⟶ C` connect the two, and the hypotheses
`w₁, w₂, hq, hb, w'` are the commuting squares. Let `s` solve the larger
reindexed datum and `a` the smaller one. Only `r` needs to be an fppf
surjection.

- `fppfLocalSolutionComparison : a.obj ≅ c*s.obj` descends the identity
  between `a` and the published restricted solution `localRestriction … s`.
- `fppfLocalSolutionMap` is the induced map of underlying schemes
  `a.obj.X.left ⟶ s.obj.X.left`.
- `fppfLocalSolutionMap_proj`: its composite with `a.schemeProj` is the
  canonical map of covering groups followed by `s.schemeProj`. This follows
  from `descendIsoOfFppf_schemeProj` and the published `localRestriction_proj`.
- `fppfLocalSolutionMap_square`: this map, `c`, and the two structure maps form
  a pullback square, transported from the canonical pullback through the
  comparison isomorphism.
- `fppfLocalSolutionMap_unique`: the equation in `fppfLocalSolutionMap_proj`
  determines the map, because `a.schemeProj` is an epimorphism (module
  `FppfSchemeSolution`).

Provenance is internal: these are the published étale arguments with the fppf
descent of `FppfHomDescent`, `FppfReverseRefinement` and
`FppfSchemeSolution`.
