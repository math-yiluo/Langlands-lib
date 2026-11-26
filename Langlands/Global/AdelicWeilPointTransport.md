# Naturality of the adelic Weil point comparison

The canonical adelic point equivalence for an affine Weil restriction commutes with homomorphisms of the upper-field groups. The proof combines `AffineWeil.map_affinePoints`, which gives naturality on tensor-valued points, with `GroupScheme.affinePointsTarget_naturality` for the canonical adele tensor map. This is a functorial consequence of the Weil comparison in Springer, *Reduction theory over global fields*, §1.4, pp. 208–209, `springer-1994-reduction-global-fields`, SHA-256 `774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`.

For group schemes over a single number field, `AdelicGroupPoints.adelicPointsIso` evaluates a group-scheme isomorphism on the adelic coefficient algebra. The existing continuity of `AdelicGroupPoints.map` makes the resulting point equivalence a topological group isomorphism.
