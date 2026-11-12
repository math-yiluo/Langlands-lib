# Final topologies of directed systems of stages

Author: Worker 105.

General topology module. It supports the proof of Conrad's p.17 claims on adelic points of
algebraic spaces (`Langlands.Global.AdelicSpacePointTopologyStatement`). There the adelic points
carry the final topology of the maps from the levels.

## Declarations

Namespace `Langlands.Topology.FinalStage`. A type `Y` has maps `s i : X i → Y` from
topological spaces `X i`.

- `final s`: the final topology `⨆ i, coinduced (s i) (τ i)`.
- `isOpen_final_iff`, `isClosed_final_iff`: a set is open (closed) exactly when all its
  preimages under the stages are open (closed).
- `continuous_stage`: every stage map is continuous.
- `continuous_final_iff`: a map out of `Y` is continuous when its composites with all stages are
  continuous.
- `isOpenEmbedding_stage`: let the index be directed, with transitions `t : X i → X j` for
  `i ≤ j` that are open embeddings and satisfy `s j ∘ t = s i`. If every stage is injective,
  every stage is an open embedding. The preimage in `X j` of an image `s i '' U` equals
  `t⁻¹ (t '' U)`, computed in a common upper bound.
- `continuous_of_stages`: a map `f : Y → Y'` of final topologies is continuous if it is
  compatible with continuous stage maps `fs i : X i → X' i`.
- `isClosedEmbedding_of_stages`: such an `f` is a closed embedding when:
  - it is injective;
  - the stage maps are closed embeddings;
  - a stage point of `Y'` whose image lies in the image of `f` lies in the image of the stage
    map.

  It is continuous and injective. The image of a closed set `C` is closed because its
  preimage in `X' i` is `fs i '' (s i ⁻¹' C)`.
- `isHomeomorph_of_stages`: a bijection of final topologies that is compatible with stage-wise
  homeomorphisms is a homeomorphism. It is continuous by `continuous_of_stages`. It is open
  because the preimage in `X' i` of the image of an open set `U` is `fs i '' (s i ⁻¹' U)`.

Covers by open stages (`Z` a space with maps `u i : X i → Z` that are open embeddings):
- `t2Space_of_stages`: if any two points of `Z` lie in a common stage and the stages are
  Hausdorff, `Z` is Hausdorff.
- `locallyCompactSpace_of_stages`: if every point lies in a stage and the stages are locally
  compact, `Z` is locally compact. Compact neighbourhoods in a stage map to compact
  neighbourhoods.
- `secondCountableTopology_of_stages`: if there are countably many stages, every point lies in a
  stage, and the stages are second countable, then `Z` is second countable. The stage images form
  a countable open cover (`TopologicalSpace.secondCountableTopology_of_countable_cover`).
- `isInducing_of_stages`: consider a map `Φ : Z → W`, where the stages of `W` are open
  embeddings `u' i`, together with stage maps `Φs i : X i → X' i` such that:
  - `Φ ∘ u i = u' i ∘ Φs i`;
  - every point of `Z` lies in a stage;
  - a point of `Z` whose image lies in the stage `u' i` lies in the stage `u i`.

  If every `Φs i` is inducing, so is `Φ`. The proof compares neighbourhood filters:
  `comap Φ (map (u' i) G) = map (u i) (comap (Φs i) G)` for every filter `G` on `X' i`.

