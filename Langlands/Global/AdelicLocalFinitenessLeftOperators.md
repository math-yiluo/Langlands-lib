# The left-hand operator family of the boundary model

Module `Langlands.Global.AdelicLocalFinitenessLeftOperators` (namespace
`StandardParabolicFamily`). Setting of `AdelicLocalFinitenessResidualOperators`: a compatible
standard parabolic family `𝓕`, an Iwasawa subgroup `K` of the standard minimal parabolic `P₀`,
chamber coordinates `e` with `r` central coordinates, rates `ra`, `rb` and thresholds `τ`.

## Definitions

- `BoundaryDirection P r`: the directions of a component `P`, i.e. the simple roots outside its
  Levi index `J_P = P ∩ Δ` and the central indices `Fin r`.
- `BoundaryIndex r`: the coordinates `ω = (P, ε, o)` with `P ⊆ Δ` a component (a member of the
  powerset of the simple roots), `ε` an orthant, and `o = none` (the box) or `o = some k` (a
  direction).
- `boundaryRegion hK e τ m ω`: the box `orthantBox (chamberCoords hK e) τ J_P ε (m P ε)` for
  `o = none`, the positive region `orthantPos (chamberCoords hK e) τ J_P ε` for `o = some k`.
- `siegelHilbert hK e ra τ rb`: the weighted Hilbert space (`WeightedSiegel.HilbertSpace`) of the
  Siegel region `siegelHeightRegion e τ` for the log weight `localFinitenessLogWeight ra rb ∘ e`.
- `siegelEmbedding`: the linear isometry of `siegelHilbert` into `L²` of the Siegel weight on
  `G(𝔸)` (`siegelHaar`), the frame embedding of `AdelicLocalFinitenessSiegelFrame` followed by the
  identification `measurePreserving_id_siegelHaar` of the frame measure with `siegelHaar`
  (`frameMeasure_eq_domainWeightedHaar`). `siegelEmbedding_ae`: it is composition with
  `G(𝔸) → G(F) \ G(𝔸)` on representatives.
- `boundaryLhsCore E Lsh m p ω`: the operator `E P` for the box and the residual operator
  `residualOperator (Lsh P ε k) (p P ε k) = Lsh P ε k m + ∑_q p_q Lsh P ε k q` for a direction.
- `boundaryLhs … E Lsh m p s`: the assembly (`piAssemble`, module `PiOperatorAssembly`) over all
  coordinates `ω` of `restriction to boundaryRegion ω ∘ boundaryLhsCore … (p s) ω ∘ siegelEmbedding`,
  a continuous linear map from `siegelHilbert` to the `ℓ²` product of the `L²` spaces of the
  restricted Siegel measure.

## Results

- `isHolomorphicOperatorFamilyOn_boundaryLhs`: if every coefficient `s ↦ p s P ε k q` is complex
  differentiable on `S`, the family `s ↦ boundaryLhs … p s` is weakly holomorphic on `S`: the box
  coordinates are constant, and the residual coordinates are a fixed operator plus a finite
  combination of fixed operators with differentiable coefficients.
- `isEmbedding_boundaryLhs`: if the strict norm bound
  `‖F‖ ≤ C ∑_{P ⊆ Δ} ∑_ε (‖E P F‖_{box} + ∑_k ‖residualOperator (Lsh P ε k) (p s₀ P ε k) F‖_{pos})`
  holds on `L²` of the Siegel weight (as given by `exists_residualOperators`), then
  `boundaryLhs … p s₀` is a topological embedding: the embedding is isometric, and the right side
  is `C` times the sum of the norms of the coordinates (`isEmbedding_piAssemble`).

## Provenance

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37
(2024), 187–234: (7.3) and §7.6, pp. 219–220 (the operator `μ_s` of the system `Ξ^λ(s)`, given by
the difference operators `D_α(s)(T_{a_α})` applied to the components `f_P^S` and the restrictions of
the components to `S_P^B`, is a strict embedding for `λ` sufficiently positive) and §7.7,
pp. 220–221 (the orthants and the central equations) (literature id
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`). The residual coordinates are restricted
to the positive regions of the orthant heights, as in the strict-embedding estimate of
`AdelicLocalFinitenessChamberEmbedding`.
