# The weighted Siegel norm is controlled by boxes and residuals of components

Module `Langlands.Global.AdelicLocalFinitenessChamberEmbedding` (namespace
`Langlands.Global.StandardConstantTerm`). Setting of `AdelicLocalFinitenessChamberSlabs`: a
connected reductive group `G` over a number field, a maximal split torus `i`, a generic
cocharacter `ν`, an Iwasawa compact `K` for the represented standard minimal parabolic, chamber
coordinates `chamberCoords hK e g = e(H₀(g))` with root part indexed by the simple roots `Δ` and
`r` central coordinates; `D₀` is the fundamental domain of the image `Λ₀` of `P₀(F)`.

## Definition

`orthantBox c τ J ε m = {g | 0 < orthantHeight c τ J ε k g ≤ m_k for all directions k}`, the
box of the orthant heights with upper endpoints the degrees `m_k`.

## The estimate `exists_chamberEmbedding`

Hypotheses:

- `a_β` (`β ∈ Δ`) and `z_j` (`j < r`) shift the chamber coordinates by the unit vectors,
  `chamberCoords(a_β g) = chamberCoords(g) + e_β`, `chamberCoords(z_j g) = chamberCoords(g) + e_j`;
- for every `J ⊆ Δ`, the points `a_β` with `β ∉ J` and all `z_j` commute with `L_J(𝔸)` and
  normalize `U_J(𝔸)` in both directions;
- a finite index type of components `P` with sets `J_P ⊆ Δ`, thresholds `τ` and a coefficient
  bound `M`.

Conclusion: there is `R₀ ≥ 0` such that for all rates `ra_β ≥ R₀`, `rb_j ≥ R₀`, all degrees
`m_{P,ε,k}` and all lower coefficient families `p_{P,ε,k}` with `∑_q ‖p_{P,ε,k,q}‖ ≤ M` there is
`C ≥ 0` with the following property. Let `μ_B = W · Haar|_{D₀}` with `W` the Siegel weight
`siegelWeight (chamberCoords hK e) ra rb τ` (module `AdelicLocalFinitenessOrthantCombination`).
Let `f` and components `φ_P` be measurable, each `φ_P` left invariant under `Λ₀ ⊔ U_{J_P}(𝔸)`,
with `f = ∑_P φ_P` `μ_B`-almost everywhere. If every `φ_P` is square integrable on the boxes
`orthantBox (…) τ J_P ε (m_{P,ε})` and every residual
`residualFun F G (orthantShift a z J_P ε k) p_{P,ε,k} φ_P` is square integrable on the positive
regions `orthantPos (…) τ J_P ε`, all for `μ_B`, then `f` is square integrable for `μ_B` and

```
‖f‖_{μ_B} ≤ C ∑_P ∑_ε (‖φ_P‖_{box(P,ε)} + ∑_k ‖residual_{P,ε,k}‖_{pos(P,ε)}).
```

## Proof

For each component `P` and orthant `ε`, `exists_orthantSlabEstimate` gives a threshold
`R(P, ε)`; take `R₀ = ∑ |R(P, ε)|`. For rates at least `R₀` it gives constants `C(P, ε) ≥ 1`.
`siegel_estimate_of_orthants` turns the orthant estimates for `φ_P` into square integrability of
`φ_P` for `μ_B` with norm at most `exp(2 ∑_j rb_j) ∑_ε C(P,ε)(…)`. Then `f` is square integrable as
an almost-everywhere sum, and the triangle inequality (`eLpNorm_sum_le`) gives the bound with
`C = exp(2 ∑_j rb_j) ∑_{P,ε} C(P, ε)`.

## Provenance

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc.
37 (2024), 187–234 (literature id `bernstein-lapid-2024-meromorphic-continuation-eisenstein`),
§7.6, pp. 219–220: with `λ` sufficiently positive, the map `f ↦ (f_P)_P` and the Proposition of
§7.5 (p. 219) make `μ_s` a strict embedding; the same estimate shows that the solutions of
`Ξ_main(s)` lie in `𝓗^λ` (their components satisfy the difference equations and are rapidly
decreasing on the boxes). §7.7 (pp. 220–221) for the orthants. The module states this for an
arbitrary decomposition of `f` into invariant components, so that it applies both to the
Harish-Chandra components of `L²` vectors and to those of solutions.
