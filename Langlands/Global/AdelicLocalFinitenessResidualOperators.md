# Residual and box operators on the weighted Siegel space

Module `Langlands.Global.AdelicLocalFinitenessResidualOperators`. Setting of
`AdelicLocalFinitenessChamberEmbedding`: a compatible standard parabolic family `𝓕` (or a
connected reductive group `G` with maximal split torus `i` and generic cocharacter `ν`), an
Iwasawa compact `K` for the standard minimal parabolic `P₀`, chamber coordinates
`chamberCoords hK e g = e(H₀(g))` with root part indexed by the simple roots `Δ` and `r` central
coordinates, `Λ₀` the image of `P₀(F)` and `D₀` its fundamental domain.

## The Siegel weight

`W = siegelWeight (chamberCoords hK e) ra rb τ` is `exp(−2 ℓ(c))`, `ℓ = localFinitenessLogWeight
ra rb` (`ℓ(x, y) = ∑_β ra_β x_β + ∑_j rb_j |y_j|`), on the region `c ∈ siegelRegion τ` (all root
coordinates `> τ_β`) and zero elsewhere.

- `siegelWeight_le_of_coords`: if `c(y) = c(x) + v` with `v_β ≥ 0` for every root `β`, then
  `W(x) ≤ exp(2(∑_β ra_β v_β + ∑_j |rb_j| |v_j|)) W(y)` (any coordinate map `c`).
  `exists_siegelWeight_le_mul` packages this as a finite factor `κ` with `W(g) ≤ κ W(b g)` for a
  point `b` moving the coordinates by a fixed `v`; `exists_siegelWeight_le_orthantShift` applies
  it to every orthant shift (`a_β`, `z_j` or `z_j⁻¹`), using that `a_β` and `z_j` move the
  coordinates by unit vectors.
- `chamberDensity_eq_siegelWeight`: the Library's chamber density
  `WeightedSiegel.chamberDensity` of the log weight `ℓ ∘ e` on the region `e⁻¹(siegelRegion τ)`
  is `W`. Hence `frameMeasure_eq_domainWeightedHaar`: the frame measure of the weighted Siegel
  space of that region (module `AdelicLocalFinitenessSiegelFrame`) is `W · Haar|_{D₀}`.
- `measurable_siegelWeight_chamberCoords`; `siegelWeight_cosetSubgroup_mul`: `W` is left
  invariant under `Λ₀ ⊔ U_J(𝔸)` for every `J ⊆ Δ` (the chamber coordinates are, by
  `chamberCoords_cosetSubgroup_mul`).
- `invariant_sup`: a function left invariant under two subgroups is left invariant under their
  join.

## Operators

- `residualOperator L p = L m + ∑_{q < m} p_q • L q` for a family `L : ℕ → (E →L[ℂ] E)` and lower
  coefficients `p : Fin m → ℂ`. `residualOperator_ae`: if `L q F` is almost everywhere
  `g ↦ φ(b^q g)` for every `q`, then `residualOperator L p F` is almost everywhere the residual
  `residualFun b p φ = φ(b^m ·) + ∑_q p_q φ(b^q ·)`.
- `IsLeviNormalizingPoint.inv`: the inverse of a point commuting with `L_J(𝔸)` and normalizing
  `U_J(𝔸)` has the same properties. `isLeviNormalizingPoint_orthantShift`: if every `a_β`
  (`β ∉ J`) and every `z_j` has them for every `J ⊆ Δ`, so does every orthant shift for the index
  `J_P = P ∩ Δ` of a finset `P`.
- `siegelHaar hK e ra τ rb = 𝓕.weightedHaar W`.

## `exists_residualOperators`

Hypotheses: `a_β`, `z_j` move the chamber coordinates by the unit vectors; every `a_β` with
`β ∉ J` and every `z_j` commutes with `L_J(𝔸)` and normalizes `U_J(𝔸)` for every `J ⊆ Δ`;
thresholds `τ` and a coefficient bound `M`.

Conclusion: there is `R₀ ≥ 0` such that for all rates `ra_β ≥ R₀`, `rb_j ≥ R₀` there are
continuous linear operators on `L²(siegelHaar)`

- `E P` for every finset `P` of characters, with `E P F = ∑_{S ⊆ P} (−1)^{|P ∖ S|}
  componentFoldCT S f` almost everywhere for every measurable representative `f` of `F`, and
  `∑_{P ⊆ Δ} E P = 1`;
- `L P ε k q` for every orthant `ε`, direction `k` (a root `β ∉ J_P` or a central index) and
  `q ∈ ℕ`, with `L P ε k q F = (g ↦ (∑_{S ⊆ P} (−1)^{|P ∖ S|} componentFoldCT S f)(b^q g))` almost
  everywhere, `b = orthantShift a z J_P ε k`;

and for all degrees `m P ε k` and lower coefficients `p P ε k` with `∑_q ‖p_q‖ ≤ M` there is
`C ≥ 0` with, for every `F`,

```
‖F‖ ≤ C ∑_{P ⊆ Δ} ∑_ε ( ‖E P F‖_{orthantBox(J_P, ε, m P ε)}
                         + ∑_k ‖residualOperator (L P ε k) (p P ε k) F‖_{orthantPos(J_P, ε)} ),
```

the norms being those of the restrictions (`LpToLpRestrictCLM`) to the boxes and positive
regions.

Proof. `R₀` is the threshold of `exists_chamberEmbedding` for the components indexed by the
subsets `P ⊆ Δ` with `J_P = P ∩ Δ`. For rates at least `R₀`, `W` is measurable and invariant under
`Λ₀` and every `U_J(𝔸)`, so `exists_componentOperators` gives the constant-term contractions
`T S` with `T Δ = 1`; `E P` is their alternating sum (`alternatingSum_apply_ae` computes it on
representatives, `sum_alternatingSum` gives `∑_P E P = T Δ = 1`). Each orthant shift `b` is a
normalizing point with a finite forward factor `κ` for `W`, so `exists_translatedComponent_pow`
gives `L P ε k`. For the bound, take a measurable representative `f` of `F` and the components
`φ_P = ∑_{S ⊆ P} (−1)^{|P ∖ S|} componentFoldCT S f`: they are measurable, invariant under
`Λ₀ ⊔ U_{J_P}(𝔸)` (`componentFoldCT_invariant` and `invariant_sup`), sum to `f` almost
everywhere, agree almost everywhere with `E P F`, and their residuals agree almost everywhere
with the residual operators (`residualOperator_ae`). So the boxes and residuals are square
integrable, and the estimate of `exists_chamberEmbedding` becomes the displayed one after
identifying each `lpNorm` of a representative with the norm of the corresponding class.

## Provenance

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc.
37 (2024), 187–234 (literature id `bernstein-lapid-2024-meromorphic-continuation-eisenstein`):
§7.4, p. 215 (the weighted Hilbert space on a Siegel domain), §7.5, p. 219 (Proposition: the
operator `f ↦ ((D_α(T_{a_α}) f)_α, f|_{S_P^B})` is a strict embedding), §7.6, pp. 219–220 (the
operator `μ_s` built from the Harish-Chandra components, a strict embedding for `λ` sufficiently
positive) and §7.7, pp. 220–221 (central orthants and the shifts `z_i^{±1}`). The operators here
are raw left translates; the coefficients `p` are those of the difference polynomial acting by
raw left translation. The weight comparison replaces the exact scaling of BL's linear weights by
a forward inequality, which suffices for bounded translation operators.
