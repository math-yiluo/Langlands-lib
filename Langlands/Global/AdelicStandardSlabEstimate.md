# Slab estimates for functions on `P₀(F) U_J(𝔸) \ G(𝔸)`

Module `Langlands.Global.AdelicStandardSlabEstimate`. Notation as in
`Langlands.Global.AdelicStandardCosetShift`: `Λ₀` is the image of `P₀(F)` in `G(𝔸)`, `U_J` and
`L_J` are the unipotent radical and the Levi factor of the standard parabolic `P_J`, and
`domainWeightedHaar F G i ν W` is `W · Haar` on the fundamental domain of `Λ₀`.

## Definitions

- `CosetSpaceShift.shift_iterate_mk` (namespace `Langlands.Analysis.CosetSpaceShift`): the
  `k`-th iterate of the descended translation by `a` sends the coset of `g` to the coset of
  `a^k g`.
- `residualFun F G b p φ` is the function `g ↦ φ(b^m g) + ∑_{k<m} p_k φ(b^k g)`: the residual of
  the monic difference equation `X^m + ∑_{k<m} p_k X^k` for left translation by `b`.

## The estimate `exists_slabEstimate`

Data and hypotheses, for a finite index type `I`:

- points `b_k ∈ G(𝔸)` that commute with every point of `L_J(𝔸)` and satisfy
  `b_k U_J(𝔸) b_k⁻¹ ⊆ U_J(𝔸)` and `b_k⁻¹ U_J(𝔸) b_k ⊆ U_J(𝔸)`;
- a measurable weight `W`, left invariant under `Λ₀ ⊔ U_J(𝔸)`, with `W(g) = κ_k W(b_k g)` for
  positive reals `κ_k`;
- measurable real heights `ht_k`, left invariant under `Λ₀ ⊔ U_J(𝔸)`, with
  `ht_l(b_k g) = ht_l(g) + δ_{kl}`;
- degrees `m_k` and lower coefficients `p_k : Fin m_k → ℂ` with
  `∑_q ‖p_{kq}‖ f_k^q < f_k^{m_k}`, where `f_k = √(κ_k c(b_k))` and `c(b_k)` is the Haar
  factor of conjugation by `b_k` on `U_J(𝔸)`.

Write `pos = {g | ht_k(g) > 0 for all k}` and `box = {g | 0 < ht_k(g) ≤ m_k for all k}`.
Conclusion: there is `C ≥ 1` such that for every measurable `φ : G(𝔸) → ℂ` left invariant
under `Λ₀ ⊔ U_J(𝔸)`, if `φ` is square integrable on `box` and every residual
`residualFun F G b_k p_k φ` is square integrable on `pos` (for `W · Haar|_{D₀}`), then `φ` is
square integrable on `pos` and

```
‖φ‖_pos ≤ C (‖φ‖_box + ∑_k ‖residualFun F G b_k p_k φ‖_pos).
```

## Proof

Each `b_k` gives an `L2RenormalizingShift` on the coset space
`(Λ₀ ⊔ U_J(𝔸)) \ G(𝔸)` for the pushforward measure (`standardRenormalizingShift`); the
heights descend, and the shifts are independent in the sense of `L2IndependentSlabs` because
`ht_l(b_k g) = ht_l(g)` for `k ≠ l`. The coefficient hypothesis is the one of
`l2IndependentSlabs`, which gives `C`. The function `φ` descends; the positive region and
the boundary box of the coset space are the images of `pos` and `box`
(`restrict_map_mk`), the residual of the descended function composed with the quotient map
is `residualFun F G b_k p_k φ` (`shift_iterate_mk`), and `Lᵖ` norms and membership transfer
through the pushforward (`eLpNorm_lift`, `memLp_lift_iff`, `eLpNorm_map_measure`).

## Provenance

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc.
37 (2024), 187–234, §7.5, Corollary (p. 218) and Proposition (p. 219), and the membership
step in §7.6, pp. 219–220 (literature id
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`). BL apply their Corollary on the
relative Siegel domain in `P₀(F) U(𝔸) \ G(𝔸)` with `σ_α` the left translation by `a_α`; this
module carries out that application for functions on `G(𝔸)` invariant under
`P₀(F) U_J(𝔸)` and a weight with exact scaling, using the sufficient coefficient condition of
`L2IndependentSlabs` in place of BL's condition on the roots of the polynomials. It does not
construct the weights, heights or translations of the system `Ξ_main`.
