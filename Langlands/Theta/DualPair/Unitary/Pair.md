# The Weil representation of the unitary dual pair `(U(ν, ν), U(Q))`

**GKT §11.1.1** (the map `G(W) × H(V) → Sp(𝕎)`, `(g, h) ↦ g ⊗ h`, p. 306), **§12.3.1**
(Definition 12.20, the Leray splitting of a dual pair, p. 365), **§12.4.1** (the splitting
`h ↦ (1_W ⊗ h, μ(h))` of `H(V)` when `W` is split, and Proposition 12.26 (3):
`ω(1_W, h) φ(x^* ⊗ v) = μ(h) φ(x^* ⊗ h⁻¹ v)`, p. 371) and **Definition 13.15** (p. 399), in
Case `3₊` with `W` split and `μ = 1`, on the metaplectic group of pairs of **§2.1** (pp. 47–49).

The module `Langlands.Theta.DualPair.Unitary.Pair` adds the second member `H(V) = U(Q)` of the
unitary dual pair to the Leray splitting of `U(ν, ν)`
(`Langlands.Theta.DualPair.Unitary.LeraySplitting`): its action on `𝕎` and on the Schrödinger
model, the commutation of the two members, the representation of `U(ν, ν) × U(Q)` and its splitting
in the metaplectic group of pairs of the book's Schrödinger model.

## Content

`U(Q) = UnitaryGroup.ofForm c Q`, the `h ∈ GL_α(E)` with `hᵀ Q c(h) = Q`, acts on
`𝕎 = M_{α×ν}(E)²` (the book's `W ⊗ V` in the coordinates of the Library) by left multiplication;
`unitaryMat h` is its matrix.

- `hermitianPairing_mul_mul`, `hermitianTracePairing_mul_mul`: `β(h x, h y) = β(x, y)`
  (`hᵀ Q c(h) = Q` and the cyclicity of the trace).
- `UnitaryGroup.leftMulEquiv ν h`, `UnitaryGroup.toTraceIsometryOfForm ν : U(Q) →* isometryGroup ⟪,⟫`:
  `h ↦ 1_W ⊗ h`. `UnitaryGroup.rightMulInvEquiv_leftMulEquiv`: it commutes with `g ⊗ 1_V`
  (`w ↦ w g⁻¹`); `UnitaryGroup.pairToTraceIsometry hc hQ : U(ν, ν) × U(Q) →* isometryGroup ⟪,⟫`,
  `(g, h) ↦ (w ↦ h w g⁻¹)`, is the map `(g, h) ↦ g ⊗ h` of the dual pair
  (`MonoidHom.noncommCoprod`).
- `geometricWeil c ν Q : Representation ℂ U(Q) (SchwartzBruhat M_{α×ν}(E))`, `h · φ = φ(h⁻¹ ·)`
  (Proposition 12.26 (3) with `μ = 1`); `geometricWeil_normalizes`: it normalizes the book's model
  `hermitianTraceSchrodinger c ν Q ψ` along `toTraceIsometryOfForm` (relation (2.2));
  `geometricSplitting ν ψ`, the splitting `h ↦ (1_W ⊗ h, geometricWeil h)` of `U(Q)`, with
  `weil_geometricSplitting`. Every other splitting of `U(Q)` (the book's `μ(h) ≠ 1`) is its twist by
  a character (`MetaplecticGroup.Splitting.exists_eq_twist`, `MetaplecticGroup.Splitting.twist`).
- `UnitaryGroup.norm_det_eq_one`: `N_{E/F}(det h) = 1`; `measurePreserving_unitaryMat_mul`:
  `x ↦ h x` preserves every Haar measure (`map_mul_mul_addHaar`, which scales by
  `|N det h|^{|ν|}`); `geometricWeil_lintegral_enorm_sq`, `geometricSplitting_mem_unitary`: the
  splitting lands in `Mp(𝕎)^{ℂ¹}`.
- `lerayWeil_mul_geometricWeil`: **the two members commute**,
  `lerayWeil g ∘ geometricWeil h = geometricWeil h ∘ lerayWeil g`. The `g` for which it holds form a
  subgroup; it contains the Siegel parabolic, because there `ω(p) φ(x) = s(det A) ψ(½ ⟪x A, x B⟫)
  φ(x A)` and `h` preserves `⟪,⟫` and commutes with right multiplication, and the Weyl element,
  because `ω(w)` is a Fourier transform for `⟪,⟫` and `x ↦ h x` preserves Haar measure; the Siegel
  parabolic and the Weyl element generate `U(ν, ν)`.
- `pairWeil c ν ψ χ Q hE hQ hQu hχ hres : Representation ℂ (U(ν, ν) × U(Q)) (SchwartzBruhat M_{α×ν}(E))`,
  `(g, h) ↦ lerayWeil g ∘ geometricWeil h` (`pairWeil_apply`); `pairWeil_comp_inl`,
  `pairWeil_comp_inr`: its restrictions to the two members.
- `pairWeil_normalizes`, `pairSplitting hE hQ hQu hχ hres : MetaplecticGroup.Splitting
  (hermitianTraceSchrodinger c ν Q ψ) (UnitaryGroup.pairToTraceIsometry hE.involutive hQ)`: **the
  Leray splitting `s^V_{ψ,χ} × s^W` of the dual pair** (Definition 12.20, with the splitting of
  `U(Q)` for `μ = 1`); `weil_pairSplitting`: its Weil representation `ω_ψ ∘ s` (Definition 13.15) is
  `pairWeil`; `pairSplitting_comp_inl`, `pairSplitting_comp_inr`: it restricts to `leraySplitting`
  and `geometricSplitting`; `pairSplitting_mem_unitary`: it lands in `Mp(𝕎)^{ℂ¹}`.

Hypotheses as in `Langlands.Theta.DualPair.Unitary.LeraySplitting`; the action of `U(Q)` alone
needs only the topology of `F` and `⅟2` (for the Heisenberg group), and its unitarity needs `hE`,
`hQ`, `hQu`.

## Declarations

- `Langlands.Theta.unitaryMat`, `unitaryMat_inv_mul_cancel`, `unitaryMat_mul_inv_cancel`,
  `hermitianPairing_mul_mul`, `hermitianTracePairing_mul_mul`.
- `Langlands.UnitaryGroup.leftMulEquiv`, `leftMulEquiv_apply`, `toTraceIsometryOfForm`,
  `toTraceIsometryOfForm_apply`, `rightMulInvEquiv_leftMulEquiv`, `pairToTraceIsometry`,
  `pairToTraceIsometry_apply`, `norm_det_eq_one`.
- `Langlands.Theta.geometricWeil`, `geometricWeil_apply`, `geometricWeil_normalizes`,
  `geometricSplitting`, `weil_geometricSplitting`, `measurePreserving_unitaryMat_mul`,
  `geometricWeil_lintegral_enorm_sq`, `geometricSplitting_mem_unitary`.
- `Langlands.Theta.lerayWeil_mul_geometricWeil`, `pairWeil`, `pairWeil_apply`, `pairWeil_comp_inl`,
  `pairWeil_comp_inr`, `pairWeil_normalizes`, `pairSplitting`, `weil_pairSplitting`,
  `pairSplitting_comp_inl`, `pairSplitting_comp_inr`, `pairSplitting_mem_unitary`.

## Dependencies

`Langlands.Theta.DualPair.Unitary.LeraySplitting`; Mathlib: `GroupTheory.NoncommCoprod`.
