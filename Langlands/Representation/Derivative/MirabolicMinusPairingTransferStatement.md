# Transfer of invariant pairings through unnormalized `Φ⁻`

Author: Worker 806.

This module states one Prop-valued definition,
`Langlands.Derivative.Mirabolic.PhiMinusPairingTransferStatement F T m`. It
proves nothing.

## Statement

Let `F` be a p-adic field with topological data `T`, let `m : ℕ`, and let `ψ`
be a unitary additive character of `F` (nontrivial by the Library definition).
Write `P = mirabolic (m + 1) F` (the group `P_(m+2)` inside `GL_(m+2)(F)`),
`U = Mirabolic.radical (m + 1) F`, and `abv = normalizedAbsoluteValue T`. Let
`ξ` and `ξ'` be smooth complex representations of `P` on carriers `V`
(universe `uV`) and `W` (universe `uW`). Assume that the vectors `ξ u x - x`
(`u : U`, `x : V`) span `V`; this is the condition `IsRadicalGenerated ξ` of
the rigidity development, written out so that the module depends only on the
Library.

For `s : ℂ`, let `β` be a nonzero element of
`InvariantBilinear.forms ξ ξ' χ_s`, where `χ_s(g) = determinantWeight abv g (-s)`
is `|det g|^(-s)`. So `β (ξ g v) (ξ' g w) = |det g|^(-s) β v w` for all
`g : P`.

The statement asserts a nonzero `β'` in `InvariantBilinear.forms` of the two
unnormalized `Φ⁻` representations
`(phiMinusUnnormalized T ψ m).obj (SmoothRep.of ξ hs)` and
`(phiMinusUnnormalized T ψ m).obj (SmoothRep.of ξ' hs')` of `mirabolic m F`,
at covariance `h ↦ determinantWeight abv h (-(s - 1))`, that is
`|det h|^(-(s - 1))`. The exponent is lowered by one. No condition is imposed
on `ξ'` beyond smoothness.

## Source and provenance

Provenance: derived. Jacquet, Piatetski-Shapiro and Shalika (1983),
*Rankin-Selberg convolutions*, `jpss-1983-rankin-selberg`, §1.4, Proposition,
printed p.380, with its proof beginning on printed p.381. The proof treats the case
in which `ξ` and `ξ'` are induced from `P_(r-1)U_r`. It identifies
`Bil_P(ξ, ξ')` with a space of forms for `P_(r-1)` on the inducing data,
twisted by the modular characters `δ_P^(1/2) δ_H^(-1/2)` (Frobenius
reciprocity, §1.3). This statement isolates one direction, in the form needed
for the induction on `n` in `MirabolicTwistedPairingRigidityStatement` (§1.5,
Corollary 2). It uses the unnormalized `Φ⁻` (Bernstein–Zelevinsky 1976,
Definition 5.11 a), printed p.46), so the modular characters appear as the
shift from `-s` to `-(s - 1)`.

The expected form is
`β'(q v, q w) = ∫_U β(ξ u v, ξ' ε w) θ_ψ(u)⁻¹ du`, where `ε` is the Levi
element `diag(-1, …, -1, 1)`. Conjugation by `h` scales the Haar measure of
`U ≅ F^(m+1)` by `|det h|`, which accounts for the shift by one.
