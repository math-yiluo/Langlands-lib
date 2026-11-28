# Schur orthogonality for cut-off supercuspidal coefficients

The module `Langlands.BaseChange.SupercuspidalWindowSchurOrthogonalityStatement` states, as the
proposition `SupercuspidalWindowSchurOrthogonalityStatement.{u, v, uW}`, that a coefficient of
the contragredient of an irreducible supercuspidal representation `τ` of `GL_n(E)`, cut off by
the determinant window normalized over the scalars `F^×`, acts on `τ` as a fixed nonzero
multiple of a rank-one operator. The module states the proposition and does not prove it.

## Notation (Library and Mathlib)

- `determinantWindow F m` (module `Langlands.BaseChange.DeterminantWindow`): the indicator of
  `0 ≤ ord_F N_{E/F}(det x) < m`; here `m = n · [E : F]` (`n * Module.finrank F E`).
- `GeneralLinear.IsSupercuspidal τ`: admissible with vanishing Jacquet coinvariants for all
  proper block parabolics and their conjugates; `hτ.1.1` is the smoothness of `τ`.
  `τ.IsIrreducible` is Mathlib's irreducibility of a representation.
- `SmoothDual τ`: smooth linear forms on `W`.
- `Hecke.integratedAction μ τ hτ.1.1 φ` (module `Langlands.Representation.Hecke.IntegratedAction`)
  is `τ(φ) = ∫ φ(x) τ(x) dμ(x)` for a Schwartz–Bruhat function `φ`.

## Statement

`SupercuspidalWindowSchurOrthogonalityStatement.{u, v, uW}` quantifies over a field `F : Type u`
with `[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`, a field
`E : Type v` with `[Algebra F E] [Module.Finite F E] [TopologicalSpace E] [IsTopologicalRing E]
[IsModuleTopology F E]`, and `n : ℕ` with `0 < n`; `GL_n(E)` carries its locally compact
topology and the Borel σ-algebra. For every irreducible representation
`τ : Representation ℂ (GeneralLinear n E) W` (`W : Type uW`) with
`hτ : GeneralLinear.IsSupercuspidal τ` and every Haar measure `μ` on `GL_n(E)`, there is
`d : ℂ` with `d ≠ 0` such that for every `w : W`, every `ℓ : SmoothDual τ` and every
`φ : SchwartzBruhat (GeneralLinear n E)` with
`φ x = determinantWindow F (n * Module.finrank F E) x * ℓ (τ x⁻¹ w)` for all `x`,

`Hecke.integratedAction μ τ hτ.1.1 φ u = (d * ℓ u) • w` for every `u : W`.

The constant `d` depends only on `τ`, `μ` and the window, not on `w`, `ℓ` and `φ`. The case
`E = F` (`[E : F] = 1`) is included.

## Why it is true

Let `A = F^×`, embedded as scalar matrices; it is a closed subgroup of the centre `E^×` of
`GL_n(E)` with `E^× / A` compact. Fix a Haar measure `μ_A` on `A`, and let `d(τ)` be the
formal degree of `τ` for the quotient measure `μ / μ_A` on `GL_n(E) / A`. Supercuspidal
coefficients are compactly supported modulo the centre (Renard 2026, VI.2.1), so `τ` is
square-integrable modulo `A` after a twist by a character, and Schur orthogonality holds
modulo `A` (Renard 2026, IV.3.3, Lemma (i) and Remark, printed pp. 101–102):

`∫_{G/A} λ'(τ(x) u) λ(τ(x)⁻¹ w) dẋ = λ'(w) λ(u) / d(τ)` for `u, w ∈ W` and smooth `λ, λ'`.

The integrand `x ↦ λ'(τ(x) u) λ(τ(x)⁻¹ w)` is invariant under `A` (the central character
cancels), and `∫_A b(z x) dμ_A(z) = μ_A(O_F^×)` for every `x`, where
`b = determinantWindow F (n [E : F])` (exactly one `O_F^×`-coset of `A` puts `z x` in the
window; see `Langlands/BaseChange/DeterminantWindow.md`). Hence, by the quotient integral
formula,

`λ'(τ(φ) u) = ∫_G b(x) λ(τ(x)⁻¹ w) λ'(τ(x) u) dμ(x) = μ_A(O_F^×) λ'(w) λ(u) / d(τ)`

for every smooth `λ'`. Smooth linear forms separate the points of the admissible
representation `W`, so `τ(φ) u = d λ(u) w` with `d = μ_A(O_F^×) / d(τ) ≠ 0`; this number does
not depend on the choice of `μ_A`.

## Sources and provenance

The proposition is formulated for this Library (derived): it is Schur orthogonality modulo a
cocompact central subgroup, D. Renard, *Représentations des groupes réductifs p-adiques* (2026
version), IV.3.3, Lemma (i) and Remark, printed pp. 101–102, combined with the compact support
modulo the centre of supercuspidal coefficients, Renard 2026, VI.2.1, Théorème, printed
pp. 137–138, and rewritten for the determinant-window cut-off of
`Langlands.BaseChange.DeterminantWindow`. It is step 2 of the proof sketch of
`Langlands.BaseChange.SupercuspidalCoefficientEllipticMatchingStatement` (the twisted trace of
the cut-off coefficient). The Library's Schur orthogonality for compactly supported
coefficients (`Langlands/Representation/CompactCoefficient/`) and for coefficients modulo a
cocompact central subgroup (`Langlands/Representation/Compact/CocompactCentralSquareIntegrableStatements.lean`)
are the closest results present in the Library.
