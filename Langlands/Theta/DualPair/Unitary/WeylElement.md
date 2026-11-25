# The operator of the Weyl element

**GKT Proposition 2.24** (p. 63: the Weyl element acts by a Fourier transform) and **Theorem 1.25**
(p. 34: the Fourier transform between two Schrödinger models intertwines them) for the polarization
of `𝕎`, and **Lemma 5.1** (p. 136) tensored with `V` (the braid relation), in Case `3₊`: the third
formula of Proposition 12.27 (1) (p. 372).

The module `Langlands.Theta.DualPair.Unitary.WeylElement` defines the Fourier transform of the
Hermitian pairing, by a multiple of which the Weyl element of `U(ν, ν)` acts in the Leray
splitting, and proves its relations with the operators of the Siegel parabolic (internal lemmas).

## Content

- `hermitianFourier c ψ Q μ φ x = ∫ ψ(β(x, y)) φ(y) dμ(y)` with `β = hermitianPairing c Q`: the
  transform `bicharacterFourier` of the self-dual bicharacter `ψ ∘ β`
  (`Langlands/HarmonicAnalysis/Bicharacter/Fourier.lean`).

Internal lemmas (namespace `Langlands.Theta.Unitary.Internal`), for an invertible Hermitian `Q`:

- `fou_parFun_levi`: if `w p = q w` for `p, q` in the Siegel parabolic, then
  `ℱ ∘ T(p) = T(q) ∘ ℱ` (`T = siegelParabolicOp`); then `p` and `q` are Levi elements
  (`blocks_of_weyl_mul_eq`) and this is the change of variables `y ↦ y a` in the integral.
- `heisFun_fou`: `ρ(w) ℱ = ℱ ρ(w J)`: the Fourier transform normalizes the Schrödinger operators
  along the Weyl element `J`.
- `braid_relation`: for an invertible Hermitian `b` whose character of second degree
  `x ↦ ψ(½ β(x, x b))` has Gauss integral `γ`,
  `s(det(-b⁻¹)) ℱ T(n(b)) ℱ φ = γ T(p) ℱ T(n(-b⁻¹)) φ` with `n(b) = [[1, b], [0, 1]]`,
  `p = [[-b⁻¹, 1], [0, -b]]` and `s` the splitting scalar; from Weil's formula
  (`bicharacterFourier_mul_bicharacterFourier`). This is the relation `w n(b) w = p w n(-b⁻¹)` of
  the group, realized by the operators up to the Weil index `γ`.

Kudla, *Splitting metaplectic covers of dual reductive pairs*, Israel J. Math. 87 (1994); Ranga
Rao, *On some explicit formulas in the theory of Weil representation*, Pacific J. Math. 157 (1993)
(page references to be added).

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`, under
`src/Development/AbelianVarietyTheory/`: `Definitions/Divisors/UnipVal.lean`, lines 130–132
(`fou`); under `Proofs/DivisorProofs/`: `FourierIntertwinesSiegelLeviOperator.lean`,
`FourierIntertwinesWeylHeisenbergSchrodinger.lean`, `FourierHermitianMultiplierBraidRelation.lean`
(each whole). The repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- `KSp.fou` → `Langlands.Theta.hermitianFourier`, defined with the Library's `bicharacterFourier`
  (the source's `four`); the lemmas in `Langlands.Theta.Unitary.Internal`.
- Calls of the wrappers replaced by the wrapped lemmas (`weil_formula_fourier_quadratic_character`
  → `bicharacterFourier_mul_bicharacterFourier`, `isSelfDualBicharacterPairing_of_symmBilinForm` →
  `isSelfDualBicharacter_of_symm`, `map_twoSided_mul_haar_matrix_quadraticExt` →
  `map_mul_mul_addHaar`, …); `IsPair`, `Good` → `IsSelfDualBicharacter` and Mathlib's classes.

## Declarations

- `Langlands.Theta.hermitianFourier`

## Dependencies

`Langlands.Theta.DualPair.Unitary.SiegelParabolic`, `Langlands.HarmonicAnalysis.Bicharacter.GaussIntegral`.
