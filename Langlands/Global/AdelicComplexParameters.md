# Complex character parameters and the adelic characters `m ↦ m^λ`

Module `Langlands.Global.AdelicComplexParameters` constructs the parameter
spaces `X^*(G) ⊗ ℂ` and `X^*(G) ⊗ ℝ` of an actual group scheme `G` over a
number field `F`, their pairings with the real character dual
`𝔞_G = Hom(X^*(G), ℝ)`, the real part map, and the characters
`m ↦ m^λ = exp ⟨λ, H_G(m)⟩` of the actual adelic points `G(𝔸_F)`. It is a
definition module: besides the bundled homomorphism laws it proves only the
definitional evaluation formulas marked `@[simp]`.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), 187–234, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`; §2.1, journal
p.190 (page 4 of the journal PDF). For a standard parabolic `P = M ⋉ U` it
sets `𝔞_P = Hom(X^*(P), ℝ) = Hom(X^*(M), ℝ)` and `𝔞_P^* = X^*(M) ⊗ ℝ`,
defines `H_M : M(𝔸) → 𝔞_P` by `e^{⟨χ, H_M(m)⟩} = |χ(m)|` for `χ ∈ X^*(M)`,
and writes `m^λ` for the value at `m` of `λ ∈ 𝔛_P`, the group of continuous
quasi-characters of `M(𝔸)/M(𝔸)^1`, in additive notation. In the number field
case `𝔛_P = X^*(M) ⊗_ℤ ℂ = 𝔞_P^* ⊗_ℝ ℂ`, and the map `Re : 𝔛_P → 𝔞_P^*` is
used throughout. The source refers to Mœglin–Waldspurger I.1.4 for these
facts.

## Existing objects used

- `RealCharacterDual F G` (module `Langlands.Global.AdelicCharacterLog`) is
  `Hom_ℤ(X^*(G), ℝ)`, the source's `𝔞`, with `X^*(G)` the actual group
  `GroupScheme.rationalCharacters G` of characters defined over `F`.
- `characterLog F G : G(𝔸) → RealCharacterDual F G` satisfies
  `characterLog F G m χ = log |χ(m)|`, with the normalized idelic absolute
  value of the actual character value. It is the source's `H_M` (with
  `G = M`), and `characterLog_mul` makes it a homomorphism.

## Definitions

- `ComplexCharacterParameter F G` is `ℂ ⊗[ℤ] X^*(G)`: the source's
  `X^*(M) ⊗_ℤ ℂ` with the complex scalars written as the first tensor factor,
  as in the Library's local parameter
  `Langlands.Plancherel.rationalCharacterTensorParameter`. Its complex
  structure is scalar multiplication on the first factor.
- `RealCharacterParameter F G` is `ℝ ⊗[ℤ] X^*(G)`, the source's `𝔞^*`.
- `complexCharacterEvaluation` and `realCharacterEvaluation` send a
  character `χ` to the evaluation `H ↦ H(χ)` on `RealCharacterDual F G`, a
  real-linear form with complex, respectively real, values; they are additive
  in `χ`.
- `complexParameterPairing F G` is the complex-linear map sending `λ` to the
  real-linear form `H ↦ ⟨λ, H⟩` on `𝔞`, determined by
  `⟨s ⊗ χ, H⟩ = s · H(χ)` (`complexParameterPairing_tmul`). It is the
  complex-bilinear extension of the canonical pairing of `X^*(G)` with
  `Hom(X^*(G), ℝ)`, built with `TensorProduct.AlgebraTensorModule.lift`.
- `realParameterPairing F G` is the analogous real pairing
  `⟨t ⊗ χ, H⟩ = t · H(χ)` of `𝔞^*` with `𝔞`.
- `parameterRealPart F G : X^*(G) ⊗ ℂ → X^*(G) ⊗ ℝ` is the real-linear map
  `s ⊗ χ ↦ Re(s) ⊗ χ`, the source's `Re`.
- `parameterPower F G λ m` is the complex number
  `exp ⟨λ, H_G(m)⟩`. For `λ = s ⊗ χ` it equals `exp(s · log |χ(m)|) = |χ(m)|^s`,
  so it agrees with the source's `m^λ` under the identification
  `𝔛 = X^*(G) ⊗ ℂ`.
- `parameterCharacter F G λ : G(𝔸) →* ℂˣ` is `m ↦ m^λ` as a homomorphism.
  It is multiplicative because `H_G` is a homomorphism, the pairing is
  additive in `H`, and `exp` turns sums into products.

The source works with `G = M` a Levi subgroup (and with `P` through
`𝔞_P = Hom(X^*(P), ℝ)`). The definitions here are stated for an arbitrary
actual group scheme `G` over `F`, so they apply to `P`, to `M` and to `G`
itself. The identification `X^*(P) = X^*(M)` is not part of this module.

## Scope

Not proved or asserted here: continuity of `m ↦ m^λ`; holomorphy in `λ`;
`|m^λ| = m^{Re λ}`; finite generation or freeness of `X^*(G)` (for connected
reductive groups it is the published `GroupScheme.rationalCharacterLattice`),
hence finite dimensionality of the parameter spaces; surjectivity of `H_G`
and the resulting identification of `X^*(G) ⊗ ℂ` with the continuous
quasi-characters of `G(𝔸)/G(𝔸)^1`. The function field case of the source is
not treated. Holomorphy and meromorphy on `X^*(G) ⊗ ℂ` are expressed with
`Langlands.Analysis.Meromorphic.IsHolomorphicInCoordinatesOn` and
`IsMeromorphicInCoordinatesOn`.
