# The Library's Fourier transforms as transforms of self-dual bicharacters

The module `Langlands.HarmonicAnalysis.Bicharacter.Instances` identifies the Library's scalar, row
and rectangular Fourier integrals as instances of the transform of a self-dual bicharacter
(`Langlands/HarmonicAnalysis/Bicharacter/Fourier.lean`), so that the Library has one theory of the
Fourier transform on totally disconnected groups and not two.

## Content

For a topological field `K` and the Library's measures (`AdditiveHaarMeasure`, its product
`rowMeasure μ d` on `Kᵈ` and `RankinSelberg.rectangularMeasure μ r s` on `M_{r×s}(K)`):

- `fourierIntegral_eq_bicharacterFourier`: `fourierIntegral ψ μ f y` (`∫ ψ(x y) f(x) dμ(x)`,
  `Langlands/HarmonicAnalysis/Basic.lean`) is `bicharacterFourier μ (fun a b => ψ(a b)) f y`.
- `rowFourierIntegral_eq_bicharacterFourier`: the row transform (`RowFourier.lean`) is the
  transform of `(a, b) ↦ ψ(∑ aᵢ bᵢ)`.
- `rectangularFourierIntegral_eq_bicharacterFourier`: the rectangular transform
  (`RectangularFourier.lean`) is the transform of `(a, b) ↦ ψ(∑ aᵢⱼ bᵢⱼ)`.
- `rowPairing_comm`: the row pairing is symmetric.

Over a nonarchimedean local field `K` (Mathlib's `IsNonarchimedeanLocalField`), the three
bicharacters are self-dual (`isSelfDualBicharacter_mul`, `isSelfDualBicharacter_rowPairing`,
`isSelfDualBicharacter_rectangularPairing`, from `isSelfDualBicharacter_of_symm` for the
multiplication, the dot product and the entrywise pairing, which are non-degenerate symmetric
bilinear forms). So the general theorems apply:

- `rowFourierClosed`: the Library's `RowFourierClosed ψ μ d` holds for every Haar measure `μ`: the
  row transform of a Schwartz–Bruhat function is one (`bicharacterFourier_mem`).
- `isSelfDual_iff`: the Library's scalar self-duality `IsSelfDual ψ μ` (Fourier squared is the
  reflection, with convergent second integrals) holds exactly when the constant of
  `exists_pos_bicharacterFourier_bicharacterFourier` for `(a, b) ↦ ψ(a b)` and `μ` is `1`; the
  convergence part is automatic, because the transform is again a Schwartz–Bruhat function.

The Library's proofs of row and rectangular compatibility from scalar self-duality
(`RowFourierCompatibilityProof.lean`, `RectangularFourierCompatibilityProof.lean`) work over any
topological field and are not replaced.

## Relation to the source

No text of this file is taken from the source repository
(<https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`). The source's
Fourier analysis of a self-dual bicharacter is here the Library's general theory, and the
Library's transforms are its instances.

## Declarations

- `fourierIntegral_eq_bicharacterFourier`, `rowPairing_comm`,
  `rowFourierIntegral_eq_bicharacterFourier`, `rectangularFourierIntegral_eq_bicharacterFourier`
- `isSelfDualBicharacter_mul`, `isSelfDualBicharacter_rowPairing`,
  `isSelfDualBicharacter_rectangularPairing`
- `rowFourierClosed`, `isSelfDual_iff`

All in the namespace `Langlands.HarmonicAnalysis`.

## Dependencies

`Langlands.HarmonicAnalysis.Bicharacter.Fourier`, `Langlands.HarmonicAnalysis.RectangularFourier`
(and through it `RowFourier`, `Representation.RankinSelberg.Measures`); Mathlib:
`Topology.Algebra.Nonarchimedean.TotallyDisconnected`.
