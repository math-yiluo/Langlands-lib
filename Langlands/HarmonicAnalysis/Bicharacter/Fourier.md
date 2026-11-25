# The Fourier transform of a self-dual bicharacter

The module `Langlands.HarmonicAnalysis.Bicharacter.Fourier` defines the Fourier transform attached
to a bicharacter and a Haar measure, and proves for a self-dual bicharacter that it preserves the
Schwartz–Bruhat functions, that its square is a positive multiple of the reflection, and
Plancherel's formula with that constant.

## Content

Let `X` be a commutative topological group, locally compact and second countable, with
arbitrarily large and small compact open subgroups (`CompactOpenExhaustion`), `μ` a Haar measure and
`e` a self-dual bicharacter (`IsSelfDualBicharacter`, `Bicharacter/SelfDual.lean`).

- `bicharacterFourier μ e φ x = ∫ y, e x y * φ y ∂μ`, for any function `φ : X → ℂ`
  (`bicharacterFourier_apply`).
- `bicharacterFourier_mem`: the transform of a Schwartz–Bruhat function (a locally constant
  function of compact support, `schwartzBruhatSubmodule X`) is one. Local constancy: `φ` has compact
  support and `e` is locally constant, so `e z · = e y ·` on the support for `z` near `y`. Compact
  support: `φ` is invariant under a neighbourhood `U` of `0`; if `y` is outside the compact set
  containing the annihilator of `U`, some `t ∈ U` has `e t y ≠ 1`, and translating by `t`
  multiplies the integral by `e t y`, so it vanishes. `bicharacterFourierSB μ he` is the transform
  as a linear endomorphism of `SchwartzBruhat X`.
- `exists_pos_bicharacterFourier_bicharacterFourier`: there is `C > 0` with
  `ℱ (ℱ φ) (x) = C φ (-x)` for every Schwartz–Bruhat `φ`. For a compact open subgroup `L`, the
  transform of `1_L` is `μ(L) 1_{L^⊥}` (`L^⊥` the annihilator), and `L^⊥⊥ = L`; for `φ` invariant
  under `L^⊥`, Fubini on `L^⊥⊥ × supp φ` gives `ℱℱφ(x) = μ(L^⊥) μ(L^⊥⊥) φ(-x)`. Every
  Schwartz–Bruhat function is invariant under some compact open subgroup, the constant obtained
  does not depend on the subgroup (compare on the indicator of a fixed one), and the self-duality
  conditions give the required subgroups. `C = 1` exactly when `μ` is the self-dual measure for
  `e`; the Library's `IsSelfDual ψ μ` is this condition for the scalar transform
  (`isSelfDual_iff`, `Bicharacter/Instances.lean`).
- Three facts on Schwartz–Bruhat functions used throughout (for `X` a commutative topological
  group): `eventually_add_eq_of_mem_schwartzBruhatSubmodule (hf : f ∈ schwartzBruhatSubmodule X) :
  ∀ᶠ t in 𝓝 (0 : X), ∀ x, f (x + t) = f x`; `exists_nhds_add_eq_of_mem_schwartzBruhatSubmodule hf :
  ∃ U ∈ 𝓝 (0 : X), ∀ M : AddSubgroup X, (M : Set X) ⊆ U → ∀ t ∈ M, ∀ x, f (x + t) = f x` (the
  generalized tube lemma on `tsupport f × {0}`); and, for a compact open subgroup `L`,
  `indicator_one_mem_schwartzBruhatSubmodule L hc ho :
  (L : Set X).indicator (fun _ => (1 : ℂ)) ∈ schwartzBruhatSubmodule X`.
- `lintegral_enorm_bicharacterFourier_sq` (Plancherel): with that constant,
  `∫⁻ ‖ℱ φ‖² dμ = C ∫⁻ ‖φ‖² dμ`, from `∫ ℱφ · conj ℱφ = C ∫ φ · conj φ` (Fubini, and
  `conj (e x y) = e (-x) y`).

Hausdorffness is not used. Reference: A. Weil, *Sur certains groupes d'opérateurs unitaires*, Acta
Math. 111 (1964), chapter I, n° 2, p. 147 (the Fourier transform `Φ*(x*) = ∫ Φ(x) ⟨x, x*⟩ dx`, the
dual Haar measure, the inversion formula and Plancherel's formula) and n° 11, pp. 157–158 (the space
`S(G)` of Bruhat, on which the Fourier transform induces an automorphism). Weil's transform takes
functions on `G` to functions on the dual `G*`; here `X` is identified with its dual through `e`, and
`C = 1` is Weil's choice of the dual measure. The Library's row and rectangular Fourier transforms
are instances (`Bicharacter/Instances.lean`).

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`, under
`src/Development/AbelianVarietyTheory/`: `Definitions/Divisors/UnipVal.lean` line 37 (`four`);
`Proofs/DivisorProofs/BicharacterFourierTransformMemSchwartzBruhat.lean` (whole);
`Proofs/DivisorProofs/BicharacterFourierTransformTwiceEqPosSmulReflect.lean` lines 60–291;
`Proofs/DivisorProofs/LintegralFourSq.lean` lines 37–109. The repository has no licence file; the
text is used with attribution, see
`licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespaces `GlobalTheory.KSp`, `KSp.FourMem`, `KSp.FourInv`, `KSp.Planch` →
  `Langlands.HarmonicAnalysis` (public) and `Langlands.HarmonicAnalysis.BicharacterFourier.Internal`.
- Renamed: `four` → `bicharacterFourier`, `four_mem_SB` → `bicharacterFourier_mem`, `four_four` →
  `exists_pos_bicharacterFourier_bicharacterFourier`, `lintegral_four_sq` →
  `lintegral_enorm_bicharacterFourier_sq`; internal: `four_eq_zero`, `four_indicator`,
  `four_four_of_invariant`, `integral_four_mul` and the private
  `exists_four_four_eq_smul_neg_of_ann_invariant` with names in `bicharacterFourier`.
- `KSp.Good X` replaced by Mathlib's classes and `CompactOpenExhaustion X`; `T2Space` dropped (not
  used); `IsPair` → `IsSelfDualBicharacter`; `SB X` → `schwartzBruhatSubmodule X`. In
  `lintegral_enorm_bicharacterFourier_sq` the unused group `X` and the structure `Good` are no
  longer arguments.
- New: `bicharacterFourier_apply`, `bicharacterFourierSB`, `coe_bicharacterFourierSB`. Types in
  any universe.
- `eventually_add_eq_of_mem_schwartzBruhatSubmodule`, `exists_nhds_add_eq_of_mem_schwartzBruhatSubmodule`
  and `indicator_one_mem_schwartzBruhatSubmodule` are public in `Langlands.HarmonicAnalysis` (they
  are used by the Heisenberg, metaplectic and Weil index files).

## Declarations

- `bicharacterFourier`, `bicharacterFourier_apply`
- `eventually_add_eq_of_mem_schwartzBruhatSubmodule`
- `bicharacterFourier_mem`, `bicharacterFourierSB`, `coe_bicharacterFourierSB`
- `exists_nhds_add_eq_of_mem_schwartzBruhatSubmodule`, `indicator_one_mem_schwartzBruhatSubmodule`
- `exists_pos_bicharacterFourier_bicharacterFourier`
- `lintegral_enorm_bicharacterFourier_sq`

All in the namespace `Langlands.HarmonicAnalysis`.

## Dependencies

`Langlands.HarmonicAnalysis.Bicharacter.SelfDual`; Mathlib: `MeasureTheory.Integral.Prod`,
`MeasureTheory.Measure.Haar.Basic`.
