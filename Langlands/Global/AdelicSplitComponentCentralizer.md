# Split-component points centralize the Levi factor and normalize the radical

Module `Langlands.Global.AdelicSplitComponentCentralizer`. Its statement form is
`Langlands.Global.SplitComponentCentralizerStatement`, proved by
`Langlands.Global.splitComponentCentralizer`.

## Statement

Let `𝓕 : StandardParabolicFamily F G` be a compatible standard parabolic family over a number
field `F`, in an arbitrary universe `u`, and let `J` be a standard index. For a point `a` of the
split component `A_J` with values in the adele ring, write `b = a ≫ (a_J ≫ l_J ≫ p_J)` for its image
in `G(𝔸)`. Then:

1. `b` commutes with every point of `L_J(𝔸)`, where `L_J = standardLevi 𝓕.i 𝓕.ν J`.
2. For every measurable `φ : G(𝔸) → [0, ∞]` left-invariant under the image `Λ₀` of `P₀(F)` and
   under `U_J(𝔸)`, where `U_J = standardUnipotent 𝓕.i 𝓕.ν J`:
   `∫_{D₀} φ(b g) dg = mulEquivHaarChar (conjPoints b) · ∫_{D₀} φ(g) dg`.
   Here `D₀` is the Library Borel fundamental domain of `Λ₀`, Haar measure is on `G(𝔸)`, and
   `conjPoints b` is conjugation by `b` on `U_J(𝔸)`.

## Proof

These hold on every test scheme `X`:

- `splitComponent_commute_standardLevi`: the image of `A_J` lies in the center of the Levi factor
  `M_J`, by the split-component field `(𝓕.isCompatible J).splitComponent`. Every point of
  `L_J = range(l_J ≫ p_J)` (`levi_eq`) is the image of a point `m` of `M_J`. Mapping the
  commutation in `M_J` along `l_J ≫ p_J` gives the commutation in `G`. This is the same argument
  as in the Library proof of `commutator_mem_radical_of_splitComponent`.
- `splitComponent_mem_standardParabolic`: `b ∈ P_J`, by `parabolic_eq`.
- `splitComponent_conj_mem`, `splitComponent_conj_inv_mem`: `b` and `b⁻¹` normalize `U_J`, since
  `P_J` normalizes `U_J` (`StandardConstantTerm.standardUnipotent_isNormalizedBy_standardParabolic`).

With these hypotheses discharged at the adele ring, part 2 is
`StandardConstantTerm.setLIntegral_mul_left_eq` (module
`Langlands.Global.AdelicSplitComponentTranslation`).

## Provenance

Joseph Bernstein and Erez Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), 187–234, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §§7.3–7.5 (pp. 214–217). The
translations `σ_α` there are left translations by points of split components. This derived module
supplies their change of measure on the fundamental domain of `P₀(F)`. It does not identify the
factor `mulEquivHaarChar (conjPoints b)` with the Library's `halfModulus`, and does not construct
the translation operators on weighted `L²` spaces.
