# The archimedean image of the open-cell Haar measure on a finite region

Module `Langlands.Global.Factors.CuspidalPairEisensteinOpenCellArchimedeanMeasure`, namespace
`Langlands.Global.CuspidalPairEisenstein.ArchimedeanMeasure`.

The module compares the open-cell Haar measure `openCellHaar F r t` on the adelic matrices
`M_((t+1)×(r+1))(𝔸)` (module `Langlands.Global.Factors.CuspidalPairEisensteinOpenCell`) with
the archimedean Haar measure `archimedeanOpenCellHaar F r t` on `M_((t+1)×(r+1))(F_∞)` of
[CuspidalPairEisensteinArchimedeanNumeratorStatement.md](CuspidalPairEisensteinArchimedeanNumeratorStatement.md).

## Content

- `archimedeanPart F r t Y`: the archimedean component `Y_∞`, entrywise `(Y_(ij)).1`;
  `continuous_archimedeanPart`.
- `archimedeanPart_archimedeanMatrix_add`: `(archimedeanMatrix X + Y)_∞ = X + Y_∞`;
  `archimedeanMatrix_neg_add_cancel`:
  `archimedeanMatrix (−X) + (archimedeanMatrix X + Y) = Y`.
- **`exists_setIntegral_comp_archimedeanPart`**: let `R` be an open set of adelic matrices
  with `0 ∈ R`, stable under `Y ↦ archimedeanMatrix X + Y` for every archimedean `X`, and
  such that every `Y ∈ R` has finite components in the integral finite adeles
  (`integralFiniteAdeles F`). Then there is `κ : ℝ≥0`, `κ ≠ 0`, such that for every
  `G : M_((t+1)×(r+1))(F_∞) → ℂ` that is almost everywhere strongly measurable for
  `archimedeanOpenCellHaar F r t`,

  `∫_R G(Y_∞) d(openCellHaar) = κ · ∫ G(X) d(archimedeanOpenCellHaar)`.

## Proof

Let `ν` be the image of the restriction of `openCellHaar` to `R` under `Y ↦ Y_∞`.

1. `ν` is invariant under translations: for archimedean `X₀`, the preimage of `X₀ + A` is
   the translate by `archimedeanMatrix X₀` of the preimage of `A`, intersected with `R`,
   because `R` is stable under these translations in both directions
   (`archimedeanMatrix_neg_add_cancel`); `openCellHaar` is translation invariant
   (`measure_preimage_add`).
2. `ν` is finite on compact sets: for compact `K`, the preimage of `K` in `R` lies in the
   image of `K × M_((t+1)×(r+1))(Ô)` under the pairing map, which is compact
   (`isCompact_integralFiniteAdeles`), and Haar measures are finite on compact sets.
3. The archimedean matrix space is locally compact and second countable
   (`infiniteAdeles_secondCountableTopology`), so uniqueness of Haar measure
   (`Measure.isAddLeftInvariant_eq_smul`) gives `ν = κ • archimedeanOpenCellHaar` with
   `κ = addHaarScalarFactor ν archimedeanOpenCellHaar`.
4. `κ ≠ 0`: otherwise `ν = 0`, but `ν(univ)` is the measure of the nonempty open set `R`,
   which is positive for a Haar measure.
5. `G` is almost everywhere strongly measurable for `ν = κ • archimedeanOpenCellHaar`, so
   the change of variables `integral_map` and `integral_smul_nnreal_measure` give the
   identity.

## Provenance

Internal to the Library: this is the standard uniqueness of Haar measure, applied to the
decomposition `𝔸 = F_∞ × 𝔸_f` of the adelic matrices in the open-cell integral. It lets the
partial open-cell integral of a section cut off at the finite places be computed as a
multiple of the archimedean open-cell integral.
