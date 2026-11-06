# The preimage of a split-torus centralizer is a split-torus centralizer

Author: Worker 1413.

Module `Langlands.GroupScheme.SimplyConnected.CoverPreimageCentralizer`,
namespace `Langlands.GroupScheme.CoverPreimage`, over a field `k`. Internal
helpers for clauses 1–3 of the reduction
[`SplitTorusCentralizerCoverPreimageReduction`](SplitTorusCentralizerCoverPreimageReduction.md).
They introduce no literature assertion.

- `gm_multiplication_fpqc` and `torusCentralizer_multiplication_comp`. For
  `n > 0`, the `n`-th power map of `𝔾ₘ` is quasi-compact, flat and surjective
  (published `IsTorus.flat_and_surjective_multiplication`). Precomposing a
  cocharacter `χ : 𝔾ₘ ⟶ H` with it does not change the torus centralizer
  (`torusCentralizer_comp_of_fpqc`, [toolkit](CoverPreimageToolkit.md)).
- `exists_cover_cocharacter`. Let `d : D ⟶ G` be monomorphic and
  `π : C ⟶ D` a central isogeny. Let `i : Z ⟶ G` be central with
  `centralProduct i d` a central fppf cover
  ([`CoverPreimageCentralProduct`](CoverPreimageCentralProduct.md)). Then
  for every cocharacter `χ : 𝔾ₘ ⟶ G` there is a cocharacter
  `Ψ : 𝔾ₘ ⟶ C` with `torusCentralizer (Ψ ≫ π ≫ d) = torusCentralizer χ`.
  The published power lift `CentralPowerLift.exists_comp_eq_multiplication_comp`
  through `Z × D ⟶ G` gives `Φ : 𝔾ₘ ⟶ Z × D` with
  `Φ ≫ (Z × D ⟶ G) = [2N] ≫ χ`. Let `Φ_D` be its `D`-component. The
  published `IsCentralIsogeny.exists_comp_eq_multiplication_comp` gives
  `Ψ : 𝔾ₘ ⟶ C` with `Ψ ≫ π = [2N'] ≫ Φ_D`. On points,
  `d(Φ_D(x)) = i(Φ_Z(x))⁻¹ χ(x)^{2N}`, with the first factor central. So
  `torusCentralizer_eq_of_hom_eq_mul_central` and two applications of
  `torusCentralizer_multiplication_comp` give the equality.
- `exists_splitSubtorus_torusCentralizer_eq_comap`. Assume in addition that
  `G` and `C` are affine and locally of finite type. Then for every split
  subtorus `a : A ⟶ G` there is a split subtorus `a' : A' ⟶ C` with
  `torusCentralizer a' = (torusCentralizer a).comap (π ≫ d)`.
  - The published `centralizingCocharacter_spec` gives a cocharacter `χ` of
    `A` with the same centralizer in `G` as `a`, using
    `torusCentralizer_gm_eq_dynamicCentralizer`. Let `Ψ` be the cocharacter
    of `C` given by `exists_cover_cocharacter`.
  - `A'` is the schematic image of `Ψ` (published `SchematicImage`). It is a
    torus (published `IsTorus.isTorus_schematicImage`) and split (published
    `IsSplitTorus.isSplitTorus_schematicImage`), and its inclusion `a'` is
    closed. The projection `𝔾ₘ ⟶ A'` is flat and surjective (published
    `HomImage.flat_projection`, `HomImage.surjective_projection`), so
    `torusCentralizer a' = torusCentralizer Ψ`.
  - The published `IsCentralIsogeny.torusCentralizer_comap` gives
    `torusCentralizer Ψ = (torusCentralizer (Ψ ≫ π)).comap π`.
    `torusCentralizer_comp_comap_of_mono` handles `d`, and `comap_comp`
    combines the two.

The literature route through the maximal central torus and the maximal
subtorus of the preimage of a split torus (sketched in the Markdown of
`SplitTorusCentralizerCoverPreimageStatement`) is replaced by this cocharacter
argument. The argument uses only the central product cover and the power
lifts.
