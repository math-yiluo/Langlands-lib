# Proof of eventual lifting of sections from an ample fibre

This module proves the published proposition
`ProperFibrePowerSectionLiftingStatement` from module
`ProperFibrePowerSectionLiftingStatement`:

```
theorem properFibrePowerSectionLifting :
    ProperFibrePowerSectionLiftingStatement.{u}
```

Let `f : X ⟶ S` be proper over a locally noetherian base, let `L` be a line
bundle on `X`, and let `s ∈ S` be a point at which the pullback of `L` to the
residue-field fibre `f.fiber s` is ample. Then there is `n₀` with the following
property. For every `n ≥ n₀`, every global section `σ` of the pullback of
`L^{⊗n}` to that fibre is the restriction (`fibreNeighbourhoodSection`) of a
section `τ` of `L^{⊗n}` over `f⁻¹V`, for some affine open `V ∋ s`.

## Declarations

- `localAdicLayerVanishing : LocalAdicLayerVanishing.{u}`. This is the
  uniform vanishing of the first cohomology of the maximal-ideal layers
  `𝔪^k L^{⊗n} / 𝔪^{k+1} L^{⊗n}` over a noetherian local base. Its hypothesis
  is that `L` is ample on a base change `Z` of the closed point. It is the
  degree-`1` case (`p = 0`) of
  `IdealAdic.exists_uniform_vanishing_adicLayer_maximalIdeal` (module
  `IdealAdicFibreSerre`). That lemma gives one `d₀` such that
  `H^{p+1}(X, 𝔪^k L^{⊗d} / 𝔪^{k+1} L^{⊗d}) = 0` for all `d ≥ d₀` and all
  `k`, `p`. The two pullback squares have the same form, so the proof only
  specializes `p = 0`.
- `properFibrePowerSectionLifting_of_stableImage`. Assuming
  `ProperAdicCohomologyStableImageStatement`, it proves the target. It applies
  `properFibrePowerSectionLifting_of_local` (module
  `ProperFibrePowerSectionLiftingLocalReduction`) to
  `localClosedFibrePowerSectionLifting_of_layerVanishing hs
  localAdicLayerVanishing` (module `ProperFibrePowerSectionLiftingLocalCase`).
- `properFibrePowerSectionLifting` supplies the hypothesis with the theorem
  `properAdicCohomologyStableImage` (module
  `ProperAdicCohomologyStableImageProof`).

## Route of the proof

The proof is assembled from three Library results.

1. **Reduction to a local base**
   (`ProperFibrePowerSectionLiftingLocalReduction`). The fibre over `s` is
   identified with the closed fibre of the base change to `Spec 𝒪_{S,s}`.
   Ampleness is transported along this identification. A global section over
   the local base change descends to `f⁻¹V` for an affine basic open `V ∋ s`,
   by flat base change of sections and localization. So it suffices to prove
   `LocalClosedFibrePowerSectionLifting`. This says: over a noetherian local
   ring `A`, if `L` is ample on a base change `Z` of the closed point, then
   `Γ(X, L^{⊗n}) → Γ(Z, i^*(L^{⊗n}))` is surjective for all large `n`.
2. **The local case** (`ProperFibrePowerSectionLiftingLocalCase`). Vanishing
   of `H¹` of every layer `𝔪^k M / 𝔪^{k+1} M`, for `M = L^{⊗n}`, makes the
   transitions `Γ(M/𝔪^{k+1} M) → Γ(M/𝔪 M)` surjective. The stable-image
   statement (Stacks Lemma 30.20.4(3)) in degree `0` makes the image of
   `Γ(M)` in `Γ(M/𝔪 M)` equal to the image of some `Γ(M/𝔪^{1+c} M)`. So
   `Γ(M) → Γ(M/𝔪 M)` is onto. `closedFibreIso` identifies `M/𝔪 M` with
   `i_* i^* M`.
3. **Uniform layer vanishing** (`IdealAdicFibreSerre`, with
   `IdealAdicGradedFamily`). The devissage of `IdealAdicGradedFamily` reduces
   uniform vanishing for all layers `𝔪^k L^{⊗d} / 𝔪^{k+1} L^{⊗d}` to Serre
   vanishing for single coherent modules annihilated by `𝔪`. Each such module
   is pushed forward from the closed fibre, where Serre vanishing over a field
   for the ample pullback of `L` applies. This gives one bound `d₀` for all
   `k`.

The stable-image input is the theorem `properAdicCohomologyStableImage`. It
derives Stacks Lemma 30.20.4(3) from a uniform Čech form of the Artin–Rees
lemma 30.20.3. The comparison with the source and the corrected citation
(comment 11745) are explained in that module's Markdown.

All universes, possibly non-reduced schemes, an arbitrary point `s` and the
specified line bundle `L` are kept. No flatness of `f`, no projectivity and
no ampleness over a neighbourhood of `s` are assumed.

## Provenance

The target is a neighbourhood form of the case `F = 𝒪_X` of the
surjectivity in Stacks Project Lemma 30.21.3
([tag 02OF](https://stacks.math.columbia.edu/tag/02OF)). The implemented
proof follows the proof given there. It first reduces to the spectrum of a
noetherian local ring. Then it uses Serre vanishing on the layers
`𝔪^n F/𝔪^{n+1} F ⊗ L^{⊗d}`, through Lemma 30.19.3 on the closed fibre. Finally it
uses Lemma 30.20.4(3) on stable images. Only degree `0` sections and degree `1`
vanishing are needed, and the local reduction uses sections rather than all
cohomology. The source is retained as
`stacks-noetherian-fibre-section-lifting-2026-11-03`.
