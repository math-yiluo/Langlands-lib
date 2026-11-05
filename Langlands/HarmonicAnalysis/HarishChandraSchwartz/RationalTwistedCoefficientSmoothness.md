# Twisted coefficients on `Im X(G)` for the rational points of a connected reductive group

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalTwistedCoefficientSmoothness`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- the published `HarishChandraSchwartz.TwistedCoefficientSmoothness`: `twistedCoefficientFamily`
  and `norm_torusPartialDerivList_twistedCoefficientFamily_le`, and through it `torusSynthesis`,
  `torusPartialDerivList` (`TorusFourierSynthesis`), `Space`, `nu` and `L2Weights`;
- `HarishChandraSchwartz.RationalValuationCoordinates` (Worker 249, accepted candidate
  2863d106): the lattice coordinates
  `rationalValuationCoordinates G hG` (`n(g) ∈ ℤ^r`), `measurable_rationalValuationCoordinates`
  and the character formula `rationalUnitaryUnramifiedCharacter_apply`, which states
  `χ(g) = torusCharacter (n g) z` for the character `χ` with circle coordinates `z`
  (`rationalCanonicalUnitaryUnramifiedCharacterCoordinates`, Worker 200);
- the published `BruhatTits.Unipotent.RationalPointCompactOpen`:
  `rationalPointCompactOpenSubgroup`, which gives the instance
  `Nonempty (CompactOpenSubgroup G(F))` required by `Space`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082.

- I.1, printed pp. 239–240 (PDF pp. 5–6): `G¹`, `X(G) = Hom(G/G¹, ℂ^×)`, its unitary subgroup
  `Im X(G)` and `H_G`. In the Library, `Im X(G)` is `unitaryUnramifiedCharacters` for the
  rational norm characters; `RationalValuationCoordinates.md` explains the coordinates.
- Proposition VII.1.3 and its proof, printed pp. 316–317 (PDF pp. 82–83): for `f ∈ 𝒞_H` the
  function `χ ↦ C_{v⊗v̌,f}(χ) = d(ω ⊗ χ)⟨(ω ⊗ χ)(f̌)v, v̌⟩` is in `C^∞(Im X(G))`, and the
  estimate (2) `∫_G |f̌(g)⟨ω(g)v, v̌⟩D(χ(g))| dg ⩽ c ν_r(f)`. The quotations, and the way the
  abstract module models `f̌`, `⟨ω(g)v, v̌⟩` and `D`, are in `TwistedCoefficientSmoothness.md`.

This module removes two of the identifications that `TwistedCoefficientSmoothness` leaves
open, for the actual group `G(F)`: the torus `J → Circle` is `Im X(G)` through the Library's
circle coordinates (`J = Fin (rationalImageRank G)`), and the abstract lattice map `n` is the
coordinate map of the integer valuation. The bound `‖n(g)‖ ≤ C (1 + σ(g))` remains a hypothesis
because the Library has no Waldspurger `σ` on `G(F)`. The statements are derived for this
purpose.

## Scope and hypotheses

`F` is a nonarchimedean local field (`IsNonarchimedeanLocalField F`), `G` an affine group scheme
over `F`, locally of finite type, and `G(F) = GroupScheme.rationalPoints G` carries the canonical
`rationalPointTopology F G.X`, a topological group (`rationalPoint_isTopologicalGroup`). The
connected-reductive hypothesis `hG : GroupScheme.IsConnectedReductive G` is an explicit argument
of every theorem; the definition `rationalTwistedCoefficient` does not use it. `G(F)` has a measurable space with `OpensMeasurableSpace`, and `mu` is an
arbitrary measure on it. Write `n = rationalValuationCoordinates G hG` (sup norm on
`Fin r → ℤ`).

Hypotheses of the results:

- `rationalTwistedCoefficient_comp_coordinates`: `hG`; no hypothesis on `f`, `φ` or `mu`.
- `rationalTwistedCoefficient_comp_coordinates_eq`,
  `isSmoothFiniteTorusFunction_rationalTwistedCoefficient`: `hG`, `OpensMeasurableSpace G(F)`,
  `hw : L2Weights mu Ξ σ`, `hnσ : ∀ g, ‖n(g)‖ ≤ C * (1 + σ g)`, `hφc : Continuous φ`,
  `hφ : ν_{-r}(φ) ≠ ∞`, and `f ∈ Space Ξ σ`.
- `norm_torusPartialDerivList_rationalTwistedCoefficient_le`: the same, for a list `l` of
  directions and a point `z`.

## Definitions

- `rationalTwistedCoefficient mu f φ χ = ∫_{G(F)} f(g) φ(g) χ(g) dmu(g)` for `χ ∈ Im X(G)`,
  a Bochner integral (so `0` when the integrand is not integrable).

## Results

- `rationalTwistedCoefficient_comp_coordinates`: in circle coordinates the twisted coefficient
  is `torusSynthesis mu n (f φ)`.
- `rationalTwistedCoefficient_comp_coordinates_eq`: for `f ∈ C(G)` it is the image of `f` under
  `twistedCoefficientFamily` for this `n`.
- `isSmoothFiniteTorusFunction_rationalTwistedCoefficient` (**smoothness on `Im X(G)`**): in
  circle coordinates, `χ ↦ ∫ f(g) φ(g) χ(g) dmu(g)` is smooth (`IsSmoothFiniteTorusFunction`).
- `norm_torusPartialDerivList_rationalTwistedCoefficient_le` (**estimate (2) on `Im X(G)`**):
  every iterated angle derivative along `l` is bounded by
  `|C|^{|l|} (ν_{d+r+|l|}(f) ν_{-r}(φ) c).toReal`, with `d = hw.exponent` and `c = hw.const`.

## Proof notes

1. `rationalTwistedCoefficient_comp_coordinates`: rewrite the character values with
   `rationalUnitaryUnramifiedCharacter_apply`; both sides are then the same integral.
2. The remaining results rewrite with step 1 and apply the abstract results of
   `TwistedCoefficientSmoothness` to `n`, which is measurable.

## Relation to the Library

`RationalOrbitSmoothFunctions` defines smoothness on actual discrete-series orbits by pulling
back along the same circle coordinates (`IsSmoothRationalOrbitFunction`); this module works on
`Im X(G)` itself, with scalar functions, and does not construct the orbit families
`ψ_f[𝒪, P]`. `TwistedCoefficientSmoothness` is the abstract version used here.

## Open obligations

- the bound `‖n(g)‖ ≤ C (1 + σ(g))` for Waldspurger's `σ` (I.1), which needs `σ` on `G(F)`;
- the choice `φ(g) = ⟨ω(g)v, v̌⟩` with Corollary III.1.2, `f̌` in place of `f`, the factor
  `d(ω)`, and the passage to `ψ_f[𝒪, G]` on the orbit `𝒪 = Im X(G)/S` and to general `M`
  (Lemma VII.1.2);
- a topology on smooth functions on `Im X(G)` for the continuity assertion in topological form.
