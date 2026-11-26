# Smoothing operators on the weighted Siegel Hilbert space

Module `Langlands.Global.AdelicLocalFinitenessSmoothing` (namespace `WeightedSiegel`). Setting:
a closed subgroup `p : P → G` of a group over a number field with an Iwasawa subgroup `K`
(Iwasawa height `H`), linear coordinates `e` on the real character dual of `P` with root part
indexed by a finite type `Δ` and `r` further coordinates, and the log weight
`ell = localFinitenessLogWeight ra rb ∘ e`.

## Definitions and auxiliary results

- `siegelHeightRegion e τ = {H | τ_α < (e H)_α for every α ∈ Δ}`, the Siegel region of heights;
  `isOpen_siegelHeightRegion`: it is open for continuous `e`.
- `haar_preimage_eq_zero`: let every point `y ∈ G(𝔸)` have a rational translate whose height lies
  in a Borel region `S₀`. Then a measurable set `E` of `G(F) \ G(𝔸)` that is null for the weighted
  automorphic measure of `S₀` (module `AdelicWeightedSiegelSpace`) has Haar-null preimage in
  `G(𝔸)`. Proof: by `lintegral_domainMeasure_eq_chamberDensity` the weighted integral of the
  indicator of `E` over the fundamental domain `D` of `P(F)` vanishes; the chamber density is
  positive on the heights in `S₀`, so `Z = D ∩ π⁻¹(E) ∩ H⁻¹(S₀)` is Haar null. Every point of
  `π⁻¹(E)` has a rational translate in `Z`: first a rational translate with height in `S₀`, then
  the `P(F)`-translate into `D` (`fundamentalDomain_unique`), which keeps the height
  (`height_rational_mul`) and the class modulo `G(F)`. So `π⁻¹(E)` lies in the countable union of
  the left translates of `Z` by `G(F)`, each Haar null by left invariance.

## `exists_smoothingOperators`

Hypotheses: every `x ∈ G(𝔸)` has a rational point `q` with the finite component of `q x` in a
compact `Ω`, `(e(H(q x)))_α ≥ θ_α` for every `α`, and `ht(q x) ≤ M ht(x)^t` (`M > 0`, `t ≥ 0`,
`ht` the adelic height of a closed matrix embedding `ρ` of positive size); a finite family of test
functions `h_k` (`IsAdelicTestFunction`).

Conclusion: there is `δ ≥ 0` (depending only on `e`, `K` and the supports of the kernels) such that
for every `τ` with `τ_α + δ < θ_α` for all `α`, and all rates `ra`, `rb` whose log weight
`ell = localFinitenessLogWeight ra rb ∘ e` satisfies `exp(ell(H g)) ≤ W ht(g)^{r'}` (`W > 0`,
`r' ≥ 0`), there is `R₀ ≥ 0` such that for every `R ≥ R₀` and every subgroup `L ≤ G(𝔸_f)` under
which the kernels are left invariant there are continuous linear maps

```
K_k : HilbertSpace F p hK ell (H⁻¹(siegelHeightRegion e τ)) →L[ℂ] 𝔉^R_L
```

such that for every vector `b` and every measurable function `f` on `G(F) \ G(𝔸)` almost everywhere
equal to `b` for the weighted automorphic measure, the function of `K_k b` is the right convolution
`δ(h_k)(f ∘ π)` at every point of `G(𝔸)`. The order of the quantifiers lets the threshold `τ` be
fixed before the rates.

Proof. The union `C` of the supports of the kernels is compact, and
`IsIwasawaCompact.iwasawaHeightCoordinateRightShift` bounds by `δ` the change of each root
coordinate under right translation by `C`. Let `Y` be the set of points whose finite component lies
in `Ω` and whose root coordinates are at least `θ`. The Library theorem
`adelicWeightedSmoothingOperator` applied to `ell`, the weight bound and the representatives in
`Y` gives `R₀`. For `τ_α + δ < θ_α`, the open
region `S = siegelHeightRegion e τ` contains the heights of `Y` and of all `y a` with `y ∈ Y`,
`a ∈ C`. `weightedHilbertRealization` gives a linear measurable realization `rep` of the Hilbert
space by `G(F)`-invariant functions with weighted chamber norm at most the Hilbert norm (the
enlarged region is `S` itself, so the measure comparison holds with constant `1`). The smoothing
theorem then gives `K_k` with `K_k b = δ(h_k)(rep b)`. If `f` represents `b`, then `rep b` and
`f ∘ π` differ only on the preimage of a set null for the automorphic measure; every point has a
rational translate with height in `S`, so this preimage is Haar null (`haar_preimage_eq_zero`),
and so are its left translates; hence the two convolution integrals agree.

## Provenance

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37
(2024), 187–234, §7.4, Lemma (2) and its proof, p. 216: `δ(h)` maps the weighted Hilbert space to
functions of uniform moderate growth, modelled on an auxiliary Siegel domain containing the right
translates of the Siegel domain by the support of `h`; this module realizes it for the Siegel
region of the local-finiteness weight, where one region serves both as the Hilbert domain and as
the enlarged convolution region (literature id
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`).
