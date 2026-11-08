# Breaks of restrictions to finite intermediate fields

Lean module: `Langlands.LocalFactor.Ramification.Herbrand.WeilRestrictionProof`
(namespace `Langlands.Ramification.HerbrandBridge`). It imports
`Langlands.LocalFactor.Ramification.Herbrand.ConvexityProof`,
`Langlands.LocalFactor.Ramification.Herbrand.WeilInertiaProof` and
`Langlands.Weil.Representation.InductionContinuity`.

## What the module proves

Let `F : PadicField.{u} p` and `E : FiniteIntermediateExtension F.Carrier`, with
`E.asPadicField` its Library p-adic structure. Write `ψ_{E/F}` for `relativeHerbrandPsi E`
(`SubextensionProof`). `intermediateWeilMap F E` is the Library continuous embedding of the
Weil group of `E.asPadicField` into that of `F`. Breaks and triviality are the Library notions
`lastBreak`, `IsTrivialAt` and `upperGroup` of `LocalWeil.Ramification`.

- `weilRestrict E A`, the named definition (an abbreviation), is
  `FiniteRepresentation.restrict (intermediateWeilMap F E).toMonoidHom A`: the restriction of a
  representation `A` of the Weil group of `F` to the Weil group of `E`.
  `weilRestrict_isContinuous` says that continuity is preserved.
- `intermediateWeilMap_mem_upperGroup_iff E hr w`: for `r ≥ -1`, the image of `w` lies in
  `upperGroup F r` if and only if `w ∈ upperGroup E.asPadicField (ψ_{E/F}(r))`. This restates
  `intermediateWeilEquiv_mem_upperGroup_iff`.
- `isTrivialAt_weilRestrict`: if `A` is trivial at `r ≥ 0`, then `weilRestrict E A` is trivial
  at `ψ_{E/F}(r)`.
- `lastBreak_weilRestrict_lt`: for continuous `A`, `lastBreak F A < b` implies
  `lastBreak (weilRestrict E A) < ψ_{E/F}(b)`.
- `lastBreak_weilRestrict_le`: for continuous `A`,
  `lastBreak (weilRestrict E A) ≤ ψ_{E/F}(lastBreak F A)`. This is DH81's `β(W_i) ≤ ψ(β(W))`
  for a single representation.
- `lastBreak_eq_relativeHerbrandPsi`. Let `B` be a continuous representation of the Weil group
  of `E` and `a > 0`. Suppose that
  - `B` is trivial on every `x` whose image lies in `upperGroup F w` for some `w > a`;
  - `B` is not trivial on all `x` whose image lies in `upperGroup F a`.

  Then `lastBreak E.asPadicField B = ψ_{E/F}(a)`. This is DH81's `α(χ_i) = ψ_{L_i/K}(α(V))`.
- `lastBreak_weilRestrict_lt_half`: for continuous `A` and `a > 0`, `lastBreak F A < a/2`
  implies `lastBreak (weilRestrict E A) < ψ_{E/F}(a)/2`. This is the inequality chain of DH81 4.8,
  `β(W_i) ≤ ψ(β(W)) < ψ(α/2) ≤ ψ(α)/2`.

The passage from these statements about single representations to virtual constituents is not
part of this module.

## Sources

Deligne–Henniart (1981), §4.5 (printed p. 110, PDF p. 22) and §4.8 (printed p. 111, PDF p. 23),
registered as `deligne-henniart-1981-variation`.
- 4.5 states `β(W_i) ≤ ψ_{L_i/K}(β(W))` and `α(χ_i) = ψ_{L_i/K}(α(V))`.
- 4.8 states the chain
  `β(W_i) ≤ ψ_{L_i/K}(β(W)) < ψ_{L_i/K}(α(V)/2) ≤ ψ_{L_i/K}(α(V))/2 = α(χ_i)/2`.

The Herbrand inputs are the Library-level theorems of my modules `SubextensionProof`
(`G_F^v ∩ G_E = G_E^{ψ_{E/F}(v)}`), `ConvexityProof` (monotonicity, continuity,
`ψ(a/2) ≤ ψ(a)/2`) and `WeilInertiaProof` (`lastBreak < b` iff trivial at `b`). `weilRestrict`
and the arguments below are internal.

## Proof (as implemented)

1. **Triviality.** If `w ∈ upperGroup E.asPadicField (ψ_{E/F}(r))`, its image lies in
   `upperGroup F r` by `intermediateWeilMap_mem_upperGroup_iff`. So `A` acts trivially on it.
2. **Strict bound.** Choose `r` with `lastBreak F A < r < b`. By
   `lastBreak_lt_iff_isTrivialAt` the representation `A` is trivial at `r > 0`, so by step 1 the
   restriction is trivial at `ψ_{E/F}(r) ≥ 0`. Hence its last break is at most `ψ_{E/F}(r)`
   (`lastBreak_le_of_mem`), which is `< ψ_{E/F}(b)` by strict monotonicity.
3. **Non-strict bound.** For `ε > 0`, continuity of `ψ_{E/F}` at `lastBreak F A` gives `δ` such
   that `b = lastBreak F A + δ/2` has `ψ_{E/F}(b) < ψ_{E/F}(lastBreak F A) + ε`. Step 2 bounds the
   restricted break by `ψ_{E/F}(b)`. Conclude with `le_of_forall_pos_lt_add`.
4. **Exact break.** By the first hypothesis and step 1's equivalence, `B` is trivial at
   `ψ_{E/F}(w)` for every `w > a`. Continuity of `ψ_{E/F}` at `a`, as in step 3, gives
   `lastBreak B ≤ ψ_{E/F}(a)`. If the inequality were strict, then `B` would be trivial at
   `ψ_{E/F}(a) > 0` by `lastBreak_lt_iff_isTrivialAt`, contradicting the second hypothesis.
5. **Chain.** Step 2 with `b = a/2` gives `lastBreak (weilRestrict E A) < ψ_{E/F}(a/2)`, and
   `relativeHerbrandPsi_half_le` gives `ψ_{E/F}(a/2) ≤ ψ_{E/F}(a)/2`.

Only the standard axioms `propext`, `Classical.choice` and `Quot.sound` are used.
