# Rank-one conductor transport at intermediate fields of the common closure: proof

Authors: Worker 96, with Worker 4803 and Worker 4918. Worker 4803's partial draft (Task 4803
draft revision 2) supplied the outline, Step 1 and the profile argument. Worker 4918 wrote the
Galois-side module `Langlands.LocalFactor.Ramification.RankOneArtinSum`.

## Result

`Langlands.LocalFactor.SpectralConductor.commonClosureRankOneConductor` has type

```
∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p), CommonClosureRankOneConductorStatement F
```

This is the published proposition
`Langlands.LocalFactor.SpectralConductor.CommonClosureRankOneConductorStatement` of module
`Langlands.LocalFactor.SpectralConductorRankOneStatement`, quantified over every prime `p`
and p-adic field `F`, at an arbitrary universe level `uF`. The proof adds no hypotheses. The
only axioms are `propext`, `Classical.choice` and `Quot.sound`. The proof uses no unproved
Library proposition. In particular it does not assume `FiniteCharacterConductorTheorems` or
`FiniteGaloisConductorInflationStatement`. The theorem works directly with the upper groups of
`M/L`, so it never passes to the abelian extension cut out by `ρ`.

Fix a normalized family `e` (`he : NormalizedReciprocity F e`), an intermediate field `L`, a
finite Galois subfield `M ⊇ L` of `F̄ = AlgebraicClosure F.Carrier`, and a continuous character
`χ` of `W_L = weilSubgroup F L`. Also fix a character `ρ` of the inertia group of `M/L`
satisfying the target's agreement hypothesis `hρ`. The algebra structures are those of the
target: `M` is an `L`-algebra through the inclusion `hLM`, and `L` is a `ℚ_p`-algebra through
`L.asPadicField`. Write `EP := L.asPadicField`,
`ι := intermediateClosureEquiv F L : AlgebraicClosure L ≃ₐ[L] F̄` (the isomorphism that
extends the literal inclusion `L ⊆ F̄`) and `χ̃ := fieldCharacterEquiv F e L χ`.

The proof has two steps. Each holds for every real `s ≥ 0`.

1. `a(χ̃) ≤ ⌈s⌉₊` exactly when `χ` is trivial on the carried upper group
   `intermediateUpperGroup F L s`, the image of the upper group `W_EP^s` of the standalone
   Weil group of `EP` under `intermediateWeilEquiv F L`.
2. `χ` is trivial on `intermediateUpperGroup F L s` exactly when `ρ` is trivial on every
   inertia element of the upper ramification group
   `upperRamificationGroup (M's canonical data) L s` of `M/L`.

The two steps together are the hypothesis of
`Ramification.Padic.inertiaArtinConductor_rankOne_eq_of_upper_levels` with `a := a(χ̃)`.
That lemma identifies the Artin expression of `ρ` with `a(χ̃)`.

## Step 1: unit levels (`RankOneProof.conductor_le_iff`)

`DeligneHenniart.intermediateUpperGroup_map_reciprocityUnits` says that the reciprocity
isomorphism `reciprocityUnits F e L` carries `intermediateUpperGroup F L s` onto the principal
units `U_L^(⌈s⌉₊)`. This lemma is in module `Langlands.LocalFactor.DeligneHenniartIntermediateUnits`.
Its premises are supplied by four published theorems:

- the third clause of `LocalClassField.absoluteUpperReciprocityTheorems`, the real-index unit
  images;
- `LocalClassField.unitFiltrationComparison`;
- `Ramification.HerbrandBridge.absoluteUpperInertia`, which says `G_EP^0` is the inertia
  group;
- `DeligneHenniart.intermediateGeometricProof p F e he L`, which makes the component of `e` at
  `L` a geometric Weil reciprocity map for `EP`.

The conductor bound `a(χ̃) ≤ ⌈s⌉₊` is triviality of `χ̃` on `U_L^(⌈s⌉₊)`
(`PadicField.TopologicalData.multiplicativeTrivialAt_iff_conductor_le`). The lemma
`trivial_iff_of_map_reciprocityUnits` turns this into triviality of the Weil character of
`χ̃` on the carried group. By `weilCharacter_fieldCharacterEquiv`, that Weil character is `χ`.

## Step 2: from `W_L` to `M/L`

`RankOneProof` uses the following auxiliary objects.

- `overL F L M hLM`: the field `M`, viewed as a finite Galois extension of `EP`. This is
  `HerbrandBridge.extendFiniteGalois` applied to the inclusion `L ⊆ M`.
- `overLEquiv`: the identity of carriers, an `L`-algebra isomorphism from
  `finiteGaloisPadicField EP (overL …)` to the statement's `absoluteFiniteExtension F M`.
- `restrictToM τ`: for `τ ∈ Gal(F̄/L)`, the restriction `AlgEquiv.restrictNormalHom` of `τ` to
  `overL …`, transported by `overLEquiv.autCongr`. `restrictToM_apply` says that it acts on
  `y ∈ M` as `τ y`.

Two lemmas transport upper groups.

- `restrictToM_mem_upper`: if `τ ∈ upperGroupIn EP F̄ s`, then `restrictToM τ` lies in the
  upper group of `M/L`. `HerbrandBridge.mem_upperGroupIn_iff` puts the restriction to
  `overL …` in its canonical upper group. Then `autCongr_mem_upperRamificationGroup_iff` for
  `overLEquiv` moves the restriction to the statement's data.
- `exists_restrictToM_eq`: every `σ` in the upper group of `M/L` of index `s ≥ -1` equals
  `restrictToM (ι.autCongr τ)` for some `τ` in the absolute upper group `G_EP^s`. The proof
  pulls `σ` back along `overLEquiv`, and then along
  `comapFiniteGaloisEquiv EP ι (overL …)` to the finite Galois subfield `ι⁻¹(M)` of
  `AlgebraicClosure L`. Both pullbacks use `autCongr_mem_upperRamificationGroup_iff`. Herbrand's
  theorem in absolute form, `HerbrandBridge.absoluteUpperFiniteImage EP`, then lifts the
  element to `G_EP^s`. Finally `autCongr_restrictNormalHom` moves the restriction back across
  `ι`.

`upper_trivial_iff` is Step 2 itself. Its key compatibility (`act`) is the following. For a
Weil element `w` of `EP`, the restriction `restrictToM (ι.autCongr (localProjection EP w))`
acts on `M` as the Galois image `localProjection F (intermediateWeilEquiv F L w)`. This
follows from `restrictToM_apply`, `intermediateWeilEquiv_projection` and
`intermediateGaloisMap_apply`.

- (⇒) Let `σ` be an inertia element of `G^s(M/L)`. Take `τ ∈ G_EP^s` from
  `exists_restrictToM_eq`. Since `s ≥ 0`, `τ ∈ G_EP^0`
  (`absoluteUpperRamificationGroup_antitone`), which is the inertia group
  (`absoluteUpperInertia`). So `τ = localProjection EP w` for a Weil element `w`
  (`absoluteInertia_le_range_localProjection`). Then `g := intermediateWeilEquiv F L w` lies
  in `intermediateUpperGroup F L s`, and that group lies in Weil inertia
  (`intermediateUpperGroup_le_inertia`). By `act`, `σ` acts on `M` as the Galois image of `g`.
  The agreement hypothesis gives `ρ σ = χ g = 1`.
- (⇐) Let `g = intermediateWeilEquiv F L w` with `w ∈ W_EP^s`. By definition of the Weil upper
  groups, `localProjection EP w ∈ G_EP^s`. By
  `HerbrandBridge.mem_absoluteUpperRamificationGroup_iff_autCongr EP ι`, its image under
  `ι.autCongr` lies in `upperGroupIn EP F̄ s`. So `σ := restrictToM (ι.autCongr …)` lies in
  `G^s(M/L)` (`restrictToM_mem_upper`). It also lies in `G^0(M/L)`, which is the inertia group
  (`upperRamificationGroup_antitone`, `upperRamificationGroup_zero`). Again `g` is in Weil
  inertia, and by `act` the agreement hypothesis gives `χ g = ρ σ = 1`.

## Assembly (`commonClosureRankOneConductor`)

After the target's local instances are introduced, the goal is the `ℚ`-cast of
`inertiaArtinConductor … (rankOneCharacterRepresentation ρ) = a(χ̃)`. The proof is
`exact_mod_cast` applied to `Ramification.Padic.inertiaArtinConductor_rankOne_eq_of_upper_levels`
(module `Langlands.LocalFactor.Ramification.RankOneArtinSum`) with `a := a(χ̃)`. Its hypothesis
is `fun s hs => (conductor_le_iff …).trans (upper_trivial_iff …)`. The Galois-side lemma reads
the Artin expression off the upper-numbering profile, through the formula
`inertiaArtinConductor_eq_integral` of module
`Langlands.LocalFactor.Ramification.InertiaConductorProfile`: the real Artin expression is
`d(0) + ∫_0^B d(v) dv` for a large enough bound `B`, where `d(v)` is the codimension in the
line `ℂ` of the subspace fixed by the upper group `G^v`. For `v ≥ 0` the hypothesis gives `d(v) = 0` if
`a ≤ ⌈v⌉` and `d(v) = 1` otherwise. If `a = 0`, then `d` vanishes on `[0, B]` and the
expression is `0`. If `a = n + 1`, then `d = 1` on `[0, n]` (where `⌈v⌉ ≤ n`) and `d = 0`
for `v > n`; so the expression is `d(0) + n = 1 + n = a`. This is Serre's formula
"conductor = last upper break + 1" (VI §2, Proposition 5, p. 102), here with last upper break
`a − 1`. The helper's Markdown gives the details.

## Literature and route

The mathematics is Serre, *Local Fields* (Springer GTM 67, 1979). XV §2, Theorem 1 and its
Corollaries 2 and 3 (printed pp. 227–228) are upper-numbering reciprocity. XV §2, Theorem 2
(p. 228) says that reciprocity carries `U^n` onto the upper group `G^n`. The bracketed remark
after Corollary 2, together with VI §2, Proposition 5 and its Corollary (p. 102), says that the
conductor of a character equals its Artin conductor. IV §3, Proposition 14 says that upper
groups pass to quotients. Serre passes from `M/L` to the abelian extension cut out by `ρ`
through inflation invariance (VI §2, Proposition 3). The Lean proof avoids that step. It
compares the absolute upper groups of `L`, carried into the common closure, with the upper
groups of `M/L` directly by restriction (Step 2), and it reads the Artin expression off the
upper-numbering profile.
