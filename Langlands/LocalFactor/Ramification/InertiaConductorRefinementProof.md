# Refining an inertia presentation preserves its Artin and Swan sums

Module `Langlands.LocalFactor.Ramification.InertiaConductorRefinementProof`.

## Result

`Langlands.Ramification.Padic.finiteInertiaConductorRefinement` proves the Library
proposition `Langlands.Ramification.Padic.FiniteInertiaConductorRefinementStatement F A`
(module `Langlands.LocalFactor.Ramification.InertiaPresentationStatement`) for every
prime `p`, every p-adic field `F : PadicField.{uF} p` and every
`A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)`. The universes `uF` and `uV`
are independent. Its type is

```
∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)),
  FiniteInertiaConductorRefinementStatement F A
```

That is, for a finite inertia presentation `P` of `A`, a finite Galois subfield
`M ⊇ P.extension` with inclusion `h`, and the surjectivity proofs `hP` and `hM`,
`(P.refine M h).artinConductor hM = P.artinConductor hP` and
`(P.refine M h).swanConductor hM = P.swanConductor hP`. There is no continuity
hypothesis on `A`. The axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Idea

Fix the data of an actual finite extension: `T : F.TopologicalData`, a base field `K`,
its inertia group `inertia T K`, a finite-dimensional complex vector space `V`, and
`ρ : Representation ℂ (inertia T K) V`. Write `n = finrank ℂ V`, `g_i = lowerGroupOrder T K i`,
`φ = herbrandPhi T K`, `ψ = herbrandPsi T K`, `b = ramificationCutoff T K`, and
`d(v) = finrank ℂ (inertiaUpperFixedVectors T K ρ v)`, the dimension of the space fixed
by the upper group `G^v`. Then:

* the Swan sum equals `∫₀^B (n − d(v)) dv` for every `B ≥ φ(b)`;
* the Artin sum equals `(n − d(0)) + ∫₀^B (n − d(v)) dv` for the same `B`.

So both sums depend only on `n` and on the function `d` on `[0, B]`. Let `P` and `Q` be
two finite inertia presentations of the same `A`. The Library comparison
`HerbrandBridge.presentationUpperFixedComparison` shows that at every `v ≥ 0` both
upper fixed spaces equal `upperFixedSpace F A v`. That space is defined from the
absolute upper ramification groups of the Weil group alone. So the two dimension
functions agree on `[0, ∞)`. Take `B` at least as large as both cutoff images. Then the
integrals agree, and so do the sums. The target is the case `Q = P.refine M h`.

This replaces Serre's quotient argument (*Local Fields*, VI §2, Proposition 3 and its
Corollary) by a comparison of upper-numbering profiles. The finite inertia groups of
`P.extension` and `M` are never compared directly.

## The finite-level formulas (namespace `Langlands.Ramification.Padic.InertiaConductorRefinement`)

The variables are those of `Langlands.LocalFactor.Ramification.Breaks`: `T`, `K`
with `[Field K] [Algebra (Padic p) K] [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]`,
and `ρ` as above.

* Three private lemmas, `integers_isNoetherianRing`, `automorphisms_finite` and
  `inertiaAction_faithful`, prove that `T.Integers` is Noetherian, that
  `F.Carrier ≃ₐ[K] F.Carrier` is finite, and that `inertia T K` acts faithfully on
  `T.Integers` through `inertiaIntegerAction T K`. They are copies of the private
  lemmas of `Langlands.LocalFactor.Ramification.Galois` that `inertiaSwanConductor` uses
  to install the same instances. All three are propositions, so the instances they
  provide are definitionally those in the definition of `inertiaSwanConductor`.
* `card_inertiaLowerGroup`: `Nat.card (inertiaLowerGroup T K i) = lowerGroupOrder T K i`.
  `G_i ≤ G_0 = inertia T K` (`lowerRamificationGroup_antitone`, `lowerRamificationGroup_zero`),
  and `Subgroup.subgroupOfEquivOfLe` identifies `G_i.subgroupOf (inertia T K)` with `G_i`.
* `herbrandPhi_succ_sub`: `φ(i + 1) − φ(i) = g_(i+1) / g_0`. This is the Library floor
  formula `herbrandPhi_floor` at the natural numbers `i` and `i + 1`, where the fractional
  part vanishes (`Nat.floor_natCast`), followed by `Finset.sum_range_succ`.
* `inertiaUpperFixedVectors_monotone`: `v ↦ inertiaUpperFixedVectors T K ρ v` is monotone,
  because `upperRamificationGroup_antitone` makes the upper groups decrease.
* `inertiaUpperFixedVectors_of_mem_Ioo`: for `φ(i) < v < φ(i + 1)`, the upper fixed space
  is `fixedVectors ρ (inertiaLowerGroup T K (i + 1))`. Applying the strictly monotone
  `ψ` (`herbrandPsi_strictMono`, `herbrandPsi_herbrandPhi`) gives `i < ψ(v) < i + 1`, so
  `⌈ψ(v)⌉₊ = i + 1` (`Nat.ceil_eq_iff`). The Library lemma
  `inertiaUpperFixedVectors_eq_natceil` then applies, because `v > φ(i) ≥ φ(0) = 0`.
* `inertiaUpperFixedVectors_eq_top`: for `v ≥ φ(b)` the upper fixed space is `⊤`. Here
  `ψ(v) ≥ b`, so `upperRamificationGroup T K v = lowerRamificationGroupReal T K (ψ v) = ⊥`
  (`lowerRamificationGroupReal_eq_bot_of_cutoff`), and every element of the trivial group
  acts as the identity.
* `inertiaUpperFixedVectors_zero`: `inertiaUpperFixedVectors T K ρ 0 = fixedVectors ρ ⊤`,
  from the Library lemma `inertiaUpperFixedVectors_phi` at `0`, `herbrandPhi_zero` and
  `inertiaLowerGroup_zero`.
* `upperCodimension T K ρ v := (finrank ℂ V : ℝ) − finrank ℂ (inertiaUpperFixedVectors T K ρ v)`
  is a helper definition introduced for this proof. It is the real-valued codimension
  `n − d(v)` above. `upperCodimension_antitone` shows that it is antitone (from the
  monotonicity of the fixed spaces and `Submodule.finrank_mono`). Hence it is interval
  integrable on every interval (`upperCodimension_intervalIntegrable`, by Mathlib's
  `Antitone.intervalIntegrable`).
* `integral_upperCodimension_step`: `∫_{φ(i)}^{φ(i+1)} upperCodimension = (g_(i+1)/g_0) · (n − dim V^(G_(i+1)))`.
  On the open interval the integrand is constant (`inertiaUpperFixedVectors_of_mem_Ioo`).
  Mathlib's `intervalIntegral.integral_congr_Ioo_of_le` and `intervalIntegral.integral_const`
  evaluate the integral, and `herbrandPhi_succ_sub` gives the length of the interval.
* `inertiaSwanConductor_eq_sum`: `(inertiaSwanConductor T K ρ : ℝ) = Σ_{i < b} (g_(i+1)/g_0) · (n − dim V^(G_(i+1)))`.
  After installing the instances above, `inertiaSwanConductor T K ρ` is by definition
  `Ramification.swanConductor T.Integers (inertia T K) ρ`. The abstract lower groups
  `lowerGroup T.Integers (inertia T K) i` are by definition `inertiaLowerGroup T K i`. They
  vanish for `i ≥ b` (`lowerRamificationGroup_eq_bot_of_cutoff`, `Subgroup.bot_subgroupOf`),
  so `Ramification.swanConductor_eq_sum_range` (module
  `Langlands.LocalFactor.Ramification.Conductor`) writes the sum as
  `Σ_{i < b} conductorTerm (i + 1)`. Each term `conductorTerm` is
  `(card G_(i+1) / card G_0) · fixedCodimension`. `card_inertiaLowerGroup` gives the
  cardinalities, and `fixedCodimension` is `n − dim V^(G_(i+1))` as a natural number.
  Its real cast is computed by `Nat.cast_sub` with `Submodule.finrank_le`.
* `inertiaSwanConductor_eq_integral`: for `φ(b) ≤ B`,
  `(inertiaSwanConductor T K ρ : ℝ) = ∫ v in 0..B, upperCodimension T K ρ v`. The integral
  over `[0, B]` splits at `φ(b)` (`intervalIntegral.integral_add_adjacent_intervals`). On
  `[φ(b), B]` the integrand is `0` by `inertiaUpperFixedVectors_eq_top`, which is used
  through `intervalIntegral.integral_congr`. The integral over `[0, φ(b)] = [φ(0), φ(b)]` is the sum
  of the integrals over `[φ(i), φ(i+1)]` for `i < b` (`intervalIntegral.sum_integral_adjacent_intervals`).
  `integral_upperCodimension_step` turns this sum into `inertiaSwanConductor_eq_sum`.
* `inertiaArtinConductor_eq_integral`: for `φ(b) ≤ B`,
  `(inertiaArtinConductor T K ρ : ℝ) = upperCodimension T K ρ 0 + ∫ v in 0..B, upperCodimension T K ρ v`.
  The Library lemma `inertiaArtinConductor_eq_tame_add_swan` (module `Galois`) gives
  Artin = `fixedCodimension (inertia T K) ρ ⊤` + Swan. The tame term is
  `upperCodimension T K ρ 0` by `inertiaUpperFixedVectors_zero` and `Nat.cast_sub`.

## Comparison of presentations (namespace `Langlands.Ramification.Padic`)

* `presentation_conductors_eq F A P Q hP hQ`: two finite inertia presentations `P` and `Q`
  of the same `A`, with surjectivity proofs `hP` and `hQ`, satisfy
  `P.artinConductor hP = Q.artinConductor hQ` and `P.swanConductor hP = Q.swanConductor hQ`.
  Write `TP` and `TQ` for the canonical topological data of `absoluteFiniteExtension F P.extension`
  and `absoluteFiniteExtension F Q.extension`.
  1. For `v ≥ 0`, `HerbrandBridge.presentationUpperFixedComparison F A P hP v` and the same
     lemma for `Q` (module `Langlands.LocalFactor.Ramification.Herbrand.WeilBreakProof`)
     identify both `inertiaUpperFixedVectors TP F.Carrier (P.representation hP) v` and
     `inertiaUpperFixedVectors TQ F.Carrier (Q.representation hQ) v` with
     `VirtualRepresentation.LocalWeil.Ramification.upperFixedSpace F A v`. So the two
     `upperCodimension` functions agree on `[0, ∞)`.
  2. Let `B` be the maximum of `φ_P(b_P)` and `φ_Q(b_Q)`. It is nonnegative because
     `φ_P` is monotone with `φ_P(0) = 0`. The two integrals over `[0, B]` agree by
     `intervalIntegral.integral_congr`.
  3. `P.artinConductor hP` is by definition
     `inertiaArtinConductor TP F.Carrier (P.representation hP)`, through
     `artinConductorOfQuotient` and `descendInertiaRepresentation`; the same holds for
     the Swan sums. After casting to `ℝ` (`Rat.cast_injective`),
     `inertiaSwanConductor_eq_integral` and `inertiaArtinConductor_eq_integral` at `B`
     reduce both equalities to steps 1 and 2.
  This lemma has the form of the Library proposition
  `FiniteInertiaConductorIndependenceStatement F A`. This module does not state it as a
  proof of that proposition.
* `finiteInertiaConductorRefinement`: given `P`, `M`, `h`, `hP` and `hM`, apply
  `presentation_conductors_eq` to the presentations `P.refine M h` and `P`. The
  extension of `P.refine M h` is by definition `M`, so `hM` is the required surjectivity
  proof for it.

## Imported Library results

Module `Langlands.LocalFactor.Ramification.Galois`: `inertia`, `inertiaIntegerAction`,
`inertiaLowerGroup`, `inertiaLowerGroup_zero`, `lowerRamificationGroup_zero`,
`lowerRamificationGroup_antitone`, `inertiaArtinConductor`, `inertiaSwanConductor`,
`inertiaArtinConductor_eq_tame_add_swan`.
Module `Langlands.LocalFactor.Ramification.Conductor`: `Ramification.swanConductor_eq_sum_range`,
`conductorTerm`, `fixedCodimension`.
Module `Langlands.LocalFactor.Ramification.Herbrand.Finite`: `lowerGroupOrder`,
`lowerGroupOrder_pos`, `ramificationCutoff`, `lowerRamificationGroup_eq_bot_of_cutoff`,
`herbrandPhi`, `herbrandPhi_floor`, `herbrandPhi_zero`, `herbrandPhi_strictMono`,
`herbrandPsi`, `herbrandPsi_strictMono`, `herbrandPsi_herbrandPhi`,
`upperRamificationGroup`, `upperRamificationGroup_antitone`,
`lowerRamificationGroupReal_eq_bot_of_cutoff`.
Module `Langlands.LocalFactor.Ramification.Breaks`: `inertiaUpperFixedVectors`,
`inertiaUpperFixedVectors_eq_natceil`, `inertiaUpperFixedVectors_phi`.
Module `Langlands.LocalFactor.Ramification.InertiaPresentation`: `FiniteInertiaPresentation`,
`FiniteInertiaPresentation.representation`, `.artinConductor`, `.swanConductor`, `.refine`.
Module `Langlands.LocalFactor.Ramification.Herbrand.WeilBreakProof`:
`HerbrandBridge.presentationUpperFixedComparison`.
Mathlib: `intervalIntegral.integral_add_adjacent_intervals`,
`intervalIntegral.sum_integral_adjacent_intervals`, `intervalIntegral.integral_congr`,
`intervalIntegral.integral_congr_Ioo_of_le`, `intervalIntegral.integral_const`,
`Antitone.intervalIntegrable`, `Subgroup.subgroupOfEquivOfLe`, `Nat.ceil_eq_iff`,
`Nat.floor_natCast`.

## Literature

J.-P. Serre, *Local Fields* (1979), registered as `serre-1979-local-fields`
(`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256 `109b461d…`).
* IV §3, printed p. 74 (PDF p. 81): the upper numbering `G^v = G_(ψ(v))`. The function
  `herbrandPhi` is the Library's piecewise-linear `φ`, with slope `g_(i+1)/g_0` on `[i, i+1]`.
* VI §2, printed p. 101 (PDF p. 108): Corollary 1′ to Proposition 2 gives
  `f(χ) = Σ_i (g_i/g_0) codim V^(G_i)`, which is the Library definition of the Artin
  sum. Proposition 3 and its Corollary give invariance under inflation from a quotient,
  which is the classical form of the statement proved here.

The proof in this module is not Serre's. It writes the sums as integrals over the
upper-numbering index of the codimension of the upper fixed spaces, and it compares
those fixed spaces through the absolute upper groups of the Weil group.
