# The affine root systems of valuation building data without V 7

For every nonarchimedean local field `F`, every affine group scheme `G` over `F`
and every `B : ValuationBuildingData G` (universe `u`), this module proves the
following parts of KP Axiom 4.1.6 for the class `A(S)` of `B`. Here
`Ψ′ = B.apartment.extendedAffineRoots`, `Ψ = B.affineRoots`, and
`Φ = Set.range (rootForm B.i)` is the set of relative roots seen as linear forms
on `TranslationSpace B.i`:

* AS 2: `Ψ′` is an affine root system
  (`AffineRootSystem.IsAffineRootSystemWithRankZero`), and its derivative set
  `AffineRootSystem.derivativeRoots Ψ′` equals `Φ`;
* AS 3 except one inclusion: `Ψ` is an affine root system and
  `derivativeRoots Ψ ⊆ Φ`;
* AS 4: for `ψ ∈ Ψ′`, `ψ ∈ Ψ` or `2ψ ∈ Ψ`;
* AS 5, first sentence: `W(Ψ) ≤ f(N(F)) ≤ W(Ψ)ᵉˣᵗ`, where
  `f = B.apartment.normalizerAffineEquiv`, `W(Ψ)` is `affineWeylGroup Ψ` and
  `W(Ψ)ᵉˣᵗ` is `extendedAffineWeylGroup Ψ`.

The proof uses neither V 7 nor any part of AS 5, and it assumes nothing about
`B` beyond its fields. The proposition does not contain V 7, the inclusion
`Φ ⊆ derivativeRoots Ψ`, or the last two sentences of AS 5. These are the
remaining parts of `B.SatisfiesApartmentAxioms`, the target
`ValuationBuildingApartmentAxiomsStatement` of module
`UnramifiedValuationDescentStatement`.

## The proposition

`ValuationBuildingAffineRootSystemsStatement : Prop` says: for all `F`, `G` and
`B` as above,

```text
IsAffineRootSystemWithRankZero Ψ′
∧ derivativeRoots Ψ′ = Set.range (rootForm B.i)
∧ IsAffineRootSystemWithRankZero Ψ
∧ derivativeRoots Ψ ⊆ Set.range (rootForm B.i)
∧ (∀ ψ ∈ Ψ′, ψ ∈ Ψ ∨ (2 : ℝ) • ψ ∈ Ψ)
∧ affineWeylGroup Ψ ≤ B.apartment.normalizerAffineEquiv.range
∧ B.apartment.normalizerAffineEquiv.range ≤ extendedAffineWeylGroup Ψ.
```

The conjuncts are, in order, the fields `isAffineRootSystem_extendedAffineRoots`,
`derivativeRoots_extendedAffineRoots`, `isAffineRootSystem_affineRoots`, one
inclusion of `derivativeRoots_affineRoots`, `mem_or_two_smul_mem`,
`affineWeylGroup_le_range` and `range_le_extendedAffineWeylGroup` of the
published structure `KPApartmentData.SatisfiesApartmentAxioms` (module
`KPApartmentAxioms`), with the same Lean expressions. The theorem
`valuationBuildingAffineRootSystems` proves it.

The affine root systems are the Library's `IsAffineRootSystemWithRankZero`
(module `RankZeroAffineRootSystem`): KP Definition 1.3.1 with the corrected AR 4
and the derivative form of AR 1, as in the published AS 2 and AS 3 fields. Its
fields are: `∇Ψ` spans `V*`; no element has zero derivative; `∇Ψ` is finite;
every element has a coroot (`IsCoroot Ψ ψ v`: `ψ̇(v) = 2` and the reflection
`η ↦ η - η̇(v) ψ` preserves `Ψ`); the coroots are integral on derivatives; each
derivative fibre is infinite; and the elements of a derivative fibre within
bounded distance of a fixed element are finitely many.

## Declarations

General lemmas:

* `AffineRootSystem.infinite_fiber_of_add_const_mem`: if `ψ ∈ Ψ`, `c ≠ 0`, and
  adding the constant `c` maps the derivative fibre of `ψ` in `Ψ` into `Ψ`, then
  that fibre is infinite. The functionals `ψ + n c`, `n ∈ ℕ`, are distinct.
* The imported `AffineRootSystem.isCoroot_unique_of_finite_of_span` from
  [AffineRootSystemPullback](AffineRootSystemPullback.md): if `∇Ψ` is finite and
  spans, every `ψ` has at most one coroot. A coroot `v` gives a reflection of the
  dual that maps `∇Ψ` into itself, so Mathlib's
  `Module.Dual.eq_of_preReflection_mapsTo` applies.
* `KPApartmentData.conjugateAffineFunctional_mem_extendedAffineRoots` (and its
  `_iff` form): for `n ∈ N(F)`, `ψ ↦ ψ ∘ f(n)⁻¹` maps `Ψ′` to `Ψ′`. This is the
  `Ψ′` part of KP Lemma 6.3.12. The derivative is the root `w(n)·a`
  (`conjugateAffineFunctional_linear_eq_rootForm`). By `conj_affineRootGroup` and
  `conj_affineRootGroupPlus` (module `RootReflectionConjugation`), conjugation by
  `n` carries `U_ψ` and `U_{ψ+}` to `U_{n·ψ}` and `U_{n·ψ+}`. So `U_ψ ≠ U_{ψ+}`
  implies `U_{n·ψ} ≠ U_{n·ψ+}`.
* `KPApartmentData.normalizerAffineEquiv_mem_rootStabilizer_extendedAffineRoots`:
  the same fact stated as `f(n) ∈ rootStabilizer Ψ′`.

For `B : ValuationBuildingData G`, in namespace `ValuationBuildingData`:

* `isCoroot_reflectionCoroot_extendedAffineRoots`: for `g ∈ U_a(F) ∖ {1}` with
  an opposite factor pair `p`, the coroot `B.reflectionCoroot hg hg1 hp` of the
  pair is a coroot of `ψ^g_a = B.reflectionFunctional a g` for `Ψ′`. Its value
  is `2` by `rootForm_reflectionCoroot`. The affine reflection it defines is
  `f(m(g))` (`normalizerAffineEquiv_reflectionElement`), which preserves `Ψ′`.
  `comp_affineReflection` turns this into the `IsCoroot` reflection condition.
* `rootForm_reflectionCoroot_integral`: every relative root takes an integer
  value on such a coroot. The coroot is the image of the cocharacter
  `hp.coroot …` of `S`, so the value is the lattice pairing.
* `derivativeRoots_extendedAffineRoots`: `∇Ψ′ = Φ`. `⊆` is the definition of
  `Ψ′`. For `⊇`, at a point `x` of the apartment the valuation `x` has some
  `g ∈ U_a(F)` with finite value (`exists_ne_top`), and
  `affineFunctional_mem_extendedAffineRoots` puts the corresponding functional,
  with derivative `a`, in `Ψ′`.
* `finite_derivativeRoots_extendedAffineRoots` and
  `span_derivativeRoots_extendedAffineRoots`: `∇Ψ′` is finite (finitely many
  relative roots, `finite_relativeRoots`) and spans. Spanning follows from the
  published `span_derivativeRoots_affineRoots_of_oppositePairs` for `Ψ ⊆ Ψ′`.
* `exists_isCoroot_extendedAffineRoots`: every `ψ ∈ Ψ′` has a coroot. The
  published `reflectionAffineRoots_eq` writes `ψ = ψ^g_a` with `g ≠ 1`, and
  `B.hasOppositeFactorPairs` gives a pair for `g`.
* `coroot_integral_extendedAffineRoots`: every coroot of `θ ∈ Ψ′` is the coroot
  of an opposite pair, by `isCoroot_unique_of_finite_of_span`, so it is integral
  on every `ψ ∈ Ψ′`.
* `coroot_integral_affineRoots`: the same for `Ψ`. Here uniqueness of the coroot
  is the published `reflectionCoroot_eq_of_isCoroot_of_locallyFinite`, applied
  with the published local finiteness
  `isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs`.
* `exists_centralizer_eval_translation_eq_neg_two`: for each relative root `a`
  there is `z ∈ Z(F)` with `a(ν(z)) = -2`, where `ν = B.translation`. Take
  `g`, `p` as above and the integral coroot `ν_a = hp.coroot …` with
  `⟨a, ν_a⟩ = 2` (`coroot_spec`). Let `z = s(ϖ^{ν_a})`, the published
  `splitTorusUniformizerPoint` of `B.centralizer.s`. Choose a character `χ` of
  `Z` restricting to `d·a` on `S` with `d > 0`
  (`exists_character_rootCharacterDenominator`). Then `ω(χ(z)) = ⟨d·a, ν_a⟩ = 2d`
  (`rationalCharacterValuation_splitTorusUniformizerPoint`), so
  `d · a(ν(z)) = -2d` (`eval_centralizerTranslation`), and `a(ν(z)) = -2`.
* `exists_conjugateAffineFunctional_eq_add_two`: with `n` the image of this `z`
  in `N(F)`, `ψ ∘ f(n)⁻¹ = ψ + 2` for every affine functional `ψ` with
  derivative `a`. V 6 for `B` (`isOmegaCompatible.smul_eq_vadd`) says that `z`
  acts on the apartment by translation by `ν(z)`.
* `infinite_fiber_extendedAffineRoots` and `infinite_fiber_affineRoots`: each
  derivative fibre of `Ψ′`, respectively `Ψ`, is infinite. Conjugation by `n`
  preserves `Ψ′` (above) and `Ψ` (published
  `conjugateAffineFunctional_mem_affineRoots`), and it adds `2` on the fibre, so
  `infinite_fiber_of_add_const_mem` applies.
* `finite_bounded_extendedAffineRoots`: for a point `x` and `C`, only finitely
  many `ψ ∈ Ψ′` satisfy `|ψ(x)| ≤ C`. This is KP Proposition 6.3.7 in the form of
  the published `finite_bounded_reflectionFunctionals_of_oppositePairs`, one root
  at a time.
* `isAffineRootSystemWithRankZero_extendedAffineRoots` (AS 2): assembled from the
  lemmas above. A nonzero derivative follows from the coroot value `2`. The
  bounded-fibre condition follows from `finite_bounded_extendedAffineRoots` at
  an arbitrary point `x`, since `|θ(x)| ≤ M + |ψ(x)|` when `|θ - ψ| ≤ M`.
* `isAffineRootSystemWithRankZero_affineRoots`: the published
  `isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs` supplies
  spanning, nonzero derivatives, finiteness of `∇Ψ`, the coroots and local
  finiteness (`finite_bounded_at`). The lemmas above supply integrality and
  infinite fibres.

The theorem `valuationBuildingAffineRootSystems` combines these. AS 4 is the
published `affineRoot_mem_or_two_smul_mem_of_oppositePairs`. The two inclusions
of AS 5 are the published `affineWeylGroup_le_range_of_AS3`, applied to
`isAffineRootSystemWithRankZero_affineRoots`, and
`range_le_extendedAffineWeylGroup_of_AS4`, applied to AS 4 (module
`NormalizerImageAffineWeylBounds`). `derivativeRoots Ψ ⊆ Φ` holds by the
definition of `Ψ`.

## Provenance and scope

Source: Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023).

* Axiom 4.1.6, AS 2–AS 5 (printed pp. 159–160, PDF pp. 190–191) states the
  conditions.
* KP prove AS 2, AS 3, AS 4 and the first sentence of AS 5 in §6.3.
  Proposition 6.3.7 (printed p. 219, PDF p. 250) gives the discreteness of each
  fibre without V 7. Proposition 6.3.8 (printed pp. 219–220, PDF pp. 250–251)
  assumes V 7; it compares `Ψ` and `Ψ′`, and its part (2) is AS 4. Lemma 6.3.12
  (printed pp. 220–221, PDF pp. 251–252) gives `N(k)`-stability. Proposition
  6.3.13 (printed p. 221, PDF p. 252) concludes through Proposition 1.3.12
  (printed p. 18, PDF p. 49). The reflections come from Proposition 6.2.1
  (printed p. 212, PDF p. 243). The authors' Corrections (version of 1 November
  2024, PDF p. 33) record that AS 1–AS 4 hold by §6.3.

The Lean proof follows a different route. It does not use Proposition 1.3.12; it
checks the fields of `IsAffineRootSystemWithRankZero` directly. Infinite fibres
come from the element `z = s(ϖ^{ν_a})` of `Z(F)`, not from Proposition 6.3.8,
which needs V 7. AS 4 is the published V 7-free result named above. The proposition is therefore weaker than KP's AS 3 by the
inclusion `Φ ⊆ ∇Ψ`. For a multipliable root `a`, KP derive this inclusion from
V 7 via Lemma 6.3.9. For a non-multipliable root it follows from AS 4 and
`∇Ψ′ = Φ`, but that case split is not part of this module.

Not covered here, and still needed for `ValuationBuildingApartmentAxiomsStatement`:
V 7 (`B.apartment.IsTopologyCompatible`), the inclusion `Φ ⊆ ∇Ψ`, and the last
two sentences of AS 5: `f(N(F)) = W(Ψ)` for simply connected `G`, and
`f(N(F)) = W(Ψ)ᵉˣᵗ` for quasi-split adjoint `G`.
