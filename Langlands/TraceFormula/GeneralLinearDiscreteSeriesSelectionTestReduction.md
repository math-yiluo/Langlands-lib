# The square-integrable selection test for `GL_n` from normalized pseudo-coefficients

Module `Langlands.TraceFormula.GeneralLinearDiscreteSeriesSelectionTestReduction`, namespace
`Langlands.TraceFormula.DiscreteSeriesSelection`.

The module states and proves the conditional reduction

```
DeterminantSlicePseudoCoefficientExistenceStatement.{u, max u uV uW} →
  GeneralLinearDiscreteSeriesSelectionTestStatement.{u, uV, uW}
```

The proposition is `GeneralLinearDiscreteSeriesSelectionTestReductionStatement.{u, uV, uW}`, and
its proof is `generalLinearDiscreteSeriesSelectionTestReduction`. That proof applies the theorem
`generalLinearDiscreteSeriesSelectionTest_of_determinantSlicePseudoCoefficient`, which takes the
premise as a hypothesis. The conclusion is exactly
`Langlands.TraceFormula.GeneralLinearDiscreteSeriesSelectionTestStatement` (module
`Langlands.TraceFormula.GeneralLinearLocalSelectionTestStatement`) at arbitrary universes. The
premise `Langlands.BaseChange.DeterminantSlicePseudoCoefficientExistenceStatement` (module
`Langlands.BaseChange.DeterminantSlicePseudoCoefficientStatement`) is stated in its module and
proved neither there nor here. It asserts the existence of elliptic pseudo-coefficients of
square-integrable representations that are normalized on determinant slices. This module
therefore gives no unconditional proof of the selection test.

## Universe of the premise

The premise is used at the carrier universe `max u uV uW`, for the universe lift
`universeLiftRepresentation.{max u uW} ρ` of `ρ` on `ULift V`. Over a field in `Type u`, the
classification of generic representations, `Classification.genericSegmentProductExhaustion`,
treats smooth representations with carrier in a universe `max u w`, by segment data with
carriers in the same universe. It is applied to the lifts to `Type (max u uV uW)` of twists of
the lift of the tested representation `π` to `ULift W : Type (max uW uV)`. Clauses (a) and (b)
of the premise speak only of representations whose carrier is in the universe of the carrier
of `ρ`, so the lift of `ρ` must also be in `max u uV uW`.

## Auxiliary results

*Sums of roots of unity.* `sum_range_zpow_pow`: for a primitive `n`-th root of unity `ζ` and
`m : ℤ`, `∑_{k < n} (ζ^m)^k` is `n` if `n ∣ m` and `0` otherwise (geometric sum).

*Characters at test functions* (section `Generic`). Here `G` is a Hausdorff, locally compact and
totally disconnected topological group with its Borel σ-algebra, and
`Character.distribution μ ρ hρ f` is the trace of `ρ(f) = ∫ f(g) ρ(g) dμ(g)`.

- `weightedTest χ hloc f` is the test function `g ↦ χ(g) f(g)`, for `χ : G →* ℂˣ` with locally
  constant values.
- `Character.distribution_twist_weightedTest`: the character of `twist χ ρ` at `f` is the character of `ρ` at
  `weightedTest χ hloc f`, because the two integrated operators agree.
- `Character.distribution_eq_of_equiv`: equivalent admissible representations have the same character
  (from `Character.distribution_eq_of_equivariant`).
- `distribution_nnreal_smul_measure`: replacing `μ` by `c • μ` multiplies the character by `c`.
- `distribution_ne_zero_of_haar`: on a second-countable group two Haar measures are proportional
  (`Measure.isMulLeftInvariant_eq_smul`), so whether the character vanishes at `f` does not depend
  on the Haar measure.
- `eq_of_distribution_ne_zero_of_leftCovariant`: suppose `φ(z g) = b⁻¹ φ(g)` for all `g`, that
  `ρ(z)` is the scalar `a`, and that the character of `ρ` at `φ` is nonzero. Then `a = b`. The left
  translate of `φ` by `z` is `b φ`, and `ρ(z) ρ(φ)` is that translate's operator, so
  `b · tr ρ(φ) = a · tr ρ(φ)`.
- `sum_weightedTest_eq_smul_cutoff`: let `δ : G →* Multiplicative ℤ` be continuous, `ζ` a
  primitive `n`-th root of unity and `u ∈ ℂˣ`. Suppose `f` vanishes at each `g` with
  `n ∣ δ(g)` and `δ(g) ≠ 1`. Then the weighted tests of `f` by the characters
  `g ↦ (ζ^k u)^{δ(g)}`, `k < n`, sum to `n` times `ConcordanceLocalization.cutoff` of `f` to
  the clopen set `δ⁻¹{1}`. Here `Multiplicative ℤ` is written additively in exponents. Pointwise,
  `(ζ^k u)^{δ(g)} = (ζ^{δ(g)})^k u^{δ(g)}`, so `sum_range_zpow_pow` applies.

*Scaling* (section `Scaling`). `isCompatible_nnreal_smul`: if `ν` is a quotient measure
compatible with `μG` and `μH`, then `c • ν` is compatible with `c • μG` and `μH` for `c ≠ 0`.
`orbitalIntegral_nnreal_smul`: orbital integrals are linear in the quotient measure.

*Genericity of determinant twists.* Let `F` be a `PadicField` with topological data `T`, and let
`χ : Fˣ →* ℂˣ` be a character such that `χ ∘ det` has open kernel. Then
`isGeneric_twist_of_isOpen_ker` says that the twist by `χ ∘ det` of a `ψ`-generic representation
is `ψ`-generic. Irreducibility comes from `isIrreducible_twist_iff` and admissibility from
`isAdmissible_twist_iff`. The Whittaker functional is carried over by
`Whittaker.determinantTwistFunctionalEquiv`.

*Classification* (section `Classification`). Let `F` be a `PadicField` with topological data
`T`, and let `n = r + 1`. Let `ρ` be admissible on a carrier in `Type (max uF uW)`, and let `χ`
be a unitary character of the centre with open kernel. Let `f` be a pseudo-coefficient of `ρ`
for `χ` (`IsPseudoCoefficient`) whose characters vanish at every admissible unnormalized
smooth induction, from a standard block parabolic subgroup with at least two blocks, of an
irreducible admissible representation of the Levi product (carrier in `Type (max uF uW)`).
Then `nonempty_equiv_of_distribution_ne_zero` says the following. Every irreducible admissible
representation `σ` with carrier in `Type uW` that is generic for some unitary additive
character, has central character `χ`, and whose character at `f` is nonzero, is equivalent to
`ρ`. The proof:

- The universe lift of `σ` (`SmoothRep.universeLift`) is generic, and
  `Classification.genericSegmentProductExhaustion` gives segment data `d` with `σ` equivalent to
  `d.induced`. This is the normalized parabolic induction of the external tensor product `τ` of
  the segment representations of the blocks.
- If `d` has at least two blocks, `d.induced` is by definition the unnormalized smooth induction
  of `Ξ`, the twist of `τ` by the Levi half-modulus. `Ξ` is irreducible and admissible by
  `FiniteTensor.isIrreducible_external` and `FiniteTensor.isAdmissible_external`, and its twists.
  The induced-vanishing hypothesis then makes the character of `σ` vanish at `f`, which is
  excluded.
- If `d` has one block, `σ` is equivalent to a reindexing of a segment representation. That is
  essentially square-integrable by `segmentSpecialEssentialSquareIntegrability`. Since the central
  character `χ` is unitary, `σ` is square-integrable by
  `isSquareIntegrable_of_essential_of_unitaryCentralCharacter`. Hence it is tempered, by
  `Unramified.isTempered_of_isSquareIntegrable` and `isTemperedRep_iff_isTempered`. If `σ` were
  not equivalent to `ρ`, the pseudo-coefficient property would make the character of its
  universe lift vanish at `f`.

*Valuation degree* (section `Completion`). For a finite place `v` of a number field `K`,
`unitDegree v : K_vˣ →* Multiplicative ℤ` is the completion valuation on units. Write
`deg t ∈ ℤ` for its additive value. The lemma `coe_unitDegree` identifies it with the
valuation. `unitDegree_surjective` uses `valuedAdicCompletion_surjective`. `unitDegree_eq_one_iff`
says `deg t = 0` exactly when `Valued.v t = 1`. `determinantNorm_eq_one_iff` says that
`|det g| = 1` on `GL_n(K_v)` exactly when `deg(det g) = 0`, using
`completion_determinantNorm_eq_one_iff` and `JacquetLanglands.determinantNorm_eq_padic`.

## The implemented proof

Fix `K`, `v`, `r`, and put `n = r + 1` and `G = GL_n(K_v)`, with the structures of the target.
`K_v` has characteristic zero because `K → K_v` is injective, and `G` is second countable
(`LocalFieldTopology.generalLinear_secondCountableTopology`). Let `ρ` be admissible, irreducible
and square-integrable modulo the centre.

1. *Central character.* Choose a Haar measure on `G / Z` (`exists_isHaarMeasure_centralQuotient`).
   Square-integrability at it supplies a unitary central character of `ρ`. Its character `χ` is
   unitary with open kernel.
2. *Pseudo-coefficient.* Let `ρL` be the universe lift of `ρ` to `ULift V`. It is admissible,
   irreducible and square-integrable and has central character `χ`. The premise, at
   `μ₀ = Measure.haar`, gives `f ∈ C^∞_c(G)` with (a) `IsPseudoCoefficient μ₀ χ ρL _ f`, (b) the
   induced-vanishing clause, (n) `IsDeterminantSliceNormalized χ f`, and (d) a neighbourhood
   `U₀` of `1` on whose regular elliptic elements the orbital integrals of `f` do not vanish.
3. *Test function.* Let `δ = unitDegree v ∘ det : G →* Multiplicative ℤ`. Then `δ g = 1` exactly
   when `|det g| = 1`. So `ker δ` is the kernel of `determinantNorm`, which is open
   (`isOpen_determinantNorm_ker`), and `δ` is continuous (`Weil.continuous_of_open_kernel`).
   Put `φ = ConcordanceLocalization.cutoff _ f`, the product of `f` with the indicator of the
   clopen set `G¹ = δ⁻¹{1}`.
4. *Clause 1.* Let `π` (carrier `W : Type uW`) be irreducible, admissible, unitarizable and
   `ψ`-generic, and let `μ` be a Haar measure with nonzero character of `π` at `φ`.
   - `unitarizableCentralCharacter` gives a unitary central character `ω` of `π`. For central `z`
     with `δ z = 1` we have `δ(z g) = δ(g)`, so (n1) gives `φ(z g) = χ(z)⁻¹ φ(g)`. Then
     `eq_of_distribution_ne_zero_of_leftCovariant` gives `ω(z) = χ(z)`.
   - Choose `a₁ ∈ K_vˣ` with `deg a₁ = 1` and let `s₁ = a₁ · 1`, so `deg(det s₁) = n`. Every central
     element is a scalar `a · 1` (`Matrix.GeneralLinearGroup.center_eq_range_scalar`) with
     `deg(det(a · 1)) = n · deg a`.
   - Take `c'` with `c'^n = χ(s₁)/ω(s₁)` (`IsAlgClosed.exists_pow_nat_eq`); then `|c'| = 1`. Let
     `ζ = exp(2πi/n)`, a primitive `n`-th root of unity. For `k < n` let
     `λ_k(t) = (ζ^k c')^{deg t}`, an unramified unitary character of `K_vˣ`. The kernel of
     `λ_k ∘ det` contains `ker δ`, so it is open, and `g ↦ λ_k(det g)` is locally constant.
   - If `f g ≠ 0` and `deg(det g) = n j`, then `deg(det(s₁^{-j} g)) = 0`, so (n2) gives
     `|det g| = 1`. Hence `sum_weightedTest_eq_smul_cutoff` gives `∑_{k<n} λ_k(det) · f = n · φ`.
   - Let `πL` be the universe lift of `π` to `ULift W`. The character of `πL` at `n φ` is
     nonzero, so for some `k` it is nonzero at `λ_k(det) · f`. By `Character.distribution_twist_weightedTest`, the
     character of `σ = twist (λ_k ∘ det) πL` is nonzero at `f` for `μ`, hence for `μ₀`.
   - `σ` is admissible and irreducible, and generic by `isGeneric_twist_of_isOpen_ker`. Its
     central character is `χ`. At `s₁`, `λ_k(det s₁) ω(s₁) = (ζ^k c')^n ω(s₁) = χ(s₁)`. Every central
     `z` is `z₀ s₁^j` with `δ z₀ = 1`, and then `λ_k(det z) ω(z) = ω(z₀) χ(s₁)^j = χ(z)`.
   - `nonempty_equiv_of_distribution_ne_zero`, applied with the topological data
     `CompletionPadic.topologicalData v` to `ρL`, `χ`, `μ₀` and `f`, gives `σ ≅ ρL`.
   - The character `λ_k⁻¹` is trivial on the units of the completed valuation ring and has
     absolute value one. Twisting by `λ_k⁻¹ ∘ det` gives
     `twist (λ_k⁻¹ ∘ det) ρ ≅ twist (λ_k⁻¹ ∘ det) ρL ≅ twist (λ_k⁻¹ ∘ det) σ = πL ≅ π`. This uses
     `twistEquiv`, `twist_inv_twist` and `equivOfRepresentationEq`.
5. *Clause 2.* `N = interior (U₀ ∩ ker δ)` is a neighbourhood of `1`. By `normNeighbourhood` it
   contains a regular elliptic `γ₀`. Then `U = N ∩ {regular elliptic}` is open by
   `isOpen_regularElliptic`, which needs characteristic zero, and nonempty. Fix `γ ∈ U`.
   - Since `δ γ = 1` and `δ` is invariant under conjugation,
     `ConcordanceLocalization.orbital_cutoff` shows that the orbital integrals of `φ` and `f` at
     `γ` agree.
   - A Haar measure `μ` is `a • μ₀` with `a ≠ 0` (`Measure.haarScalarFactor`). A quotient measure
     `νγ` compatible with `μ` gives `a⁻¹ • νγ`, compatible with `μ₀`.
   - Clause (d) gives a nonzero orbital integral for `a⁻¹ • νγ`, and the orbital integral for
     `νγ` is `a` times it.

## Provenance

This is an internal derivation. The original sources work on a space of functions with one
fixed central character, and they supply the following ingredients.

- Henniart–Lemaire 2011: the pseudo-coefficient of a discrete series with fixed central
  character (II.5.13, with `E = F` and `σ = 1`), the vanishing of its traces on properly induced
  representations (II.5.14, Proposition 2), and the nonvanishing of its orbital integrals at the
  regular elliptic elements near `1` (II.6.7, through the nonzero constant character near `1`).
  In II.6.7–II.6.9 such a pseudo-coefficient is the test function at the distinguished place,
  and a generic unitary local component with nonzero trace is properly induced or a discrete
  series.
- Arthur–Clozel 1989, Chapter 1, Lemma 6.5 and its proof: the use of Kazhdan's compactly
  supported test functions, the genericity of the local components, and elliptic orbital
  integrals that do not vanish identically, in the globalization by the simple trace formula
  with a fixed central character (Lemma 2.4 there).

The restriction of the test function to `|det| = 1`, and the twists by unramified unitary
characters `η ∘ det` that give the tested representation the central character `χ` of `ρ`, are
not taken from these sources. They are the steps "Truncation" and "Discrete series" of the
Library's derivation in the Markdown of `GeneralLinearLocalSelectionTestStatement`, which adapts
the fixed-character arguments to tested representations of arbitrary central character. This
module implements that derivation as follows.

- The premise's pseudo-coefficient `f` is compactly supported on `G`, not only modulo the
  centre, and normalized on determinant slices (`IsDeterminantSliceNormalized`). Clause (n1)
  gives the equality of the two central characters on the scalars with `|det| = 1`
  (`eq_of_distribution_ne_zero_of_leftCovariant`). Clause (n2) makes the sum of the weighted tests
  `λ_k(det) · f` over the `n`-th roots of unity `ζ^k` equal to `n · φ`, as an identity of test
  functions on `G` (`sum_weightedTest_eq_smul_cutoff`). So no integration over the centre is
  needed. The scalar `s₁` of determinant degree `n` and the `n`-th root `c'` determine the
  unramified twists `λ_k`.
- Each twist `σ` is classified directly by the Library's classification of generic
  representations, `Classification.genericSegmentProductExhaustion` (Henniart–Lemaire,
  II.3.2–II.3.3).

No literature assertion is used beyond the premise and the published Library results named
above.

## Sources

- Guy Henniart and Bertrand Lemaire, *Changement de base et induction automorphe pour `GL_n` en
  caractéristique non nulle*, Mém. Soc. Math. Fr. 124 (2011). Retained source
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`, SHA-256
  `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0` (PDF page = printed
  page + 8). II.3.2–II.3.3 (printed p. 79), II.5.13–II.5.14 (printed pp. 113–117) and
  II.6.7–II.6.9 (printed pp. 123–125).
- James Arthur and Laurent Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the
  Trace Formula*, Annals of Mathematics Studies 120 (1989). Retained source
  `arthur-clozel-1989-base-change`, SHA-256
  `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`. Chapter 1, Lemma 2.4
  (printed pp. 12–13) and Lemma 6.5 with its proof (printed pp. 54–55).
