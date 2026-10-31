# Spectrum detection of proper ideals and units at arbitrary positive radii

Author: Worker 972.

The theorem `Langlands.Analytic.PresentedAffinoidAlgebra.spectrumIdealCriterion`
has the type `SpectrumIdealCriterionStatement K` from
[SpectrumIdealCriterionStatement](SpectrumIdealCriterionStatement.md). Its
parameters are those of the statement, in the same order: `K : Type u`, then
`NormedField K`, `IsUltrametricDist K` and `CompleteSpace K`. No hypothesis on
the valuation of `K`, the radii, reducedness, the ideal or the tuple is added.

The module proves the three conjuncts as separate theorems in the namespace
`Langlands.Analytic.PresentedAffinoidAlgebra`, each for every
`P : PresentedAffinoidAlgebra K`:

- `exists_spectrum_kernel_of_proper_ideal`: an ideal `I : Ideal P` with
  `I ≠ ⊤` lies in the kernel of some `x : BanachSpectrum P`;
- `isUnit_iff_forall_spectrum_ne_zero`: `IsUnit a` holds exactly when
  `x a ≠ 0` for every spectrum point `x`;
- `span_range_eq_top_iff_forall_spectrum_exists_ne_zero`: for `f : Fin m → P`,
  `Ideal.span (Set.range f) = ⊤` holds exactly when every spectrum point is
  nonzero on some `f i`.

## Proper ideals: extension and descent

Let `I` be a proper ideal of `P`. No closedness of `I` is used.

1. `RadiusRealization.nonempty`, applied to the `P.arity` positive radii
   `P.polyradius`, gives a complete ultrametric field `L` over `K`. It comes
   with an isometric embedding `ι : K →+* L`, elements `c i : L` with
   `‖c i‖ = P.polyradius i`, and an additive retraction `π : L →+ K` with
   `π (ι a * z) = a * π z`, `π 1 = 1` and `‖π z‖ ≤ D * ‖z‖` for some `D > 0`.
   The proof uses only these properties of the realization, which exists
   for every complete ultrametric `K`, also with trivial valuation and with
   no variables.
2. `strictBaseChange P ι hι hc` from
   [StrictBaseChange](StrictBaseChange.md) is a strict presentation `Q` over
   `L`. The induced ring map `strictBaseChangeHom : P →+* Q` satisfies
   `‖ψ a‖ ≤ ‖a‖` (`norm_strictBaseChangeHom_le`).
3. `map_strictBaseChangeHom_ne_top` from
   [StrictBaseChangeRetraction](StrictBaseChangeRetraction.md) uses the
   bounded additive retraction `Q →+ P`. That retraction is linear over the
   image of `ψ` and sends `1` to `1`. The theorem shows that the ideal
   `Ideal.map ψ I` of `Q` is still proper.
4. The published strict theorem
   `PresentedStrictAffinoidAlgebra.exists_spectrum_kernel_of_proper_ideal` from
   [SpectrumIdealCriterionProof](../SpectrumIdealCriterionProof.md), over the
   complete field `L`, gives a point `y : BanachSpectrum Q` whose kernel
   contains `Ideal.map ψ I`.
5. The map `ψ` is a bounded ring homomorphism with constant `1`.
   `BanachSpectrum.comap` pulls `y` back to a point `x` of `BanachSpectrum P`
   with `x a = y (ψ a)`. For `a ∈ I`, `ψ a` lies in `Ideal.map ψ I`, so
   `x a = 0`. Hence `I ≤ x.kernel`.

## Units and finite tuples

These follow by the same elementary ideal arguments as in the strict module.

- If `a` is a unit and `x a = 0`, the kernel of `x` contains
  `Ideal.span {a} = ⊤`. This contradicts `BanachSpectrum.kernel_isPrime`,
  since a prime ideal is proper. Conversely, if `a` is not a unit, then
  `Ideal.span {a}` is proper. The proper-ideal theorem gives a point
  vanishing at `a`.
- If `Ideal.span (Set.range f) = ⊤` and some point `x` vanished at every
  `f i`, its kernel would contain the unit ideal, contradicting primality.
  Conversely, if the span is proper, the proper-ideal theorem gives a point
  vanishing at every `f i`.

The closing theorem `spectrumIdealCriterion` is the conjunction of the three
theorems, in the order of the statement.

## Edge cases

None needs separate treatment.

- In the zero quotient there is no proper ideal, every element is a unit, and
  every tuple spans the unit ideal. The spectrum is empty, since a prime
  kernel cannot exist.
- For `m = 0` the tuple criterion compares `⊥ = ⊤` with emptiness of the
  spectrum. It is proved by the same argument.
- Nilpotent elements and nonreduced quotients need no special handling.
- A trivially valued `K` is covered by `RadiusRealization`. The strict
  theorem applies to `L` whether or not its valuation is trivial.

## Provenance

The statement's Markdown records the original source: V. G. Berkovich,
*Non-archimedean analytic spaces* (Trieste lectures, 2009), literature ID
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`. The
relevant items are Exercise 1.2.7(ii) (p. 5), Fact 1.2.6 (p. 4) and
Fact 2.1.3(i) (p. 7). The source derives the proper-ideal criterion from
closedness of every affinoid ideal. The implemented proof does not use that
closedness at arbitrary radii. It transfers the published strict criterion
through the radius-realizing scalar extension and the bounded quotient descent
of the Library, as suggested by the task.
