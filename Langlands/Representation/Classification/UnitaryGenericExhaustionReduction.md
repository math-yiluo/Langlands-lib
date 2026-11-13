# Unitary generic exhaustion from generic-free Tadić exhaustion

Author: Worker 4941. Derived conditional reduction for Task 4941
(`31c91f66-6a4d-4571-9898-e0a37589a58b`). Module
`Langlands.Representation.Classification.UnitaryGenericExhaustionReduction`,
namespace `Langlands.Classification`. No axioms beyond `propext`,
`Classical.choice` and `Quot.sound`, and no `sorry`.

The module proves the published proposition `UnitaryGenericExhaustion F T`
from one remaining hypothesis, the published generic-free exhaustion
`TadicUnitaryDualExhaustion F T` (Tadić 1986, Theorem D(ii)). That hypothesis
is the target of the separate proof task Task 4988
(`3fcabfac-7cbc-4d66-90b2-40b466df00f2`); this module does not prove it. The
classification input that the elimination of higher Speh factors needs is
discharged by the proved `squareIntegrableLanglandsClassification`.

Fix an arbitrary prime `p`, `F : PadicField.{uF} p` and compatible topology
`T`. The field and representation universes are independent, and every
representation has its actual carrier in `Type (max uF uV)`. All products are
the existing normalized standard upper-block inductions.

## Declarations

- `nonempty_unitaryParameterRealization_of_isTadicBuildingBlock`. Assume
  `OrderedMultisegmentHeadClassification F T`, a unitary additive character
  `ψ`, and an actual Tadić building block `σ` of rank `n` with a nonzero
  functional for the entrywise upper character of `ψ`. Then `σ` has an actual
  `UnitaryParameterRealization`. The two cases of `IsTadicBuildingBlock` are
  treated separately; in each, the rank equality is eliminated by `subst`.
  - Speh case: `σ` is isomorphic to a Speh representation `S` of a datum `d`.
    The functional transfers to `S` along the isomorphism
    (`Whittaker.hasFunctional_iff_of_equiv`). `SpehDatum.length_eq_one_of_hasFunctional`
    gives `d.length = 1`, and `lengthOneSpehParameterRealization` gives a
    one-block realization of `S` with exponent zero, pulled back to `σ` by
    `UnitaryParameterRealization.ofIso`.
  - Complementary case: `σ` is isomorphic to `d.complementaryInduced S α`
    with `0 < α < 1/2`. The functional transfers to this product, and
    `SpehDatum.hasFunctional_complementaryInduced_iff` transfers it to `S`.
    Again `d.length = 1`, and `lengthOneComplementaryParameterRealization`
    gives the two-block realization with exponents `α` and `-α`, pulled back
    to `σ`.
- `unitaryGenericParameterRealizationOfTadic`. Assume `TadicUnitaryDualExhaustion`
  and `OrderedMultisegmentHeadClassification`. For a representation `π` of
  `GL_(n+1)` that is generic for `ψ` and unitarizable, choose an actual
  realization. Irreducibility (the first component of `Whittaker.IsGeneric`)
  and unitarizability give a Tadić factorization `π ≅ ∏ σ i` over a block
  shape `B`. The standard character equals the entrywise character
  (`Whittaker.entrywiseCharacter_eq_standardCharacter`), so the Whittaker
  functional of `π` transfers to the product and, by the finite-product
  criterion `Whittaker.hasFunctional_finiteProduct_iff`, to every factor
  `σ i`. The previous lemma realizes each factor; `UnitaryParameterRealization.product`
  assembles these into a realization of the product, and `ofIso` pulls it back
  to `π`.
- `unitaryGenericExhaustion_of_tadic`: the same two hypotheses imply
  `UnitaryGenericExhaustion F T`. `UnitaryParameterRealization.exists_datum`
  turns the chosen realization into the existential statement: a block shape,
  actual blocks, real exponents, `IsUnitaryGenericDatum` (irreducible,
  unitarizable, analytically square-integrable blocks, strict bounds
  `-1/2 < s i < 1/2`, multiplicity-preserving Hermitian symmetry with actual
  rank-transported block isomorphisms) and an isomorphism of `π` with the
  entire `T.twistedProductInduced B δ s`.
- `unitaryGenericExhaustion_of_tadic_of_squareIntegrable` replaces the
  ordered-head hypothesis by `SquareIntegrableLanglandsClassification`, using
  the published reduction `orderedMultisegmentHeadClassification_of_squareIntegrable`
  and the proved `segmentSpecialParameterUniqueness`.
- `unitaryGenericExhaustion_of_tadicUnitaryDualExhaustion`: only
  `TadicUnitaryDualExhaustion F T` remains; the classification is the proved
  `squareIntegrableLanglandsClassification`.

## Correspondence with the sources

Henniart 2000, Appendix A.2 (printed p.453), derives the description of
unitary generic representations from Tadić's classification: Tadić 1986,
Theorem D(ii) (printed pp.338–339) writes every irreducible unitary
representation as a product of Speh representations `u(δ, k)` and
complementary series `π(u(δ, k), α)` with `0 < α < 1/2`. Genericity of the
product forces genericity of every factor (Bernstein–Zelevinsky 1977
§§4.5–4.7; here the finite-product Whittaker criterion), and a generic Speh
representation has `k = 1` (Zelevinsky 1980, Theorem 9.7 and §9.10; here
`SpehDatum.length_eq_one_of_hasFunctional`). With `k = 1` the factors are
`δ` and `δν^α × δν^(-α)`, which are exactly the one- and two-block valid
parameter families. The Lean proof follows this route; Tadić's theorem enters
only through the hypothesis `TadicUnitaryDualExhaustion`.
