# Reduction of the VII.2.4 Proposition to its two steps

Renard 2026, VII.2.4, Proposition (printed p.229 / PDF p.235): for a parabolic
`P = MN` of `G`, a tempered representation `(σ, E)` of `M` and a tempered
representation `(π, V)` of `G`, there is a natural isomorphism
`Hom_G(V, i_P^G E) ≃ Hom_M((r_P^G V)_0, E)`. The source proof is one sentence: the
result is the conjunction of Frobenius reciprocity VI.1.1 and Lemma III.1.10.

The Library states the two steps separately:

- `LeviFrobeniusReciprocityStatement` (VI.1.2 adjunction) is the linear bijection
  `Hom_G(π, i_P^G σ) ≃ Hom_M(r_P^G π, σ)` sending `F` to `[x] ↦ (F x)(1)`. Carrier
  universes are independent.
- `TemperedJacquetUnitaryRestrictionStatement` says that precomposition with
  `leviUnitaryJacquetModuleι` is a bijection
  `(r_P^G π ⟶ σ) → ((r_P^G π)_0 ⟶ σ)` for tempered `π` and `σ`. Here `π` and `σ`
  have one carrier universe.

The target `TemperedInductionUnitaryReciprocityStatement` has independent carrier
universes `w` for `π` and `v` for `σ`. This module proves the target from the two
statements. The restriction step is used at the carrier universe `max v w`, through
universe lifts. The module proves neither step. It is a supporting development for
the VII.2.4 proof task, and the module does not assert the target outright.

## Declarations

- `intertwiningMapCongr e₁ e₂` is the bijection `f ↦ e₂ ∘ f ∘ e₁⁻¹` between
  intertwiner spaces. It is given by representation equivalences `e₁` of the
  sources and `e₂` of the targets, possibly between different carrier universes.
- `jacquetEquivOfEquiv` is the published `normalizedJacquetRepresentationEquiv`
  (from `CasselmanUniverseLift`) instantiated at the literal radical and Levi
  images of an actual represented parabolic. A representation equivalence
  `π ≃ π'` gives an equivalence of the actual normalized Jacquet modules over
  `pointImage (l ≫ p)`. `leviJacquetEquivOfEquiv` is the same linear equivalence
  for the Jacquet modules transported to `M(F)` along `leviPointsEquiv`.
- `isNormalizedJacquetExponent_iff_of_equiv`: equivalent representations have the
  same normalized Jacquet exponents. Through `isNormalizedJacquetExponent_iff`,
  both sides are generalized eigencharacters of the Jacquet action restricted
  along `splitComponentPointsMap`. The Jacquet equivalence is also an equivalence
  of these restricted actions, so `isGeneralizedEigencharacter_iff_of_equiv`
  applies.
- `mapsTo_unitaryJacquetPart`: every intertwiner between the actual Jacquet modules
  of two representations, over the literal Levi image, maps `(r_P^G π)_0` into
  `(r_P^G π')_0`. By `unitaryJacquetPart_eq_iSup`, the unitary part is the
  supremum of the weight spaces with zero normalized real part. Each weight space
  is preserved by `map_mem_generalizedWeightSpace`, and
  `Langlands.Subrepresentation.mapsTo_iSup` passes this to the supremum.
- `unitaryJacquetPart_map_jacquetEquivOfEquiv`: the Jacquet equivalence maps the
  unitary part onto the unitary part. One inclusion is the previous lemma for the
  equivalence; the other is the previous lemma for its inverse.
- `leviUnitaryJacquetModuleEquivOfEquiv` restricts the Jacquet equivalence to an
  equivalence of the published `leviUnitaryJacquetModule`s, using
  `LinearEquiv.ofSubmodules`.
- `leviUnitaryRestriction π σ` is the linear map
  `Hom(r_P^G π, σ) → Hom((r_P^G π)_0, σ)`, `f ↦ f ∘ leviUnitaryJacquetModuleι`, on
  actual intertwiner spaces. It does not require the carrier universes of `π` and
  `σ` to agree.
- `leviUnitaryRestriction_bijective_of_equiv`: bijectivity of this restriction for
  `(π', σ')` gives bijectivity for `(π, σ)`, when `π ≃ π'` and `σ ≃ σ'`. Conjugating
  by the two equivalences commutes with restriction. The check is pointwise and
  holds definitionally, because the unitary-module equivalence is the Jacquet
  equivalence on underlying vectors. Then `Equiv.comp_bijective` gives the result.
- `leviUnitaryRestriction_bijective_iff`: for one carrier universe, bijectivity of
  `leviUnitaryRestriction` is bijectivity of the categorical precomposition map in
  `TemperedJacquetUnitaryRestrictionStatement`. In the category `SmoothRep`, hom
  sets are identified with intertwiner spaces by `SmoothRep.hom` and
  `SmoothRep.ofHom`. Under this identification, precomposition with `ι` is
  composition with `SmoothRep.hom ι`, by `rfl`.
- `isNormalizedExponentTempered_of_equiv`: normalized-exponent temperedness
  (`IsNormalizedExponentTempered`) is invariant under representation equivalences,
  across carrier universes. Admissibility transfers by `isAdmissible_iff_of_equiv`.
  The cone condition keeps its presentation-existence part unchanged. Its
  exponent hypothesis is pulled back by
  `isNormalizedJacquetExponent_iff_of_equiv`.
- `temperedInductionUnitaryReciprocity_of`: assuming
  `LeviFrobeniusReciprocityStatement.{u, v, w}` and
  `TemperedJacquetUnitaryRestrictionStatement.{u, max v w}`, the target
  `TemperedInductionUnitaryReciprocityStatement.{u, v, w}` holds.

## Proof of the conditional assembly

Fix the data of the target and tempered `π : SmoothRep.{0, u, w}` and
`σ : SmoothRep.{0, u, v}`. Frobenius reciprocity gives `e₁` with
`e₁ F [x] = (F x)(1)`. Lift `π` and `σ` to `π' = SmoothRep.universeLift.{v} π` and
`σ' = SmoothRep.universeLift.{w} σ`, both with carriers in `Type (max v w)`. The
published `SmoothRep.universeLiftEquiv` identifies each lift with its original.
Both lifts are tempered by `isNormalizedExponentTempered_of_equiv`. The restriction
statement at universe `max v w`, followed by `leviUnitaryRestriction_bijective_iff`,
makes restriction bijective for `(π', σ')`. Then
`leviUnitaryRestriction_bijective_of_equiv` makes it bijective for `(π, σ)`. The
required equivalence is `e₁` followed by `LinearEquiv.ofBijective` of the
restriction. For `y` in the unitary part with `ι y = [x]`, its value at `F` is
`e₁ F (ι y) = e₁ F [x] = (F x)(1)`.

The assembly keeps every quantifier and datum of the target. It uses no hypothesis
beyond the two statements: no standardness, finite length, irreducibility,
unimodularity, presentation existence, quotient compactness or Iwahori contraction.

## Relation to the source

Renard composes the two isomorphisms directly. The only addition here is the carrier
transport. It is needed because the Library's restriction statement is stated for a
single carrier universe. Everything transported (Jacquet modules, unitary parts,
exponents, temperedness) is the published actual object. The comparison maps are
the published universe-lift equivalences and the published Jacquet equivalence
`normalizedJacquetRepresentationEquiv`. This is a derived, internal development;
its only source content is the one-line composition in Renard VII.2.4.
