# Second adjointness from explicit structure statements

Author: Worker 1402. Lean module
`Langlands.Representation.Exponents.LeviSecondAdjointnessStructure`. The first lemma is in
namespace `Langlands.Aubert.General`, the others in
`Langlands.Aubert.General.RepresentedParabolic`.

## Source

Renard 2026, *Représentations des groupes réductifs p-adiques*, VI.9.6, first Theorem
(VI.9.6.1) (printed p.201, PDF p.207; the proof is on printed pp.201–202, PDF pp.207–208):
`r_{P̄}^G` is right adjoint to `i_P^G`. The source ID is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

`LeviSecondAdjointnessStatement` states this for arbitrary represented parabolics `P = MN`
and `P̄ = MN̄`. It describes `P̄` only through the common Levi embedding
`mbar ≫ pbar = m ≫ p` and through rational points: `P(k) ∩ P̄(k) = M(k)`. This module applies
the general second adjointness theorem `nonempty_secondAdjunction_of_stableLift`
(`Aubert/General/SecondAdjointnessCell.lean`) to point images. It gets the Casselman
isomorphism `Ψ` from `exists_isStableLiftDuality_of_dynamic`
(`Exponents/LeviJacquetContragredientDynamic.lean`) and the duality `C` from
`exists_isNaturalIntegralDuality_of_compactSpace`
(`Aubert/General/CompactQuotientNaturalDuality.lean`). The passage from parabolics to
cocharacters is the one in `leviJacquetContragredient_of_structure`
(`Exponents/LeviJacquetContragredientStructure.lean`).

Notation on rational points:
`N(χ) = (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _))`,
`M(χ) = (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _))` and
`N(χ⁻¹) = (Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _))`.

## Open inputs

The last four theorems assume some of the following Library statements. When this was last
checked (Library commit 6f75b7b3), only the second one was proved in the Library:

- `ParabolicDynamicStatement` (`GroupScheme/Absolute/BorelStatement.lean`);
- `OppositeDynamicParabolicUniquenessStatement`
  (`GroupScheme/Dynamic/OppositeParabolicUniquenessStatement.lean`). It is proved as
  `Langlands.GroupScheme.oppositeDynamicParabolicUniqueness`
  (`GroupScheme/Dynamic/OppositeParabolicUniquenessProof.lean`), but the theorems here still
  take it as a hypothesis, as the published `LeviSecondAdjointnessFromInputsStatement` does;
- `RationalPointFamily.UniformCompressionStabilizationStatement` (the Proposition of VI.9.1,
  `Exponents/UniformCompressionStabilizationStatement.lean`), at universes `.{u, max u v}`;
- `Dynamic.LeviAdjointDeterminantReciprocityStatement`, or instead
  `RelativeRootReflectionExistenceStatement` together with
  `CentralSplitTorusCharacterStatement`;
- `RationalPointFamily.RationalReductiveUnimodularityStatement`
  (`Aubert/General/RationalReductiveUnimodularityStatement.lean`) together with
  `StandardCocharacterStatement` (`GroupScheme/Rational/StandardCocharacterStatement.lean`);
- `ArbitraryParabolicQuotientCompactStatement`
  (`Exponents/ArbitraryParabolicQuotientCompactStatement.lean`).

So the module does not prove `LeviSecondAdjointnessStatement`. It derives it from these
statements.

The passage from parabolics to cocharacters also uses
`DynamicGeometricUnipotentRadicalStatement`
(`GroupScheme/Dynamic/GeometricUnipotentRadicalStatement.lean`). This one is proved in the
Library, as `Langlands.GroupScheme.dynamicGeometricUnipotentRadical`
(`GroupScheme/Dynamic/GeometricUnipotentRadicalProof.lean`), and the proofs pass that theorem
directly. It is not a hypothesis of any theorem here.

The stabilization statement is needed at `.{u, max u v}`. The reason is that
`LeviSecondAdjointnessStatement.{u, v}` is about carriers in `Type (max u v)`, and
`exists_isStableLiftDuality_of_dynamic` builds `Ψ` for carriers in the second universe of
its stabilization hypothesis.

## Declarations

### `IsSemidirectDecomposition.eq_one_of_inf_eq`

Let `P`, `P̄`, `M` and `O` be subgroups of a group, with `P̄ = M ⋉ O`
(`IsSemidirectDecomposition P̄ M O`) and `P ⊓ P̄ = M`. If `x ∈ P` and `x ∈ O`, then `x = 1`.

Proof. Since `O ≤ P̄`, `x ∈ P ⊓ P̄ = M`. The Levi projection of `P̄` sends `x` to itself
because `x ∈ M`, and to `1` because `x ∈ O`. So `x = 1`.

### `nonempty_leviSecondAdjunction_of_dynamic`

The setting is that of `LeviSecondAdjointnessStatement` for one pair of parabolics. There
is a Hausdorff nonarchimedean local field `k` and a group scheme `G` over `k` with affine
structure map. `G(k)` carries the Library point topology and is assumed locally compact and
nonarchimedean. `G` is connected reductive. `P = MN` and `P̄ = MN̄` are represented
parabolics with Levi decompositions, `mbar ≫ pbar = m ≫ p` and
`pointImage p ⊓ pointImage pbar = pointImage (m ≫ p)`. The other hypotheses are:

- `UniformCompressionStabilizationStatement.{u, max u v}`;
- a cocharacter `χ` with `pointImage (n ≫ p) = N(χ)`, `pointImage (m ≫ p) = M(χ)` and
  `pointImage (nbar ≫ pbar) = N(χ⁻¹)`;
- reciprocity of Haar moduli: for every `x ∈ M(k)`, the Haar modulus of conjugation by `x`
  on `N̄(k)` times that on `N(k)` is `1`;
- `P(k) \ G(k)` is compact (`CompactSpace (Induction.LeftQuotient (pointImage p))`);
- `G(k)` is unimodular: `Measure.modularCharacter g = 1` for every `g`;
- the modular character of `P(k)` is the Haar modulus of conjugation on `N(k)`, restricted
  to `P(k)` (`HaarModulus.closedRestrictCharacter`).

Then `leviInductionFunctor.{u, max u v} p m n …` is left adjoint to
`leviJacquetFunctor.{u, max u v} pbar mbar nbar …`.

Proof.

1. `nonempty_leviSecondAdjunction_of_pointImage`
   (`Exponents/LeviSecondAdjointnessTransport.lean`) reduces the claim to an adjunction
   between induction from `P(k) = M(k) ⋉ N(k)` and the normalized Jacquet functor of
   `N̄(k) = pointImage (nbar ≫ pbar)` with Levi `pointImage (m ≫ p)`.
2. Give `G(k)` the Borel σ-algebra. It is Hausdorff by `rationalPoint_t2Space`. `P(k)` is
   closed, hence locally compact. `isSemidirectDecomposition_pointImage` gives
   `P(k) = M(k) ⋉ N(k)`, and `continuous_projection_pointImage` the continuity of its Levi
   projection. The same lemma for `pbar`, rewritten with `mbar ≫ pbar = m ≫ p`, gives
   `P̄(k) = M(k) ⋉ N̄(k)`.
3. `exists_isStableLiftDuality_of_dynamic`, with its `U`, `M`, `O` taken to be `N̄(k)`,
   `M(k)`, `N(k)`, gives an element `g` with a basis of opposite Iwahori contractions and a
   natural isomorphism `Ψ : r_{N̄}(π~) ≅ (r_N π)~` with the stable-lift property
   `IsStableLiftDuality`.
4. `exists_isNaturalIntegralDuality_of_compactSpace` gives a measure on `⊤ : Subgroup G(k)`
   and a natural isomorphism `C : (i_P τ)~ ≅ i_P(τ~)` given by the integral of the
   coefficient pairing. Its inputs are compactness of `P(k) \ G(k)`, unimodularity of
   `G(k)` and the modular character of `P(k)`.
5. `nonempty_secondAdjunction_of_stableLift` concludes. Its remaining inputs are:
   unimodularity of `N(k)` (`isUnimodularModulus_pointImage_radical`); `P(k) ∩ N̄(k) = 1`,
   by `IsSemidirectDecomposition.eq_one_of_inf_eq` for `P̄(k) = M(k) ⋉ N̄(k)`; and exactness of
   `r_{N̄}` (`jacquetFunctor_map_isShortExact`, using the compact open subgroups of `N̄(k)`
   from `isLimitOfCompactSubgroups_pointImage_radical`).

### `nonempty_leviSecondAdjunction_of_structure`

The same setting and conclusion. The cocharacter, Haar reciprocity, compactness,
unimodularity and modular character hypotheses are replaced by the statements
`ParabolicDynamicStatement`, `OppositeDynamicParabolicUniquenessStatement`,
`Dynamic.LeviAdjointDeterminantReciprocityStatement`,
`RationalReductiveUnimodularityStatement`, `StandardCocharacterStatement` and
`ArbitraryParabolicQuotientCompactStatement`.

Proof. `DynamicLeviConjugacy.exists_cocharacter_parabolic_levi` for `p` and `m`, with
`ParabolicDynamicStatement` and the proved `dynamicGeometricUnipotentRadical`, gives `χ`
with `range p = Dynamic.parabolic χ` and `range (m ≫ p) = Dynamic.centralizer χ`. The three
point image identities come from `pointImage_radical_eq_dynamic`,
`pointImage_eq_range_carrier` and `pointImage_opposite_radical_eq_dynamic`, as in
`nonempty_leviJacquetContragredient_iso_of_structure`. Haar reciprocity is
`dynamicOppositeHaarReciprocity_of_leviAdjoint`
(`Aubert/General/DynamicOppositeHaarReciprocity.lean`). Compactness of `P(k) \ G(k)` is
`ArbitraryParabolicQuotientCompactStatement`. Unimodularity of `G(k)` is
`rationalPoints_modularCharacter_eq_one`, and the modular character of `P(k)` is
`modularCharacter_pointImage_of_unimodularity` (both in
`Exponents/LeviParabolicModulus.lean`, by Worker 937). Then apply
`nonempty_leviSecondAdjunction_of_dynamic`.

### `leviSecondAdjointness_of_structure`

`LeviSecondAdjointnessStatement.{u, v}` holds if `ParabolicDynamicStatement`,
`OppositeDynamicParabolicUniquenessStatement`,
`UniformCompressionStabilizationStatement.{u, max u v}`,
`Dynamic.LeviAdjointDeterminantReciprocityStatement`,
`RationalReductiveUnimodularityStatement`, `StandardCocharacterStatement` and
`ArbitraryParabolicQuotientCompactStatement` hold.

Proof. Introduce the binders of the statement. The affine structure map comes from
`IsConnectedReductive.isAffineHom`, and the point topology is the one fixed by the statement.
Then apply `nonempty_leviSecondAdjunction_of_structure`. The axioms used are `propext`,
`Classical.choice` and `Quot.sound`.

### `leviSecondAdjointness_of_structure_of_reflection_centralSplitTorus`

The same conclusion with `Dynamic.LeviAdjointDeterminantReciprocityStatement` replaced by
`RelativeRootReflectionExistenceStatement` and `CentralSplitTorusCharacterStatement`.

Proof. `leviAdjointDeterminantReciprocity_of_structure`
(`GroupScheme/Dynamic/LeviAdjointDeterminantReciprocityReduction.lean`) gives the
reciprocity statement from these two statements and the proved `dynamicCentralizerReductive`.
Then apply `leviSecondAdjointness_of_structure`.

## Provenance of the derived content

Renard deduces (VI.9.6.1) from the chain (VI.9.6.3), built from the duality
`(i_P τ)~ ≅ i_P(τ~)` (III.2.7), Frobenius reciprocity and (VI.9.6.2), and says the
resulting bijection is natural. The general theorem follows that chain. In place of the
naturality claim it uses a per-object condition on the unit of the chain, proved with
open-cell functions (see `SecondAdjointnessCell.md`). This module adds no new mathematics.
It only rewrites the hypotheses of `LeviSecondAdjointnessStatement` into the form of the
general theorem. Two inputs are derived rather than taken from the source. `P(k) ∩ N̄(k) = 1`
is derived from the statement's opposition hypothesis `P(k) ∩ P̄(k) = M(k)`. The identification `N̄(k) = N(χ⁻¹)` is on
rational points only, because the statement's opposition hypothesis is on rational points
and the Jacquet functors use only point images.
