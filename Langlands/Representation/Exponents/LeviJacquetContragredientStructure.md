# Jacquet modules of contragredients from explicit structure statements

Author: Worker 937. Lean module
`Langlands.Representation.Exponents.LeviJacquetContragredientStructure`, namespace
`Langlands.Aubert.General.RepresentedParabolic`.

## Source

Renard 2026, *Représentations des groupes réductifs p-adiques*, VI.9.6, second Theorem
(VI.9.6.2) (printed p.201, PDF p.207): `r_{P̄}^G(π~) ≅ (r_P^G π)~` for every smooth `π`. The
source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

`LeviJacquetContragredientStatement` states this for arbitrary represented parabolics
`P = MN` and `P̄ = MN̄`. It describes `P̄` only through the common Levi embedding
`mbar ≫ pbar = m ≫ p` and through rational points: `P(k) ∩ P̄(k) = M(k)`. This module reduces
the statement to the dynamic case
`nonempty_leviJacquetContragredient_iso_of_dynamic_of_leviAdjoint`
(`Exponents/LeviJacquetContragredientReciprocity.lean`), where `N`, `M` and `N̄` have point
images `N(χ)`, `M(χ)` and `N(χ⁻¹)` for one cocharacter `χ`. Renard takes the opposite
parabolic as given with its Levi. The identification `N̄(k) = N(χ⁻¹)(k)` is the uniqueness
of the opposite parabolic containing a given Levi, Borel–Tits 1965, 4.8 and 4.10. In the
Library it is the statement `OppositeDynamicParabolicUniquenessStatement`
(`GroupScheme/Dynamic/OppositeParabolicUniquenessStatement.lean`).

Notation on rational points:
`N(χ) = (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _))`,
`M(χ) = (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _))` and
`N(χ⁻¹) = (Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _))`.

## Open inputs

Every result here assumes some of the following Library statements. None of them was proved
in the Library (commit 6f182f92) when this was last checked:

- `ParabolicDynamicStatement` (`GroupScheme/Absolute/BorelStatement.lean`; rational
  parabolics are dynamic parabolics);
- `OppositeDynamicParabolicUniquenessStatement`
  (`GroupScheme/Dynamic/OppositeParabolicUniquenessStatement.lean`);
- `RationalPointFamily.UniformCompressionStabilizationStatement` (the Proposition of
  VI.9.1, `Exponents/UniformCompressionStabilizationStatement.lean`);
- `Dynamic.LeviAdjointDeterminantReciprocityStatement`, or instead
  `RelativeRootReflectionExistenceStatement` together with
  `CentralSplitTorusCharacterStatement`.

So the module does not prove `LeviJacquetContragredientStatement`. It derives it from these
statements.

The module also uses `DynamicGeometricUnipotentRadicalStatement`
(`GroupScheme/Dynamic/GeometricUnipotentRadicalStatement.lean`): the identity-limit subgroup of
a cocharacter is the geometric unipotent radical of its dynamic parabolic. This one is proved
in the Library, as `Langlands.GroupScheme.dynamicGeometricUnipotentRadical`
(`GroupScheme/Dynamic/GeometricUnipotentRadicalProof.lean`), and the proofs below pass that
theorem directly. It is not a hypothesis of any result here.

## Declarations

### `pointImage_opposite_radical_eq_dynamic`

The field `k` is arbitrary and `G` is connected reductive. Assume `ParabolicDynamicStatement`
and `OppositeDynamicParabolicUniquenessStatement`. Let `χ` be a cocharacter and `p : P ⟶ G`,
`m : M ⟶ P` with `range p = Dynamic.parabolic χ` and `range (m ≫ p) = Dynamic.centralizer χ`.
Let `P̄ = M N̄` be a represented parabolic, `pbar : P̄ ⟶ G` parabolic, `mbar : M ⟶ P̄` a
rational Levi and `nbar : N̄ ⟶ P̄` a geometric unipotent radical. Assume
`mbar ≫ pbar = m ≫ p` and `pointImage p ⊓ pointImage pbar = pointImage (m ≫ p)`. Then
`pointImage (nbar ≫ pbar) = N(χ⁻¹)`.

Proof. `DynamicLeviConjugacy.exists_cocharacter_parabolic_levi`
(`GroupScheme/Rational/ParabolicLeviRealization.lean`) applied to `pbar` and `mbar`, with
`ParabolicDynamicStatement` and the proved `dynamicGeometricUnipotentRadical`, gives a
cocharacter `χ'` with `range pbar = Dynamic.parabolic χ'` and
`range (mbar ≫ pbar) = Dynamic.centralizer χ'`. Since `mbar ≫ pbar = m ≫ p`, this gives
`Dynamic.centralizer χ' = Dynamic.centralizer χ`. `pointImage_eq_range_carrier` rewrites the
hypothesis on point images as
`P(χ)(k) ∩ P(χ')(k) = Z(χ)(k)`. `OppositeDynamicParabolicUniquenessStatement` then gives
`Dynamic.unipotent χ' = Dynamic.unipotent (Dynamic.oppositeCocharacter χ)`. Finally
`pointImage_radical_eq_dynamic`
(`Exponents/ArbitraryParabolicJacquetAdmissibilityReduction.lean`), again with
`dynamicGeometricUnipotentRadical`, identifies `pointImage (nbar ≫ pbar)` with `N(χ')`. The
last step is `rfl`, because `Dynamic.oppositeCocharacter` and `Dynamic.inverseCocharacter`
have the same body.

### `nonempty_leviJacquetContragredient_iso_of_structure`

The setting of `LeviJacquetContragredientStatement` for one pair of parabolics. There is a
Hausdorff nonarchimedean local field `k` and a group scheme `G` over `k` with affine structure
map. `G(k)` carries the Library point topology and is assumed locally compact and
nonarchimedean. Assume the first three open inputs,
`Dynamic.LeviAdjointDeterminantReciprocityStatement` and that `G` is connected reductive. Let
`P = MN` and `P̄ = MN̄` be represented parabolics with Levi decompositions,
`mbar ≫ pbar = m ≫ p` and `pointImage p ⊓ pointImage pbar = pointImage (m ≫ p)`. Then there
is a natural isomorphism `r_{P̄}^G(π~) ≅ (r_P^G π)~`: the functors
`SmoothRep.contragredientFunctor ⋙ leviJacquetFunctor pbar mbar nbar …` and
`(leviJacquetFunctor p m n …).op ⋙ SmoothRep.contragredientFunctor` are isomorphic.

Proof. `exists_cocharacter_parabolic_levi` for `p` and `m` gives `χ` with
`range p = Dynamic.parabolic χ` and `range (m ≫ p) = Dynamic.centralizer χ`. The theorem then
applies `nonempty_leviJacquetContragredient_iso_of_dynamic_of_leviAdjoint` with three point
image identities:

- `pointImage (n ≫ p) = N(χ)`, by `pointImage_radical_eq_dynamic`;
- `pointImage (m ≫ p) = M(χ)`, by `pointImage_eq_range_carrier` and the equality for
  `m ≫ p`;
- `pointImage (nbar ≫ pbar) = N(χ⁻¹)`, by `pointImage_opposite_radical_eq_dynamic`.

### `leviJacquetContragredient_of_structure`

`LeviJacquetContragredientStatement.{u, v}` holds if `ParabolicDynamicStatement`,
`OppositeDynamicParabolicUniquenessStatement`, `UniformCompressionStabilizationStatement.{u, v}`
and
`Dynamic.LeviAdjointDeterminantReciprocityStatement` hold.

Proof. Introduce the binders of the statement. The affine structure map comes from
`IsConnectedReductive.isAffineHom`, and the point topology is the one fixed by the statement.
Then apply `nonempty_leviJacquetContragredient_iso_of_structure`.

### `leviJacquetContragredient_of_structure_of_reflection_centralSplitTorus`

The same conclusion with `Dynamic.LeviAdjointDeterminantReciprocityStatement` replaced by
`RelativeRootReflectionExistenceStatement` and `CentralSplitTorusCharacterStatement`.

Proof. `leviAdjointDeterminantReciprocity_of_structure`
(`GroupScheme/Dynamic/LeviAdjointDeterminantReciprocityReduction.lean`) gives the
reciprocity statement from these two statements and the proved `dynamicCentralizerReductive`.
Then apply `leviJacquetContragredient_of_structure`.

## Provenance of the derived content

The module adds no new mathematics beyond Renard's theorem. It only rewrites the hypotheses
of `LeviJacquetContragredientStatement` into the dynamic form. One choice is derived: the
opposite radical is identified on rational points only, because the statement's opposition
hypothesis is on rational points and the Jacquet functors use only point images.
