# Conditional squared-modulus compatibility for actual rational parabolics

Author: Worker 1615.

This module is a supporting construction for the host task proving
`Langlands.Plancherel.ConditionalParabolicIntertwiningStatement`. It reduces
the squared-modulus input of the published
`ConditionalParabolicIntertwiningInputs` (module
`ParabolicIntertwiningReduction`) to two open structural statements of the
Library:

- `RelativeRootSystemStatement` (module `GroupScheme.Rational.Statement`):
  every maximal split torus of a connected reductive group has a relative
  root system; and
- `CentralSplitTorusCharacterStatement` (module
  `GroupScheme.Rational.CentralSplitTorusCharacterStatement`): every nonzero
  rational character of a connected reductive group is nonzero on some
  central split torus.

Neither statement is proved here; both stay explicit premises.

## Setting

Throughout, `r : ParabolicRootPresentation p l a` and
`r' : ParabolicRootPresentation p' l' a` are presentations of two rational
parabolics with the same split component `a : A ⟶ M`. In the main results
they also have the same Levi composite, `hLevi : l ≫ p = l' ≫ p'`. The maps
`n : U ⟶ P` and `n' : U' ⟶ P'` are geometric unipotent radicals.
`r.data.i : T ⟶ G` is the maximal split torus of the first presentation, and
`r.data.f` is the factor of the split component through it.

## Torus cocharacters and identifications

- `parabolicTorusCocharacter r ν` is the cocharacter
  `RealTorusSpace.cocharacterMapInt r.data.f ν` of `T`, the push of a
  cocharacter `ν` of `A`.
- `parabolic_groupHom_torusCocharacter_comp`: its composite with `r.data.i`
  equals `ν ≫ a ≫ l ≫ p`. This uses the factorization `r.isCompatible.factor_comp`.
- `parabolic_centralizer_torusCocharacter_eq` (assuming `hLevi`): the pushes
  of the two split-component cocharacters have the same full dynamic
  centralizer, since both centralizers are the common Levi image
  (`levi_eq_splitComponentCocharacter` of each presentation).
- `parabolic_levi_eq_centralizer_torusCocharacter`: the Levi image
  `range (l ≫ p)` is the dynamic centralizer of the first pushed
  cocharacter.
- `parabolic_radical_eq_unipotent_torusCocharacter`: `range (n ≫ p)` is the
  dynamic unipotent subgroup of the first pushed cocharacter.
  `parabolic_radical'_eq_unipotent_torusCocharacter` (assuming `hLevi`):
  `range (n' ≫ p')` is the dynamic unipotent subgroup of the push of the
  second split-component cocharacter. Both use `range_comp_radical_eq`.

## Torus factor through the Levi and character restriction

- `parabolic_exists_torusLeviFactor`: there is `j : T ⟶ M` with
  `j ≫ l ≫ p = r.data.i`. Proof: `l ≫ p` is a monomorphism representing the
  centralizer of a cocharacter of `T`, so the published `Dynamic.torusFactor`
  and `Dynamic.torusFactor_comp` (module `GroupScheme.Rational.LeviFactorization`)
  apply.
- `parabolic_groupHom_comp_torusLeviFactor`: for every such `j`,
  `r.data.f ≫ j = a`, by cancelling the monomorphism `l ≫ p`.
- `parabolic_characterRestrict_injective_of_splitComponent`: if restricting
  rational characters of `M` along `a` is injective, then so is restricting
  along every such `j`. This is because restriction along `a` factors through
  restriction along `j` (`characterRestrict_comp`).
- `parabolic_characterRestrict_injective_of_centralSplitTorusCharacter`:
  assuming `CentralSplitTorusCharacterStatement`, restriction along every
  such `j` is injective. Here `M` is connected reductive and `a` is its
  split component, so the published
  `characterRestrict_injective_of_centralSplitTorusCharacter` (module
  `GroupScheme.Rational.CharacterRestrictionInjective`) applies.

## The squared-modulus compatibility

The ambient group is smooth with affine structure map. `M` is affine, `F` is
a nonarchimedean local field, and the rational points of `G` carry the point
topology and are locally compact, nonarchimedean and Hausdorff. The
semidirect decompositions `h` and `h'` of the two parabolic point groups have
the common Levi point subgroup and the actual radical point groups. These
radical groups are closed (`hU`, `hU'`), and the intersection carries a
Borel measurable structure.

`parabolic_squaredModulusCompatibility_of_characterRestrict_injective` takes
`hLevi`, `hn`, `hn'`, `hroot : HasRelativeRootSystem r.data.i`, a torus
factor `j` with `j ≫ l ≫ p = r.data.i`, injectivity of restriction along
`j`, and the decompositions and closedness facts. It proves the published
`SquaredModulusCompatibility h hU h' hU'` (module
`StandardIntertwiningTarget`). On the Levi point subgroup, the product of the
Haar moduli of conjugation on the two radicals equals the square of the
modulus on their intersection.

Proof. By the published `squaredModulusCompatibility_iff` it suffices to
check the identity at each point `m` of the Levi point subgroup, which comes
from a rational point `z` of `M`. Apply the published
`centralizingHaarCharacter_values_square_of_centralizer_eq` (module
`Aubert.General.EqualCentralizerHaarBalance`) with:

- the two pushed cocharacters;
- the acting group `Z = M` with map `l ≫ p`;
- the dynamic unipotent groups and their intersection, represented and
  closed by the affine dynamic representability results and
  `isRepresentedBy_subgroupIntersectionHom`;
- Lie coordinates from `Lie.finiteCoordinates`;
- the factor `j`; and
- the injectivity premise.

The three Haar characters it compares are those of the dynamic subgroups.
The identifications above rewrite them as the closed-normalizer characters
of the actual radical point groups and their intersection, through the
private congruence lemma `closedNormalizerCharacter_congr'` and the published
`levi_le_normalizer_intersection`.

`parabolic_squaredModulusCompatibility_of_structural` proves the same
conclusion from `hRS : RelativeRootSystemStatement.{u}`,
`hS : CentralSplitTorusCharacterStatement.{u}` and
`hG : IsConnectedReductive G` instead of `hroot`, `j` and injectivity. It
takes `j` from `parabolic_exists_torusLeviFactor` and `hroot` from `hRS`
applied to the maximal split torus `r.isCompatible.maximalSplit`. Injectivity
comes from `hS` as above.

## Reduction of the host inputs

`ConditionalParabolicAnalyticInputs.{u, uV}` is a proposition (a `def` of
type `Prop`). It has exactly the binders, local instances and `let`
definitions of the published `ConditionalParabolicIntertwiningInputs`, and
its conclusion is that proposition's conclusion without the squared-modulus
compatibility. For each admissible finite-length smooth representation `π`
of the Levi point subgroup it asserts one real threshold `R` such that:

- the published actual standard-integral `domain` is the whole source at
  every parameter of `C R`; and
- for every radical-unimodularity proof `hδ`, the published
  `CompactIntegralLocallyDominatedOn` holds on `C R`.

Nothing here proves it.

- `conditionalParabolicIntertwiningInputs_of_analyticInputs`: `hRS`, `hS` and
  `ConditionalParabolicAnalyticInputs.{u, uV}` imply
  `ConditionalParabolicIntertwiningInputs.{u, uV}`. After introducing the
  data, the analytic inputs give `R`, convergence and domination.
  `parabolic_squaredModulusCompatibility_of_structural` gives the
  squared-modulus compatibility.
- `conditionalParabolicIntertwiningStatement_of_analyticInputs`: `hRS`, `hS`
  and the analytic inputs imply
  `ConditionalParabolicIntertwiningStatement.{u, uV, uW}`, by the published
  `conditionalParabolicIntertwiningStatement_of_inputs`.

## Scope and provenance

This module does not prove `RelativeRootSystemStatement`,
`CentralSplitTorusCharacterStatement`, convergence or domination. It does not
prove the host theorem. Its two final theorems carry the structural
statements and the analytic inputs as explicit premises, and they are not
the host proof. The content is an internal adapter. It transfers the
published equal-centralizer Haar balance from dynamic subgroups of a
presentation torus to the actual radicals of the host statement. No
literature theorem replaces a proof.
