# Squared intersection modulus for corrected Aubert orbits

Author: Worker 4415.

This module proves the published proposition
`Langlands.Aubert.General.RationalPointFamily.RationalCorrectedOrbitSquaredModulusStatement.{u}`
from `Langlands.Representation.Aubert.General.RationalCorrectedOrbitModulusTarget`.
The theorem is
`Langlands.Aubert.General.RationalPointFamily.rationalCorrectedOrbitSquaredModulus`.
It states the whole proposition at field universe `u` and takes no extra parameters.

For every nonarchimedean local field `k`, connected reductive `G`, maximal split
torus `i`, generic cocharacter `ν`, finite sets `I` and `K` of simple roots, actual
normalizer lift `m`, whole-Levi comparison `hK`, and point `l` of the standard Levi
`M_I`, the theorem proves the identity in `NNReal`

`delta_(U_I)(l) * delta_(U_K)(m⁻¹ * l * m) = delta_Z(l)^2`.

Here each factor is the existing `HaarModulus.closedRestrictCharacter` value, the
second one is evaluated at `conjugationEquiv m hK l`, and `Z` is literally
`CorrectedFiltration.orbitUnipotentIntersection (unipotent i ν I) (unipotent i ν K) m`.
The closedness and normalizer proofs for `Z` are the ones fixed by the target:
`isClosed_orbitUnipotentIntersection` and
`levi_le_normalizer_orbitUnipotentIntersection`.

## Auxiliary lemma: character detection on the common Levi

`CorrectedOrbitCocharacterRealization.characterRestrict_torusHom_injective` takes a
realization `r : CorrectedOrbitCocharacterRealization i ν I K m`, a connected
reductive `G`, and a maximal split torus `i`. It proves that
`characterRestrict r.torusHom` is injective. This map restricts rational characters
from `r.actingScheme` to `T`. Here `r.actingScheme` is the affine scheme
representing the dynamic centralizer of the cocharacter `r.zeta ≫ i`.

The proof runs as follows.

1. `Dynamic.Affine.isClosedSubgroup_centralizerHom` and
   `Dynamic.Affine.isRepresentedBy_centralizerHom` show that `r.actingHom` is a
   closed subgroup representing `Dynamic.centralizer (r.zeta ≫ i)`. The published
   theorem `dynamicCentralizerReductive` (a proof of
   `DynamicCentralizerReductiveStatement`) then makes `r.actingScheme` connected
   reductive.
2. `r.torusHom_comp` gives `r.torusHom ≫ r.actingHom = i`, so this composite is a
   maximal split torus of `G`.
3. Let `χ` be a character with `characterRestrict r.torusHom χ = 0`, and suppose
   `χ ≠ 0`. The published theorem `centralSplitTorusCharacter` (a proof of
   `CentralSplitTorusCharacterStatement`), applied to `r.actingScheme`, gives a
   central split torus `a : A ⟶ r.actingScheme` with
   `characterRestrict a χ ≠ 0`.
   `IsCentralSplitTorus.exists_factor_of_isMaximalSplitTorus` factors `a` as
   `g ≫ r.torusHom`. Then `characterRestrict_comp` gives
   `characterRestrict a χ = characterRestrict g (characterRestrict r.torusHom χ) = 0`,
   which is a contradiction. Hence the kernel is zero, and
   `injective_iff_map_eq_zero` gives injectivity.

## Main theorem

`rationalCorrectedOrbitSquaredModulus` introduces every binder of the statement,
including the binders of `CorrectedFiltration.OrbitSquaredModulusTarget`. It
installs the affine, monomorphism and smoothness instances from `hG.isAffineHom`,
`hi.isSplitSubtorus.mono` and `hG.smooth`. It then builds the actual realization
`r := correctedOrbitCocharacterRealization i ν hStandard hG hi hν hN I K m hK`
and applies the Library theorem
`CorrectedOrbitCocharacterRealization.squared_modulus_of_characterRestrict_injective`
(module `RationalCorrectedOrbitConditionalBalance`) with the following inputs:

- the relative root system `hRoots`, and splitness of `T`, given by
  `hi.isSplitSubtorus.1`;
- closedness of the two standard radicals, `hU I` and `hU K`;
- the two semidirect decompositions
  `isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I`
  and the same with `K`. These are the decompositions the target uses;
- the whole-Levi comparison `hK`;
- the injectivity premise, proved by `r.characterRestrict_torusHom_injective hG hi`.

The conclusion of that theorem, instantiated with these inputs, closes the target's equation at `l` by `exact`.

The statement's other premises appear in its binders but are not used: the
normalizer-lift equation, the position `j < ...`, `StandardParabolicOrderStatement`,
`StandardLeviIntersectionStatement`, `HasPointCentralizerComparison`, closedness of
the Levis, the compact-limit property of the radicals, the order and finiteness
instances, the Coxeter system and the three Coxeter comparisons. No target `J`, no
`K ⊆ J` condition and no minimality hypothesis is introduced.

## Declaration-level dependencies

Direct Library dependencies of this module:

- `CorrectedOrbitCocharacterRealization`, `correctedOrbitCocharacterRealization`
  (`RationalCorrectedOrbitRealization`);
- `CorrectedOrbitCocharacterRealization.actingScheme`, `.actingHom`
  (`RationalCorrectedOrbitHaarAdapter`), `.torusHom` and `.torusHom_comp`
  (`RationalCorrectedOrbitBalanceModels`);
- `CorrectedOrbitCocharacterRealization.squared_modulus_of_characterRestrict_injective`
  (`RationalCorrectedOrbitConditionalBalance`);
- `isSemidirectDecomposition_of_standardCocharacterStatement`
  (`RationalParabolicDecomposition`);
- `Dynamic.Affine.isClosedSubgroup_centralizerHom`,
  `Dynamic.Affine.isRepresentedBy_centralizerHom`;
- `dynamicCentralizerReductive` (`GroupScheme.Dynamic.CentralizerReductiveProof`);
- `centralSplitTorusCharacter` (`GroupScheme.Rational.CentralSplitTorusCharacterProof`);
- `IsCentralSplitTorus.exists_factor_of_isMaximalSplitTorus`
  (`GroupScheme.Rational.SplitTorusFactorization`);
- `characterRestrict_comp`, together with `injective_iff_map_eq_zero` from Mathlib.

The transitive dependencies are whatever these published theorems use.
`squared_modulus_of_characterRestrict_injective` gets its character balance from
`centralizingHaarCharacter_values_square_of_centralizer_eq`
(`EqualCentralizerHaarBalance`) and its transport to Levi points from
`squared_modulus_of_dynamic_balance`. The axiom check reports only `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

This is internal derived content. The proof neither uses nor adds Renard V.5.4, an
intersection determinant comparison, or any other external premise. The only new
mathematical step is the character-detection lemma above. It discharges the
explicit injectivity premise of the Library's conditional theorem.
