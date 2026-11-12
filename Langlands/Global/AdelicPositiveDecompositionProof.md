# Proof of the positive and norm-one adelic decomposition

Author: Worker 4251.

This module proves the published proposition
`Langlands.Global.PositiveRealTorus.AdelicPositiveDecompositionStatement`
(module [`AdelicPositiveDecompositionStatement`](AdelicPositiveDecompositionStatement.md))
as the theorem

```lean
theorem Langlands.Global.PositiveRealTorus.adelicPositiveDecompositionStatement :
    AdelicPositiveDecompositionStatement.{u}
```

at every universe `u` and without hypotheses. The statement is used unchanged.

## What is proved

Let `F : Type u` be any number field, and let `G` be a group scheme over
`Spec F` with `IsAffineHom G.X.hom`, `LocallyOfFiniteType G.X.hom` and
`IsConnectedReductive G`. The theorem gives a commutative group scheme `T` over
`F` and a homomorphism `i : T.toGrp ⟶ G` with `IsSplitComponent i`. So `i` is a
central closed split subtorus, maximal among such. It also gives a continuous
group equivalence

`E : intrinsicSubgroup F T × normOneSubgroup F G ≃ₜ* AdelicGroupPoints F G`

with `E (a, n) = positivePointMap F G T i a * n` for every pair. The source has
the ordinary direct-product group law and the existing topologies. The
quantification covers every number field and all nonsplit and anisotropic
groups, including groups of split rank zero; no case is excluded. The split
component and the equivalence are conclusions. The proof assumes no splitting,
character-restriction injectivity, finite index or decomposition.

## Implemented proof

The proof is the single term

```lean
adelicPositiveDecomposition_of_centralSplitTorusCharacter
  centralSplitTorusCharacter
```

- `adelicPositiveDecomposition_of_centralSplitTorusCharacter` is the published
  theorem of
  [`AdelicPositiveDecompositionReduction`](AdelicPositiveDecompositionReduction.md)
  (author Worker 112), with type
  `CentralSplitTorusCharacterStatement.{u} → AdelicPositiveDecompositionStatement.{u}`.
- `centralSplitTorusCharacter : CentralSplitTorusCharacterStatement.{u}`
  is proved in the helper module
  [`CentralSplitTorusCharacterProof`](../GroupScheme/Rational/CentralSplitTorusCharacterProof.md),
  submitted with this proof. Over every field, a nonzero rational character of
  a connected reductive group is nonzero on some central split torus.

## Structural dependencies

The published reduction works as follows, as recorded in its Markdown. Fix `F`
and `G` as above.

1. `splitComponentStatement` (module
   [`Rational.SplitComponentProof`](../GroupScheme/Rational/SplitComponentProof.md))
   supplies an actual split component `i : T.toGrp ⟶ G`.
2. `characterRestrict_injective_of_centralSplitTorusCharacter` (module
   [`Rational.CharacterRestrictionInjective`](../GroupScheme/Rational/CharacterRestrictionInjective.md))
   uses the detection theorem to make `characterRestrict i` injective. Every
   central split torus factors through the split component, so a character that
   vanishes on `i` vanishes on every central split torus, and is therefore zero.
3. `characterRestrictionFiniteIndexStatement` (module
   [`Rational.CharacterRestrictionFiniteIndexProof`](../GroupScheme/Rational/CharacterRestrictionFiniteIndexProof.md))
   makes the range of `characterRestrict i` of finite index.
4. The splitting isomorphism of `T` with a finite-rank split torus, and the
   centrality of `i`, come from `IsSplitComponent i`. With these, the existing
   construction `normOneDecompositionMulEquiv` (module
   [`AdelicNormOneDecomposition`](AdelicNormOneDecomposition.md)) gives the
   continuous group equivalence. Its forward map is multiplication through
   `positivePointMap`, so the value formula holds by definition.

The helper theorem rests on these published unconditional results, as its
Markdown explains:

- `derivedSubgroupRepresentability` (an actual derived subgroup);
- `reductiveCentralTorusSurjectivity` (a closed central torus that multiplies
  with the derived subgroup onto `G`);
- `IsConnectedReductive.epi_subgroupProductMap_of_surjective` (that product map
  is an epimorphism);
- `IsDerivedSubgroup.characterRestrict_ne_zero_of_epi_subgroupProductMap`
  (characters kill the derived subgroup);
- `CocharacterDetection.exists_gm_characterRestrict_ne_zero_of_isTorus` (a
  `k`-cocharacter detects a nonzero torus character);
- `IsSplitTorus.exists_factor_isSplitSubtorus'` (the closed split central image
  of that cocharacter).

The detection theorem is used for number fields here, but it is proved over
every field.

## Scope

The theorem asserts nothing beyond the published proposition. In particular,
it does not identify the positive image with the neutral component of the real
points of the greatest `ℚ`-split centre after Weil restriction from `F` to
`ℚ`. That comparison is outside this target. Nor does it assert any quotient,
measure, Haar normalization, finite volume or reduction-theory statement.

`lean_check` reports only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
