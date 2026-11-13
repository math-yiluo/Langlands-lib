# Proof of rank-one galleries avoiding a central split torus

Author: Worker 5515.

`Langlands.GroupScheme.rationalParabolicGalleryAvoiding` proves the published
proposition `RationalParabolicGalleryAvoidingStatement.{u}` (module
`ParabolicGalleryStatement`) exactly, at an arbitrary universe `u`, with no
added hypothesis.

The statement concerns any field `k` and connected reductive `G` over `k`. It
takes an embedded rational Levi `j : L → G`, a split subtorus `b : B → L` that
is central in `L`, and two actual rational parabolic subgroup functors `F`,
`F'` of `G` with Levi `j`. Assume that `F` and `F'` meet the whole torus
centralizer `Z_G(b ≫ j)` in the same subgroup functor. Then the theorem gives
a finite gallery from `F` to `F'` of actual rank-one walls
(`RationalRankOneWallData`). At every wall, `b` composed with the inner Levi
inclusion into the wall Levi is not central. This statement is the internal
geometric input of the persistence argument for Task 5515. Its provenance is
explained in the statement pair.

## Implemented proof

The proof works with rational cocharacter directions in a split component of
`L`. It uses the published finite-arrangement chamber gallery and the
published actual wall models. The module proves four auxiliary results, all
in namespace `Langlands.GroupScheme.RationalCocharacter`.

1. **`torusCentralizer_eq_range_of_isRationalParabolicWithLevi`.** Let
   `a : A → L` be a split component of `L` and `F` an actual rational
   parabolic with Levi `j`. Then the whole torus centralizer
   `torusCentralizer (a ≫ j)` equals the image of `j`.
   - The inclusion `≤` uses a parabolic root presentation of the actual
     maps, obtained from `parabolicRootPresentationExistence`. It also uses
     `ParabolicRootPresentation.levi_eq_splitComponentCocharacter`, which
     identifies the image of the Levi with the dynamic centralizer of one
     cocharacter of `A`, and `torusCentralizer_le_dynamicCentralizer`.
   - The inclusion `≥` is `IsCentral.range_le_torusCentralizer_comp`,
     because `a` is central in `L`.

2. **`exists_regular_parabolic_eq`.** Every such `F` equals
   `parabolic hA (a ≫ j) x` for a rational direction `x`. This direction is
   regular for the finite family `rootForms (a ≫ j)` of actual relative-root
   forms.
   - Take `x` to be the rational evaluation of the presentation's
     split-component cocharacter.
   - Regularity follows from `regular_ofIntegral_of_centralizer_eq`, using
     step 1 and `levi_eq_splitComponentCocharacter`.
   - The equality of parabolics is `parabolic_ofIntegral` combined with
     `ParabolicRootPresentation.parabolic_eq_splitComponentCocharacter`.

3. **`mul_pos_of_inf_dynamicCentralizer_eq`.** Let `x` and `y` be regular
   directions. Suppose their parabolics meet the dynamic centralizer of an
   integral cocharacter `ν₀` of `A` in the same subgroup functor. Then every
   actual relative root `α` with `⟨α, ν₀⟩ = 0` has the same strict sign at
   `x` and at `y`.
   - Take the actual dynamic Levi model of `ν₀`
     (`Dynamic.rationalParabolicModel`). Factor the torus through it
     (`Dynamic.torusFactor`). Then `α` is a relative root there
     (`mem_relativeRoots_of_pairing_eq_zero`).
   - The two parabolics have equal pullbacks to that Levi. This uses
     `SubgroupFunctor.mem_comap` and the representation of the dynamic
     centralizer.
   - `Dynamic.parabolic_eq_comap_of_isClosedSubgroup` identifies each
     pullback with the dynamic parabolic of the same direction inside the
     Levi.
   - `IntegralRealization.parabolic_le_iff`, applied in both directions,
     shows that `α` is nonnegative at `x` exactly when it is nonnegative at
     `y`. Regularity rules out zero values.

4. **`not_isCentral_wallModel`.** Take a wall direction `w` between `x` and
   `y` (`IsWallDirection`), with its actual wall model `hw.wallModel`. Suppose
   every relative root vanishing on `w` pairs nontrivially with
   `ν ≫ g`, where `g ≫ a = b`. Then `b ≫ l ≫ q` is not central in the wall
   Levi.
   - A root `α` vanishing on `w` exists by `IsWallDirection.root`. It is an
     actual root of the wall Levi, by `IsWallDirection.mem_relativeRoots_iff`
     and the model's `centralizer_rep`.
   - If `g ≫ a ≫ l ≫ q` were central, then
     `root_restrict_eq_zero_of_isCentral` would give `g ≫ α = 0`. Hence
     `⟨α, ν ≫ g⟩ = 0` (`latticePairing_apply`), which contradicts the
     hypothesis.

**Main theorem.** The proof of `rationalParabolicGalleryAvoiding` runs as
follows.

- `L` is connected reductive, because it is the Levi of `F`. Choose a split
  component `a : A → L` (`exists_isSplitComponent`).
- `j` is a closed subgroup, and by step 1 `j` represents
  `torusCentralizer (a ≫ j)`.
- Step 2 writes `F` and `F'` as `parabolic hA (a ≫ j) x` and
  `parabolic hA (a ≫ j) y` with `x` and `y` regular.
- `IsSplitComponent.exists_factor` factors the central split torus `b` as
  `g ≫ a`.
- `IsSplitTorus.exists_genericCocharacter` gives a generic cocharacter `ν` of
  `B` for `b ≫ j`. Then
  `IsSplitTorus.dynamicCentralizer_eq_torusCentralizer` identifies the
  dynamic centralizer of `ν₀ = ν ≫ g` in `G` with `Z_G(b ≫ j)`. So the
  hypothesis is the hypothesis of step 3 for `ν₀`.
- Step 3 shows that every relative root `α` with `⟨α, ν₀⟩ = 0` has the same
  sign at `x` and `y`. The relative roots are finite
  (`IsSplitTorus.finite_relativeRoots`). Therefore `reflTransGen_chamberStep`
  gives a finite chain of chamber steps from `x` to `y`, none of whose walls
  vanishes on such a root.
- The chain is mapped to parabolics by `Relation.ReflTransGen.lift'`. A
  same-chamber step gives equal parabolics (`parabolic_eq_of_sameChamber`).
- A wall-adjacent step gives a wall direction
  (`exists_isWallDirection_of_wallAdjacent`) and its actual wall model
  (`IsWallDirection.wallModel`). Both endpoints keep the Levi `j`
  (`isRationalParabolicWithLevi_of_regular`). Step 4 shows that `b` is
  noncentral in that wall's Levi.

The proof covers arbitrary fields and characteristic, nonsplit `G` and
nonreduced relative roots. It keeps the original specified maps `j` and `b`.

The theorem uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
