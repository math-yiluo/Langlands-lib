# Transport of an exponent along a rank-one gallery

Author: Worker 5120.

This module carries an exponent across the walls of a finite rank-one gallery between
actual rational parabolics with a fixed embedded Levi. The galleries are those of the
published `Langlands.GroupScheme.ParabolicGallery` (Worker 153 and Worker 5120). All
declarations are in `Langlands.InducedTwistPersistence`.

## Point images

- `pointImage_comp_eq_inf_of_range_eq_comap`: if `range q = F.comap f` and `range r = F`,
  then `(q ≫ f)(Q(k)) = f(M(k)) ∩ r(R(k))`.
- `pointImage_le_of_range_le`: if `range r = F ≤ range p`, then
  `r(R(k)) ≤ p(P(k))`.

They translate the subgroup-functor conditions of `RationalRankOneWallData` into the
rational-point conditions of `isGeneralizedEigencharacter_wall`.

## The invariant

`PersistenceInvariant j b_L Z χ F` is a definition. It says that some actual rational
parabolic `r : R ⟶ G` has rational Levi `lR : L ⟶ R` with `lR ≫ r = j`, a geometric
unipotent radical, and range `F`, and that `χ` is an exponent of the central
`b_L : B ⟶ L` on the normalized Jacquet module `r_R(Z)`. It depends only on the subgroup
functor `F`.

## One wall

`persistenceInvariant_of_wall`. Let `F` be a parabolic image with Levi `j`, and let
`d : RationalRankOneWallData j F F'`. Given second adjointness
(`LeviSecondAdjointnessStatement.{u, v}`), finite length of `r_R(Z)` for every parabolic
with Levi `j`, and the irreducibility hypothesis `hirr` of the wall step for `d.q`, the
invariant passes from `F'` to `F`. The proof chooses radicals for `d.P`, `d.Q`, `d.Q'`
and `R`. It obtains the adjunction `i_{d.Q} ⊣ r_{d.Q'}` from the hypothesis, using
`d.commonLevi` and `d.opposite`, and applies `isGeneralizedEigencharacter_wall`.

## The gallery

`mem_rationalUnramifiedPrincipalOpen_mul`: the principal open set of `g₁ g₂` is the
intersection of those of `g₁` and `g₂`.

`exists_polynomial_persistenceInvariant_of_gallery`. Let `Z ψ s` be a family of
admissible representations indexed by `ψ ∈ X(M)` and `s ∈ Ix ψ`, with exponents
`χ ψ s` and finite-length Jacquet modules along every parabolic with Levi `j`. Suppose
`hwall` holds: for each wall `d` of the gallery relation `IsRationalRankOneWallAvoiding b j`
(that is, `b` is not central in the wall Levi), and each radical of `d.Q`, there is a
nonzero polynomial off whose zero set `hirr` holds for the whole family. Then
`ReflTransGen (IsRationalRankOneWallAvoiding b j) F F'` gives one nonzero polynomial off
whose zero set `PersistenceInvariant` passes from `F'` to `F` for every `ψ` and `s`. The
proof is induction on the head of the gallery (`Relation.ReflTransGen.head_induction_on`),
multiplying the wall polynomials.

## Provenance and boundary

This is the gallery step of the derived second-adjointness route to Konno 2003,
Theorem 4.2. Second adjointness enters only as the hypothesis `hadj`. It is the published
proof target `LeviSecondAdjointnessStatement`, not a theorem. The gallery is a hypothesis
of the last theorem. Its existence is the published proof target
`RationalParabolicGalleryAvoidingStatement`, used in
`InducedTwistQuotientPersistenceReduction`.
