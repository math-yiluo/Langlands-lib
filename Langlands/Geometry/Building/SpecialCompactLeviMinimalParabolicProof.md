# Algebraic minimal-parabolic compatibility in actual standard Levi schemes

Authors: Worker 255 and Worker 3642. Worker 3642 supplied the initial proof
composition; Worker 255 checked the published inputs and prepared this pair.

`Langlands.GroupScheme.standardLeviMinimalParabolicCompatibility` proves exactly
`Langlands.GroupScheme.StandardLeviMinimalParabolicCompatibilityStatement.{u}`
with no additional premise, for arbitrary universe `u`.

For a full nonarchimedean local field `F`, an actual connected reductive group
scheme `G/F`, a maximal split torus `i`, a generic cocharacter `ν`, and
`J ⊆ simpleRelativeRoots i ν`, the five conclusions are connected reductivity
of the actual `Standard.leviScheme i ν J`, minimality of the chosen ambient
empty-index standard parabolic, minimality of the intrinsic dynamic parabolic
of the same cocharacter in that Levi, equality of the intrinsic functor with
the pullback of the chosen ambient parabolic on every test scheme, and the
literal rational-point image identity with the ambient intersection.

## Implemented proof

The proof composes published Library theorems, imported by Lean module name.

1. `Langlands.BruhatTits.SpecialCompact.standardLevi_isConnectedReductive`
   supplies connected reductivity of the actual standard Levi `L`. Affineness
   of `G` and `L` comes from the respective connected-reductive hypotheses;
   the monomorphism instance for `i` comes from its maximal-split hypothesis.
2. `Standard.isMaximalSplitTorus_leviTorusHom` keeps the same torus maximal
   split in `L`. The theorem
   `Langlands.HarishChandraSchwartz.isGenericCocharacter_leviTorusHom` keeps
   the same `ν` generic, since the relative roots of `L` are relative roots
   of `G`.
3. Apply `standardCocharacter` to the empty index and evaluate its comparison
   at `ν`, using `isStandardCocharacter_empty_self`. This identifies
   `standardParabolic i ν ∅` with
   `Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)`.
4. Apply the unconditional published `genericMinimalParabolic` to `G` and
   rewrite by step 3. Apply it again to `L`, with
   `Standard.leviTorusHom i ν J` and the genericity proof from step 2. The
   intrinsic Levi parabolic is definitionally this dynamic parabolic.
5. The final two clauses are
   `Standard.leviGenericParabolic_eq_comap_standard` and
   `Standard.leviGenericParabolic_points_map`, both applied to the same
   ambient equality from step 3. The former is an equality of subgroup
   functors on every test scheme. The latter states

   ```text
   j(P_L(ν)(F)) = P_∅(F) ∩ M_J(F),
   ```

   where `j = Standard.leviHom i ν J` and the map is
   `rationalPoints.map j`. The point identity does not supply the proof of
   functor equality or minimality; those are proved by the preceding inputs.

## Provenance and scope

This proof is an internal composition of published results and adds no new
literature assertion. Its target's original provenance is Renard,
*Représentations des groupes réductifs p-adiques*, 9 July 2026 edition,
V.5.1(5), printed p.122 / PDF p.128, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
That passage concerns rational-point groups. The scheme-level all-test
formulation is the derived refinement explained in the published
[statement Markdown](SpecialCompactLeviMinimalParabolicStatement.md).

The field may have any characteristic, and the group need not be split or
quasisplit. The local-field instances remain in the theorem to match the
published target; the algebraic composition uses only the field structure.
The statement and all imported Lean/Markdown pairs are unchanged.

The proof establishes algebraic compatibility. The inherited apartment,
compactness and openness, Iwasawa and Cartan conclusions, and analytic
Plancherel conclusions remain separate obligations.
