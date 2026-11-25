# Quaternionic spin covers from rank-one type-D indices

Module `Langlands.GroupScheme.SimplyConnected.TypeDRankOneSpinProof`.

`Langlands.GroupScheme.typeDRankOneSpin` proves the exact Library proposition
`Langlands.GroupScheme.TypeDRankOneSpinStatement.{u}` for every universe `u`.
It has no additional premise.

For any field `K : Type u` and affine locally finite type group scheme `G`
over `Spec K`, assume simple connectedness, absolute almost simplicity,
`splitRank G = 1`, and an actual Tits index of outer type `D₄` or inner
type `D₅` as specified in the target. The conclusion supplies a central
finite-dimensional division algebra `D : Type u` of dimension 4, a first-kind
involution `σ` whose symmetric subspace has dimension 3, and a nondegenerate
`σ`-quadratic form of Witt index one in respectively 4 or 5 variables.
It also supplies an actual morphism `π : G ⟶ σ.isometryGroup q` satisfying
`σ.IsSpinCover q π`. This includes smoothness of the isometry group and a
central isogeny from `G` onto its identity component. Every characteristic,
including characteristic 2, is retained.

## Implemented proof

The Lean term applies
`Langlands.GroupScheme.typeDRankOneSpin_of_classicalTypeDSpinPresentation`
to `Langlands.GroupScheme.classicalTypeDSpinPresentation`, at the same
universe `u`. Both are imported Library theorems.

The first theorem, from `TypeDRankOneSpinIndexReduction`, has type
`ClassicalTypeDSpinPresentationStatement.{u} →
TypeDRankOneSpinStatement.{u}`. The second, from
`ClassicalTypeDSpinPresentationProof`, proves exactly its premise without
additional hypotheses.

The reduction uses the supplied numbering of the actual index. The outer
`D₄` star action fixes the nonfork vertices because it either fixes all
vertices or swaps the two fork tips; the inner `D₅` action is trivial.
The general presentation gives a division degree `degree`, a form in `m`
variables, the equality `m * degree = 2 * n`, and the Witt-index and
distinguished-vertex comparisons. Split rank one gives Witt index one.
The distinguished vertex with one-based number 2 then gives
`2 = j * degree` with `0 < j ≤ 1`, hence `degree = 2` and `m = n`.
The dimension formulas specialize to 4 for the algebra and 3 for the
symmetric subspace. The reduction retains the form, its nondegeneracy,
and the actual spin-cover morphism from the general presentation.

## Provenance and scope

This is an internal composition of the two published theorems. It adds no
classification premise, field restriction, axiom or proof hole. The original
source comparison and conventions are documented in
`TypeDRankOneSpinStatement.md` and
`ClassicalTypeDSpinPresentationStatement.md`; the detailed implemented
reduction is documented in `TypeDRankOneSpinIndexReduction.md`.

The imported general proof constructs a spin cover aligned with the supplied
numbering before obtaining the index comparison, so the presentation used
in type `D₄` respects that numbering. The proof does not use the local
rank-one classification or any downstream Kneser–Tits result.
