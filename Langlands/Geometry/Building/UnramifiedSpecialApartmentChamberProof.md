# Ordinary coefficient-stable chambers in every supplied special apartment

Authors: Worker 198 and Worker 352.

The theorem
`Langlands.Geometry.Building.unramifiedSpecialApartmentChamber.{u}` proves
exactly the published
`Langlands.Geometry.Building.UnramifiedSpecialApartmentChamberStatement.{u}`.
The universe `u` is arbitrary. The proof retains all the statement's actual
special-torus, apartment, centralizer, compatibility and coefficient-action
data. It assumes no additional proposition and imposes no field or residue
characteristic restriction.

For the prescribed maximal base-field split torus and containing closed
commutative subgroup that becomes maximal split over the maximal unramified
field, every supplied full-V6-compatible coefficient-stable apartment `D`
contains a point regular for `D.affineRoots`. The whole sign facet of that
point is preserved setwise by each actual affine coefficient automorphism.
These are the ordinary affine roots in the supplied apartment.

The implementation is a composition of two published results:

1. `unramifiedSpecialApartmentChamber_of_connectedGeneration`, from
   `Langlands.Geometry.Building.UnramifiedSpecialApartmentArithmeticReduction`,
   has type `ConnectedGenerationStatement.{u} →
   UnramifiedSpecialApartmentChamberStatement.{u}`. It constructs a fixed
   point in the supplied apartment and its recovered integral models and zero
   datum, identifies the entire upper neutral integral-point subgroup with
   the zero-subgroup point fixer, and uses the recovered root-restriction and
   regular-facet construction. Its torus neutral-lifting and connected-bound
   arguments retain only connected generation as a premise.
2. `Langlands.GroupScheme.connectedGeneration.{u}`, from
   `Langlands.GroupScheme.IntegralModel.ConnectedGenerationProof`, proves that
   premise. It combines the published field-generation, Henselian
   congruence-lifting and Greenberg point-model results.

Applying the first theorem to the second gives the exact target proposition.
This file introduces no definitions or additional mathematical input. It
leaves the target Lean/Markdown pair and all imported files unchanged. The
construction and source correspondence are documented in the paired Markdown
of those published inputs and of the target; this final composition makes no
new literature assertion. It uses no local anisotropic classification,
local rank-one classification or local Kneser–Tits input.
