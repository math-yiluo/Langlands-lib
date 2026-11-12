# Proof: existence of simply connected covers of actual reductive derived subgroups

Author: Worker 4073. The tactic body follows Worker 1363's conditional
composition draft (revision 1 of this task's shared draft, carried over from an
earlier TaskHub instance). Worker 1363 has no identity in this instance, so they
are credited here rather than as a submission coauthor. That draft took the three
prerequisite statements as premises. Here the published proofs replace them.

`Langlands.GroupScheme.simplyConnectedDerivedCoverExistence` proves the Library
statement `Langlands.GroupScheme.SimplyConnectedDerivedCoverExistenceStatement.{u}`
from `SimplyConnected/DerivedCoverStatement`, unconditionally and for an
arbitrary universe `u`. Its type is exactly that statement.

## The implemented proof

The proof combines three published theorems. It follows the route that
`SimplyConnected/DerivedCoverStatement.md` describes.

Fix a field `k` in universe `u` and a group scheme `G` over `Spec k` with
`hG : IsConnectedReductive G`.

1. **Derived subgroup.** The proof installs `IsAffineHom G.X.hom` from
   `hG.isAffineHom` and `Smooth G.X.hom` from `hG.smooth` as local instances.
   Smoothness supplies the `LocallyOfFiniteType G.X.hom` instance. The published
   theorem `derivedSubgroupRepresentability`
   (`Derived/RepresentabilityProof`, proving
   `DerivedSubgroupRepresentabilityStatement`) then gives a group scheme `D`, a
   homomorphism `d : D ⟶ G` and `hd : IsDerivedSubgroup d`.
2. **Semisimplicity.** The published theorem `derivedSubgroupSemisimple`
   (`Derived/SemisimpleProof`, proving `DerivedSubgroupSemisimpleStatement`,
   Milne Proposition 19.21(c)), applied to `G`, `D`, `d`, `hG` and `hd`, gives
   `IsSemisimple D`.
3. **Simply connected cover.** The published theorem
   `simplyConnectedCoverExistence` (`SimplyConnected/CoverExistenceProof`,
   proving `SimplyConnectedCoverExistenceStatement`, CGP Corollary A.4.11(1)),
   applied to `D`, gives a group scheme `C`, a homomorphism `π : C ⟶ D` and
   `hπ : IsSimplyConnectedCover π`.

The witnesses are `D`, `C`, `d` and `π`. The three fields of
`IsSimplyConnectedDerivedCover d π` are `hG`, `hd` and `hπ`.

## Checks

`lean_check` of `Langlands.GroupScheme.SimplyConnected.DerivedCoverProof` with
declaration `Langlands.GroupScheme.simplyConnectedDerivedCoverExistence` reported
0 errors and 0 warnings. The only axioms used are `propext`, `Classical.choice`
and `Quot.sound`.

## Scope

This module proves only the existence statement. It adds no uniqueness or
field-extension claim beyond what the statement says. For two covers of the same
derived subgroup, the published lemmas `IsSimplyConnectedCover.iso` and
`IsSimplyConnectedCover.iso_unique` remain the comparison tools.
