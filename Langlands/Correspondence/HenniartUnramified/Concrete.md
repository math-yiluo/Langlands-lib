# Local Weil groups as split degree data, and their unramified stages

Let `F` be a p-adic field and `φ` an element of its Weil group of geometric degree one,
for example the Library's `localGeometricFrobenius F`.

- `weilSplit F φ hφ` is the split degree datum with degree `localDegree F` and lift `φ`.
- `Langlands.Weil.Local.localInertia F` is the degree kernel that forms the inertia subgroup of `weilSplit F φ hφ`.

## The unramified stages

For `m : ℕ`, let `L = (unramifiedStage F (m + 1)).asPadicField`, the unramified
extension of degree `m + 1` from `HenniartUnramified/Degree`. Its residue degree is
`m + 1` (`unramifiedStage_residueDegree`).

- `φ ^ (m + 1)` lies in the image of the intermediate Weil map
  (`pow_mem_unramifiedStage`), and so does all of inertia
  (`localInertia_le_unramifiedStage`).
- `stageLift` is the preimage of `φ ^ (m + 1)` in `W_L`. It has degree one
  (`stageLift_degree`), by the published degree formula
  `deg_F(ι w) = f(L/F) · deg_L(w)`.
- `stageKappa` maps inertia of `F` to `W_L` through the inverse of
  `intermediateWeilEquiv`.

`weilStage F φ hφ m` is the resulting `Stage` of degree `m + 1` from
`weilSplit L (stageLift …)` to `weilSplit F φ hφ`. Its map `ι` is the Library's
`intermediateWeilMap`, which is injective and continuous. The axioms
`ι (κ n) = n` and `ι (stageLift) = φ ^ (m + 1)` follow from
`intermediateWeilMap_equiv_symm`. The degree axiom is `intermediateWeilEquiv_degree`
with residue degree `m + 1`.

## Breaks of inertia representations

`inertiaBreak F ρ`, for a representation `ρ` of inertia, is the infimum of the
nonnegative real `v` such that every inertia element of the Library's upper
ramification group `upperGroup F v` acts trivially. This is the same infimum as the
Library's `lastBreak`, read on inertia.

- `Langlands.ArithmeticStableTwist.upperGroup_le_localInertia`: upper groups of nonnegative index lie in inertia, by
  `absoluteUpperCanonicalInertia` and antitonicity.
- `upperGroup_normal'`: upper groups are normal.
- `lastBreak_eq_inertiaBreak`: the last break of a representation of `W_F` is the
  break of its inertia restriction. For nonnegative indices the two triviality
  conditions agree, because the upper groups lie in inertia.
- `inertiaBreak_congr`: two inertia representations with the same triviality on every
  nonnegative upper group have the same break.
- `inertiaBreak_equiv`: equivalent inertia representations have the same break, by
  `eq_one_of_equiv`.

This module instantiates the abstract Clifford theory for the proof of Henniart (1988),
Proposition 2.2 (route note, Proposition `prop:unram`). It is internal
infrastructure.
