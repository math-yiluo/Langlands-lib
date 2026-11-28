# Integral comparison of compact Tate-normalized representatives

The comparison takes compact Tate-normalized representatives of the
original Harris classes at a compact open level. The bases are connected
admissible CM tests over `Spec F` for the given signature charts. In
particular, they supply the locally noetherian and quasi-separated
geometry, dual data, invertibility of positive integers, finite étale
roots of unity, and pair additivity used by the original class tower.
The constructions use the Picard and tensor prerequisites, finite Weil
transition compatibility, the rational comparison for the profinite
integer adeles, and torsion finite étaleness.

`CompactTateCMRepresentative.pointedClass` forms the class using the
representative's determinant and numerical conditions.
`CompactTateCMRepresentative.pointMap` transports its level along an
isomorphism of finite étale fibre functors, using compact orbit lattice
transport to keep the normalization. The transported representative gives
the value at the new point of any compatible geometric family that the
original representative gives at the starting point.

`CompactTateCMRepresentative.pullback` uses `levelDataBaseChange` on a
morphism of admissible bases with a geometric point on its source.
It takes dual base-change naturality and polarization stability, and uses
the pullback dual data from the admissible bases.
`geometricFamilyPointPullback_classOf` supplies the determinant and
numerical conditions for the pulled-back object and compares the pointed
class with the pullback of the compatible family. Compact lattice base
change preserves the normalization on the same pulled-back object.

`CompactTateCMWitness` records a polarized rational action isomorphism with
its positive rational polarization multiplier and its equality of level
orbits. It includes an abelian-scheme isomorphism whose two arrows
rationalize to the corresponding rational arrows. Given equality of the
two pointed classes, `nonempty_compactTateCMWitness` uses
`HarrisNumericalWeilLevel.classOf_eq_iff` to obtain the rational witness.
The point is of characteristic zero by its map to `Spec F`.
`harrisCompactTateNormalized_iso_integral` lifts the rational arrows using
the compact normalization of both sides.

On a common connected test, `nonempty_compactTateCMWitness_overlap`
chooses paths from the original geometric points to the composites of a
point of that test. It transports and pulls back the two representatives.
Equality of the two pulled-back families gives equality at the chosen
point, so the pointed comparison supplies the integral witness.
