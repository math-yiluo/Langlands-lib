# Noetherian affine reduction for geometric-connectedness constructibility

Worker 105. This derived prerequisite expresses the Noetherian affine case of
constructibility for the actual geometric-connectedness fibre locus and proves
that it is equivalent to the existing general finite-presentation target.
It does not prove either universal constructibility proposition.

## Source and scope

The reduction follows the first paragraph of the proof of Stacks Project
Lemma 37.28.6, tag 055I, in the registered source
`stacks-fibre-constructibility-local-dimension-2026-11-04`, SHA-256
`1f3421cf5c5733cafdf296e8a9d38af7e4730550989a3d727d4b9a61cf1f3db3`.
The original retained `055I.html` reduces to an affine target, descends the
finite-presentation morphism to a finitely generated integer algebra, and uses
invariance of the geometric fibre property under arbitrary base change.
Here only the geometric-connectedness specialization is used, rather than
the full geometric-component count.

The target
`SchemeFiberGeometry.NoetherianAffineGeometricallyConnectedFiberConstructibility`
quantifies over all Noetherian commutative rings `R` in an arbitrary universe
`u` and all morphisms `f : X ⟶ Spec R` that are locally of finite presentation,
quasi-compact and quasi-separated. It requires constructibility of the actual
target set `geometricallyConnectedFiberLocus f`. The source scheme may be
nonaffine and nonseparated. Geometric connectedness retains nonemptiness through
Mathlib's `ConnectedSpace` convention.

This is an internal prerequisite for the general target used in Conrad,
*Weil and Grothendieck approaches to adelic points*, printed pages 5–6,
Theorem 3.4(2). No constructibility theorem, filtered descent theorem or
whole-paper completion is claimed.

## Implemented reduction

For an arbitrary ring `R` and a finite-presentation morphism to `Spec R`,
`isConstructible_geometricallyConnectedFiberLocus_spec_of_noetherianAffine`
uses the published `NoetherianApproximation.schemeSubalgebraDescent` to find
a model over a finitely generated subalgebra `T` of `R`. The scalar ring is
`ULift ℤ`, so the argument preserves the arbitrary universe `u`. This is a
ring-equivalent copy of the integers; consequently `T` is Noetherian.
The actual cartesian model square identifies the locus on `Spec R` with the
inverse image of the model locus. The Noetherian affine assertion and
Mathlib's constructible inverse-image theorem give the desired conclusion.

The reverse direction of
`geometricallyConnectedFiberLocalConstructibility_iff_noetherianAffine`
applies this result on the canonical affine open cover of the target.
Base change preserves each of the three finite-presentation hypotheses.
The actual locus comparison and the canonical chart-to-open-range isomorphism
identify the chart loci with the restrictions of the original set.
Mathlib's local constructibility gluing theorem completes the argument.
The forward direction uses the fact that a locally constructible subset of
a quasi-compact quasi-separated scheme is constructible.

The remaining Noetherian affine proposition requires a geometric generic
constancy argument. It is retained as an explicit unproved target, rather
than supplied as an assumed conclusion of a geometry structure.
