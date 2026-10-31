# Laws of the actual right-coordinate topology

Worker 6 authored the Lean proof and its initial explanation. Worker 345
checked the original source, the published prerequisites and the complete
interfaces, and prepared this focused proof pair. The closing theorem
`Langlands.Algebra.idempotentedRingTopologyTheorem_proof` has exactly the
published type `Langlands.Algebra.IdempotentedRingTopologyTheorem.{uA}`.

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original I.1.1–I.1.3, printed pp.6–9/PDF12–15, supplies the nonunital
convention, finite local units, actual right-annihilator uniformity and
injectivity of the canonical coordinate map. The uniform additive-group
and topological-ring packages and the explicit multiplication laws are
internal intrinsic consequences of this construction, not separate
numbered theorems or class formulations attributed to Renard.

Every proof uses the original `A : Type uA` with its original
`NonUnitalRing A` operations. It installs
`idempotentedRingUniformSpace A` locally, with no ambient topology
parameter or global instance. The proof retains zero rings and requires
no unit, nontriviality, commutativity or size restriction. Its closed
target preserves the weaker hypotheses for the first two clauses.

`idempotentedRing_uniformAddGroup` writes each actual right coordinate
as an additive homomorphism, using distributivity. The discrete
uniformity makes the codomain a uniform additive group. Mathlib's
`IsUniformAddGroup.comap` and `isUniformAddGroup_iInf` then prove that
the actual coordinate infimum respects subtraction. This proof needs
only a nonunital ring.

`idempotentedRing_rightCoordinatesSeparate` chooses a finite local
unit for `a - b`. Equality of the right coordinates at that idempotent
makes `(a - b) * e` zero, and the local-unit identity makes it `a - b`.
The converse follows by substitution.
`idempotentedRing_hausdorff` uses the actual singleton-coordinate
entourage basis. Membership of a pair in every entourage implies
equality of every right coordinate and hence equality of the elements.
This gives `T0Space`, and Mathlib upgrades a uniform T0 space to a
Hausdorff space.

`idempotentedRing_leftMultiplicationUniform` proves the coordinatewise
uniform continuity of `a ↦ b * a`. For every `e`, its right coordinate
is `b * (a * e)`. The coordinate is uniformly continuous to the
discrete carrier, and any map on a discrete uniform space is uniformly
continuous. The comap and infimum characterizations give the claim for
the actual uniformity. No idempotentedness is needed.

`idempotentedRing_rightMultiplicationUniform` uses finite local units.
For a target coordinate `e`, choose an actual idempotent `f` fixing
`b * e` on the left. If `x * f = y * f`, then
`(x * b) * e = (x * f) * (b * e) = (y * f) * (b * e) = (y * b) * e`.
The actual entourage-basis criterion for uniform continuity completes
the proof.

`idempotentedRing_topologicalRing` first obtains the topological
additive group from the proved uniform additive-group law. At zero,
the product of all first coordinates and the zero-neighborhood
`e.rightAnnihilator` in the second coordinate maps into that same
zero-neighborhood, by its proved stability under left multiplication.
This proves joint continuity at zero. The two preceding uniform
continuity laws imply continuity of multiplication by every fixed
element. Mathlib's `IsTopologicalRing.of_addGroup_of_nhds_zero` combines
these facts with additive translation to prove joint continuity
everywhere, with the original operations.

`idempotentedRingTopologyTheorem_proof` combines the six proved
interfaces into the exact closed target at the arbitrary ring
universe. The module checks every complete unapplied interface.
These are proofs of intrinsic laws, not input certificates or
properties of a replacement ring or quotient.

The module imports the published statement by its Lean name,
`Langlands.Algebra.IdempotentedRingTopologyStatements`, and changes no
prerequisite. The source pages were read directly, including visual checks
of PDF14–15. No source-specific project errata note was present when this
pair was prepared. The Mathlib packaging is internal formalization
provenance: the additive comap/infimum laws come from
`Mathlib.Topology.Algebra.IsUniformGroup.Constructions`, the uniform
separation criterion from `Mathlib.Topology.UniformSpace.Separation`,
and the multiplication-at-zero criterion from
`Mathlib.Topology.Algebra.Ring.Basic`.

This pair asserts no inverse-limit topology, density, completeness,
completion multiplication, direct-sum/quotient comparison or extended
module action. All those obligations remain separate.
