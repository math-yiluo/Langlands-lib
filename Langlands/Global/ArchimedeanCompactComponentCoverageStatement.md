# Compact representatives of archimedean connected components

`Langlands.Global.ArchimedeanGL.CompactComponentCoverageStatement K n` is a
proposition for every number field `K : Type u` in an arbitrary universe `u`
and every natural rank `n`, including `n = 0`. It states that the published
standard compact subgroup meets every connected component of the actual
archimedean general linear group. This module states the proposition only; it
proves nothing.

## The proposition

For every point
`g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)`
there is an element `k : standardInfiniteCompact K n` such that
`g ∈ connectedComponent k.val`.

Connected components partition a topological space, so this says exactly that
the connected component of every point of the group contains an element of the
subgroup.

## Conventions and exact scope

- The group is Mathlib's `Matrix.GeneralLinearGroup (Fin n)
  (NumberField.InfiniteAdeleRing K)`, the units of the matrix ring over the
  completion-based infinite adele ring. This is the group abbreviated
  `Langlands.Global.InfiniteAdelicGL K n` in `Langlands.Global.AdelicGL`.
- Its topology is the published one, unchanged: the infinite adele ring
  carries the product topology of the archimedean completions, matrices carry
  the entrywise topology, and the unit group carries Mathlib's units topology.
  No other topology, norm, chart or manifold structure is introduced.
- The subgroup is the published `Langlands.Global.standardInfiniteCompact K n`
  from `Langlands.Global.ArchimedeanCompact`. It is the range of
  `ArchimedeanCompactFactors.toInfiniteAdelicGL K n`: the full orthogonal
  group `O(n)` at each real place and the unitary group `U(n)` at each complex
  place, assembled in mixed coordinates and transported to the completions by
  the inverse of `archimedeanGLCoordinates K n`. The real factors are the full
  orthogonal groups, not `SO(n)`. `mem_standardInfiniteCompact_iff`
  characterizes membership. No other compact subgroup is substituted.
- `connectedComponent` is Mathlib's connected component in that topology.
- No hypothesis of connectedness of the group, path-connectedness, polar
  decomposition, determinant sign, analyticity or positive rank is assumed.
  The rank-zero case and number fields with or without real places are all
  included.

## Provenance and purpose

This is an internal statement formulated by Worker 94. It is a topological
prerequisite of the automorphic differential-growth task
`e0d3fab3-d5c8-47ae-bd65-d85037d6fd80`. That task's source map,
`notes/automorphic/differential-growth-source-map.md`, describes the
separator argument of Harish-Chandra's *Discrete series II*, sections 7–8:
elliptic analyticity and vanishing of all jets force a Hahn–Banach
separating smooth coefficient function to vanish, which proves that the
enveloping-generated orbit is dense in the closed group-generated orbit.
Worker 94's route to that density uses the compact subgroup together with
enveloping derivatives. Harish-Chandra works with a connected real reductive
group, while the actual archimedean group here need not be connected. No
external source is cited for this Lean form.

The statement is the component bridge needed for scalar analytic uniqueness.
The published `AnalyticMatrixJetUniquenessStatement K n`, proved as
`Langlands.Global.ArchimedeanGL.analyticMatrixJetUniqueness`, concludes
vanishing of a function only on `connectedComponent x₀`, where `x₀` is a
basepoint at which its full ambient jet vanishes. The group need not be
connected. For example, when `K` has a real place and `n ≥ 1`, the real factor
`GL_n(ℝ)` contains matrices of both determinant signs and the continuous
nonvanishing determinant separates them. Analytic uniqueness on one component,
such as the identity component, then cannot by itself give vanishing on the
whole group. With
the present statement, vanishing information at points of the actual compact
subgroup can be propagated to every group point: a point `g` lies in the
component of some `k` in the subgroup, and uniqueness is applied at `k`.

The expected argument for the statement is classical but is not supplied here.
At a real place, polar decomposition writes an invertible matrix as an
orthogonal matrix times a positive definite symmetric matrix. The positive
definite matrices form a convex, hence connected, set, so the matrix lies in
the component of its orthogonal factor. Complex places are analogous with a
unitary factor. The places are then combined through the product topology and
the published coordinate homeomorphism. Proving the statement is a separate
obligation.

## What is not stated

This module defines only the proposition. It does not prove the component
coverage, polar decomposition, any path or deformation retraction, smooth or
Lie orbit density, finiteness of compact types, convolution reproduction or
automorphic growth. It does not count connected components, assert that the
group or the subgroup is connected, or assert that the subgroup is maximal
compact.
