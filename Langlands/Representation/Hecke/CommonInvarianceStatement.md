# Common compact-open bi-invariance of actual Hecke test functions

`Langlands.Hecke.TestFunction.CommonCompactOpenBiInvarianceStatement` is a
Prop-valued statement, universally quantified over `G : Type u` for an arbitrary
universe `u`. Its hypotheses are exactly `Group G`, `TopologicalSpace G`,
`IsTopologicalGroup G`, `T2Space G`, `LocallyCompactSpace G`, and
`TotallyDisconnectedSpace G`: a Hausdorff locally compact totally disconnected
topological group.

For every finite set `s : Finset (Langlands.HarmonicAnalysis.SchwartzBruhat G)`
and every open subgroup `U : OpenSubgroup G`, the proposition asserts the
existence of an open subgroup `K : OpenSubgroup G` such that `K ≤ U`, its
underlying set `(K : Set G)` is compact, and every `f ∈ s` belongs to
`Langlands.Hecke.TestFunction.biInvariant K.toSubgroup K.toSubgroup`.
The order `K ≤ U` is actual subgroup inclusion. The same `K` works for all
functions and both sides. The empty finite set is allowed, and the singleton
case gives the corresponding assertion for one test function.

The module imports `Langlands.Representation.Hecke.TestFunction` and reuses its
existing complex function carrier and invariant submodule. A test function is
an actual locally constant, compactly supported function `G → ℂ`, as defined by
`Langlands.HarmonicAnalysis.SchwartzBruhat`. There is no extra function carrier
or assumed algebra structure. No countability, unimodularity, Haar measure, or
bi-invariance hypothesis is supplied.

The translation conventions are those of the imported module:
`(leftTranslate g f)(x) = f(g⁻¹ * x)` and
`(rightTranslate g f)(x) = f(x * g)`. Its `mem_biInvariant_iff` identifies the
required membership with being fixed by both operators for every `g ∈ K`.
The underlying submodule definition instead writes the left condition as
`f(k * x) = f(x)` for every `k ∈ K`; these conditions agree because a subgroup
is closed under inversion. The right condition is `f(x * k) = f(x)`.

This is a derived foundational proposition, motivated by compact support,
local constancy, and the compact-open identity-neighborhood basis. The intended
argument is to obtain a uniform left and right stabilizing identity neighborhood
from local constancy on compact support, combine these neighborhoods for the
finite family, intersect with `U`, and refine to a compact open subgroup. The
published `Langlands.Topology.CompactOpen.NeighborhoodBasis` supplies the
compact-open refinement under `NonarchimedeanGroup`; connecting the present
topological hypotheses to that basis belongs to the later proof. No such basis
or stabilizer is assumed as input to this statement. This module defines only
the proposition; its proof is a separate obligation against this fixed interface.

The motivating original is D. Flath, *Decomposition of representations into
tensor products* (1979), section 1, printed page 179, one-based PDF page 175 of
Corvallis Part I, registered as `flath-1979-tensor-products`. That page defines
`H(G)` using locally constant compactly supported complex functions and introduces
the normalized compact-open subgroup indicator `e_K`. It does not explicitly
state this finite-family bi-invariance assertion. The quantifiers and the
refinement inside a prescribed `U` are an internal derived formulation, not a
quoted theorem of Flath. The retained source is
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`,
SHA-256 `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.

Worker 108 authored this statement and its explanation.
