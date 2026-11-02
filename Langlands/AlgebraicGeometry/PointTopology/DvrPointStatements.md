# Affine integral points over a discrete valuation ring

Source: Brian Conrad, *Weil and Grothendieck approaches to adelic points*,
December 31, 2011, Example 2.3, printed page 3; registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
This pair states the DVR conclusion; it does not supply its proof.

`DvrAffinePointProperties R K` uses an arbitrary discrete valuation ring `R`
and an actual fraction field `K`, specified by `Algebra R K` and
`IsFractionRing R K`. Both rings lie in the same arbitrary universe.
The topology on `K` is constructed from the valuation at the maximal ideal
using Mathlib's `Valued.mk'`. The topology on `R` is the topology induced by
its canonical injection into `K`. These are the valuation topologies intended
in Example 2.3; the target does not assert this result for arbitrary topologies
on a DVR. Neither completeness nor finite residue field is assumed.

For every actual affine scheme `X` over `Spec R` whose structure morphism is
locally of finite type, the canonical change-of-ring map on actual points
`X(R) → X(K)` is both an open embedding and a closed embedding.
Here affine schemes are quasi-compact, so local finite type has the source's
finite-type meaning. `RingPoint.changeRing` is actual precomposition by the
spectrum of `R → K` in the category of schemes over `Spec R`.
Both point spaces use the published global-section evaluation topology.

The explicit topology and fraction-field formulation clarify the source's
implicit valuation-topology convention. The host bridge is Mathlib's
`IsDiscreteValuationRing.equivValuationSubring`: it identifies `R` with the
closed unit ball of precisely the chosen maximal-ideal valuation.
Mathlib's valuation-topology results make this ball open and closed.
The coefficient-map comparison then gives the point-space assertions, using
finite generation for openness. These observations explain the statement's
meaning and intended proof route, without recording a proof as accepted.

The rational/integral adelic discreteness examples, nonaffine integral points,
and Weil restriction remain separate obligations of the parent program.
