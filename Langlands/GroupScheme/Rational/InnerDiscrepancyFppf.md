# Fppf descent of points representing inner discrepancies

This internal supporting module uses the published
`LocalGroupIso.RepresentsDiscrepancy` and `AutomorphicAction.IsFaithful` definitions.
It defines the descended point representing a discrepancy and proves its
specifications from effective epimorphism descent, without source-dependent
assumptions. The definition is an internal construction using published APIs.

Fix group schemes `G`, `H`, `A` over any scheme `S`, a cover object `U`,
a local isomorphism `e : LocalGroupIso G H U`, and an action
`a : AutomorphicAction A G`. For two cover points `b,c : T ⟶ U`,
a point `x : T ⟶ A.X` represents their discrepancy if the action of every
restriction of `x` relates the two local isomorphisms on every refinement of `T`.

`representsDiscrepancy_of_fppf_cover` says this equation is local on an fppf
cover `p : V ⟶ T`, for a point already defined on `T`. The proof pulls the
cover to each refinement of `T`, uses naturality of the local isomorphism and
action, and cancels the resulting effective epimorphism.

The remaining results assume `a.IsFaithful`.
`representative_relation` proves that a representative over `V` agrees on all
pairs of maps to `V` that become equal in `T`. Indeed, each such pullback
represents the same discrepancy, and the published uniqueness lemma for a
faithful action equates them.

`representative_scheme_relation` expresses this compatibility for underlying
scheme maps by supplying them with their common map to `S`.
The entry definition `fppfDescendedRepresentative` constructs an actual morphism
`T ⟶ A.X` using `EffectiveEpi.desc` on the underlying schemes. Its structural
equation over `S` follows by cancellation of the cover. The theorem
`fppfDescendedRepresentative_pullback` proves its pullback is the supplied local
point. The first locality theorem gives `fppfDescendedRepresentative_spec`,
its all-refinement discrepancy equation.

`exists_representsDiscrepancy_of_fppf_cover` packages this defined point with
both specifications.
`exists_representsDiscrepancy_iff_fppf_cover` expresses the resulting equivalence
of existence on `T` and on `V`.

Finally, `hasInnerDiscrepancy_of_fppf_overlap` applies this descent to an fppf
cover of the universal overlap `U ×_S U`, then uses the published equivalence
between all-test innerness and the universal overlap equation.
Together with the existing `LocalGroupIso.innerCocycle` construction, this
allows locally obtained inner representatives to produce a natural cocycle.

Every cover used here is flat, surjective and locally of finite presentation
on underlying schemes. No quasi-compactness, affineness, reductivity,
connectedness or nonemptiness is assumed. The results do not assert that
local discrepancy representatives or quasi-split inner forms exist.
