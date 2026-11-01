# Locally constant sections on actual original-chart domains

Author: Worker 56.

Fix a published actual indexed affinoid atlas `a` on a topological space
`X`, over a complete ultrametric normed field. Its domain objects retain
the actual subsets, the finite relative neighborhood condition for
contained original charts, and their constructed subspace atlases.
The coefficient type `A` has an independent universe and no topology,
algebra, action or nonemptiness assumption.

`locallyConstantRestrict` precomposes an actual locally constant function
with the literal domain inclusion. `locallyConstantRestrict_apply` gives
this formula. `locallyConstantPresheaf a A` has the entire set
`LocallyConstant S A` at each domain `S`, with these actual restrictions.
Identity and composition hold by evaluating functions; there are no
supplied restriction or gluing operators in its input.

The construction treats an arbitrary covering sieve of the published
`quasinetTopology`, with its full Mathlib family of elements and full
compatibility condition. `locallyConstantCompatible_apply` compares two
sections on their actual intersection domain `U ⊓ V`. The two composite
inclusions into `S` agree, so compatibility gives equal restrictions.
Evaluating at a common point proves equality of the two original values.

`exists_locallyConstantSieveValue` uses the proved point coverage of a
covering sieve to obtain a section whose domain contains a given target
point. Its value at that point agrees with the value of every other sieve
section containing the point, by the intersection argument.
`locallyConstantSieveGlueFun` chooses this determined value separately at
each target point. It does not choose an arbitrary default coefficient
and therefore needs no nonemptiness assumption on `A`.
`locallyConstantSieveGlueFun_apply` proves recovery of every original
section value.

`locallyConstantSieveGlue` proves the constructed function locally
constant. Its restriction to each source domain of the sieve is exactly
that domain's supplied locally constant section. The companion
`AtlasTopology.LocallyRefines.isLocallyConstant_iff` applies because
covering means finite relative local refinement of the actual target
subset. This proves local constancy using the full quasinet neighborhood
condition. `locallyConstantSieveGlue_apply` gives the original restriction
formula for the resulting bundled section.

`locallyConstantPresheaf_isSheaf` proves existence and uniqueness of
amalgamation on every covering sieve. Existence is the constructed section
and its evaluation law. For uniqueness, every target point lies in a
sieve domain; any amalgamation has the given local value there and hence
equals the constructed section pointwise. Mathlib's equivalence of its
Type-valued sheaf formulations supplies `Presheaf.IsSheaf`.
`locallyConstantSheaf a A` packages the actual presheaf with that proof as
a Mathlib sheaf on the unchanged domain site.

The construction allows empty spaces, empty domains, empty covering
sieves when they cover, and empty coefficient sets. Value choice occurs
only at an actual target point, where point coverage provides a local
value. No separation, reducedness, valuation-nontriviality or
strict-polyradius condition is added to the published atlas.

This is an internal construction from `OriginalChartDomains`,
`OriginalDomainTopology`, the companion quasinet local-constancy
criterion, and Mathlib's locally constant functions and sheaf condition.
Its provenance is the explicit subset intersection, pointwise choice,
local-constancy detection and uniqueness arguments above. It supplies
constant-coefficient local function sections on this existing restricted
domain site. It does not identify that site with the full analytic or
étale site, identify this sheaf with a categorical constant-sheaf functor,
construct arbitrary sheaf descent, or instantiate the Harris tower.
