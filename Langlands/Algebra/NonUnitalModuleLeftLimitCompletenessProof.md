# Closedness, density and completeness of actual left-compatible module families

Authors: Worker 735 and Worker 1149. Worker 735 supplied the Lean proof and
initial explanation. Worker 1149 audited the original source, the published
carrier and topology interfaces, and this explanation, and compiled and
inspected the complete proof in the pinned environment.

This is the proof of the published proposition
`Langlands.Algebra.NonUnitalModuleLeftLimitDensityCompletenessTheorem`
from module `Langlands.Algebra.NonUnitalModuleLeftLimitCompletenessStatements`,
prepared for exact-target proof task `87b298fb-b730-4673-87de-54e91cf5ff5a`.
The target and its imports are used by Lean name without changes, and the
proof adds no hypotheses. The proof follows the structure of Worker 6's
checked ring-family proof draft (`IdempotentedRingRightLimitCompletenessProof`,
shared under the whole-book task), adapted from right multiplication on
ring-valued families to the original left action on module-valued families.

The target uses the actual additive subgroup `leftCompatibleFamilies A M`,
its carrier `NonUnitalModuleLeftLimit A M` with the actual coordinate
uniformity `NonUnitalModuleLeftLimit.uniformSpace A M`, the actual canonical
additive map `NonUnitalModuleLeftLimit.canonical`, and the original-module
uniformity `nonUnitalModuleUniformSpace A M`. It holds at arbitrary
independent universes `uA` and `uM`. Closedness and completeness hold for
every original `NonUnitalRing A`, `AddCommGroup M` and `NonUnitalModule A M`.
Density needs only `IsIdempotented A`. The dense embedding needs
`IsIdempotented A` and `IsNondegenerate A M`. Zero rings, zero actions,
trivial carriers and noncommutative nonunital rings remain included.

## Closedness

`nonUnitalModuleLeftLimit_closedFamily` installs the discrete uniformity on
`M`. Its product uniformity on `Idempotent A → M` is, by definition,
`NonUnitalModuleLeftLimit.discreteProductUniformSpace A M`. The carrier of
`leftCompatibleFamilies A M` is the intersection of two families of sets:

- for each idempotent `e`, the fixed-point set `{x | e • x e = x e}`;
- for each pair `e ≤ f`, the coherence set `{x | e • x f = x e}`.

Coordinate evaluation is continuous on the product. The map `m ↦ e • m` is
continuous because `M` is discrete. Both sides of each equation are
therefore continuous maps into the discrete, hence Hausdorff, space `M`, so
each equality set is closed. Arbitrary intersections of closed sets are
closed, and so is the intersection of the two families. No local-unit,
directedness or nondegeneracy condition is used.

## Completeness

`nonUnitalModuleLeftLimit_complete` rewrites the actual family uniformity
along the published equality `NonUnitalModuleLeftLimit.uniformSpace_eq_subtype`.
That equality identifies it with the subspace uniformity of the compatible
families inside the discrete product. Discrete `M` is complete, so the
arbitrary product is complete. A closed subset of a complete space is
complete, and Mathlib's `IsComplete.completeSpace_coe` turns this into
`CompleteSpace` on the subtype. No completion or completeness certificate
is assumed.

## Density

`nonUnitalModuleLeftLimit_canonicalDense` assumes `IsIdempotented A`. Under
this hypothesis the published lemma `NonUnitalModuleLeftLimit.nhds_hasBasis`
gives, for each family `x`, a neighborhood basis indexed by idempotents `e`:
the sets `{y | y e = x e}`. Given `e`, the proof takes the original vector
`x e`. The `e`-coordinate of its canonical family is `e • x e`, which equals
`x e` by the fixed-point condition on `x`. So the canonical image of `x e`
lies in that basic neighborhood. The neighborhood-basis criterion for
closure (`mem_closure_iff_nhds_basis`) then puts `x` in the closure of the
canonical range. Module nondegeneracy is not used.

## Dense embedding

`nonUnitalModuleLeftLimit_canonicalDenseEmbedding` assumes both
`IsIdempotented A` and `IsNondegenerate A M`. It assembles Mathlib's
`IsDenseEmbedding` from three parts:

- the topological inducing property, from the published uniform inducing
  property `NonUnitalModuleLeftLimit.isUniformInducing_canonical`;
- dense range, from the density theorem above;
- injectivity, from the published `NonUnitalModuleLeftLimit.canonical_injective`,
  which uses nondegeneracy.

Both topologies are passed explicitly as those of
`nonUnitalModuleUniformSpace A M` and `NonUnitalModuleLeftLimit.uniformSpace A M`.
If the original-module uniformity were installed as an instance on `M`,
instance search would instead give the family carrier the subtype topology
of the product of copies of that topology, which is not the target's
codomain topology.

The final theorem `nonUnitalModuleLeftLimitDensityCompletenessTheorem_proof`
puts the four proofs together into the closed master target. Complete
unapplied checks keep both universes independent, and the master is checked
at the unequal assignments `(0,1)` and `(1,0)`.

## Source and provenance

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
At the end of I.1.3, printed p.9/PDF15, Renard proves density of a ring in
its limit of right-compatible families. For `f ≥ e`, the family minus the
image of its `f`-coordinate vanishes at `e`. Renard explicitly leaves
completeness to the reader. I.1.4 on the same page describes the completion
of a nondegenerate module as the inverse limit of the `e · M`, with
compatible families `m̄(e) ∈ e · M`, `e · m̄(f) = m̄(e)` for `e ≤ f`, and the
canonical map `m ↦ (e ↦ e · m)`. It says that the arguments of I.1.3 adapt
easily, and gives no separate module proof.

The density proof here applies Renard's argument at `f = e`, using the
left-image fixed-point condition. The closed-product proof of completeness
is an internal answer to the completeness question Renard leaves to the
reader. Closedness in the full discrete product, completeness and closedness
for arbitrary original modules, density without module nondegeneracy, and
the Mathlib `IsDenseEmbedding` formulation are internal. They are neither
numbered source results nor printed proofs attributed to Renard. The
provenance of the targets themselves is recorded in the statement Markdown.

## Checks and scope

The Lake build and declaration inspection compile against the published
target and imported constructions. Only `propext`, `Classical.choice` and
`Quot.sound` occur as axioms in the master proof. The target does not
request a uniform equivalence with `UniformSpace.Completion`, module
pseudometrics, Hom or scalar-action comparisons, a completion functor or
the smoothing/completion adjunction. Those remain separate units.
