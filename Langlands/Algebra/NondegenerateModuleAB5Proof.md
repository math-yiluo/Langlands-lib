# Proof of source AB5 for actual nondegenerate modules

Authors: Worker 6 and Worker 1213. Worker 6 authored the shared proof
pair. Worker 1213 reused that draft, checked it against the original
source and published prerequisites, added all six distinct-universe
permutations, and prepared the proof for independent review.

This proof establishes the entire published target
`Langlands.Algebra.NondegenerateModuleAB5Statements.AB5Assertions`.
It imports the published statement, actual subobject comparison,
integer-unitization adapter and actual direct sum without changing their
Lean or Markdown interfaces.

The governing source is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, I.6 Proposition
and proof, printed pp.27–28 / PDF pp.33–34, especially the displayed AB5
formula on printed p.28. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1213 recomputed this hash, read both retained source pages in
full, and visually checked the formula on PDF p.34. The source AB5
convention in Appendix A.VI.2, printed p.263 / PDF p.269, was also read
in full and visually checked. No separate project errata note for this
registered 2026 source was present in the published Library notes. Renard proves the law
by the two set inclusions for modules. The implementation follows this
setwise route through the actual subobject and stable-subgroup comparisons.
Its general nonunital-ring scope is the extension documented by the target.

The private helper `inf_iSup_of_directed` treats an arbitrary ordinary
unital module. Mathlib's `Submodule.mem_iSup_of_directed` identifies
membership in the directed supremum with membership in one term.
A vector in N intersect that supremum therefore belongs to N intersect
one term and hence to the supremum of intersections. In the other
direction, every intersection is below N intersect the original supremum.
No distributive lattice assumption for all submodule families is used.

`directedSubobjectDistributivity` locally selects the canonical action of
`Unitization Int A` on the same original carrier. It composes the actual
`NondegenerateModuleCat.subobjectOrderIso hA M` with
`NonUnitalSubmodule.intUnitizedOrderIso`. Both maps keep the actual
original range as a subset. The latter only adds canonical integer scalars;
it does not replace or assume the input A-action. The composite order
isomorphism e preserves and reflects the existing categorical order and
its intersection. The prospective sum U is the inverse image under e of
the supremum of e(F(i)). Order-isomorphism transport of the ordinary
supremum proves U is the first required least upper bound. Preservation
of intersection and the helper equality show that e(N intersect U)
is the supremum of e(N intersect F(i)); transporting this least upper
bound back proves the second required assertion. Both sums exist as
conclusions. No complete lattice structure on categorical subobjects is
assumed or installed.

`sourceAB5` adds the coproduct clause using the actual finite-support
cofan and `cofanIsColimit` from `NonUnitalModuleDirectSum`. Thus the
categorical sum retains its original singleton inclusions and finite
common-idempotent nondegeneracy proof. The carrier is max uI uM,
while the directed-subobject theorem has arbitrary independent index
universe uI and fixed carrier uM. The coefficient universe uA is
independent throughout. `ab5Assertions` conjoins the two exact targets;
full unapplied target examples retain all three universes and specialize
to index-above-carrier and both unequal ring/carrier orders, together
with all six permutations of the three distinct levels 0, 1 and 2.

Local finite type
(the source's AB6), filtered-colimit exactness, and the remaining whole
book remain separate obligations.
