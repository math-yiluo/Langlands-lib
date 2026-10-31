# Exactness of the actual nondegenerate functors

Authors: Workers 6 and 490. Worker 6 supplied the shared proof draft;
Worker 490 checked it against the published prerequisites, added the two
named inclusion-exactness directions and their complete universe checks,
and prepared this explanation.

The theorem `Langlands.Algebra.nondegenerateModuleExactnessStatement`
proves the entire independently published closed proposition
`Langlands.Algebra.NondegenerateModuleExactnessStatement.{uA,uM}`.
For every original `A : Type uA`, `[NonUnitalRing A]` and
`hA : IsIdempotented A`, its four conclusions are:

1. The actual inclusion `nondegenerateInclusion.{uA,uM} A` preserves homology.
2. The actual part functor `nondegeneratePartFunctor.{uA,uM} hA` preserves homology.
3. For every short complex `S` in `NondegenerateModuleCat.{uA,uM} A`,
   `(S.map (nondegenerateInclusion A)).Exact ↔ S.Exact`.
4. For every ambient short complex `S` in `NonUnitalModuleCat.{uA,uM} A`,
   `S.Exact → (S.map (nondegeneratePartFunctor hA)).Exact`.

Here `PreservesHomology` is Mathlib's certificate for preserving kernels
and cokernels, expressed as limits and colimits of an arrow paired with
the zero arrow. The proof imports the published additive structures,
abelian construction, closure, adjunction and restricted-range proof by
their Lean names. The statement and its imported interfaces are unchanged.

`nondegenerateInclusion_preservesHomology` obtains subobject and quotient
closure from `nondegenerateModuleClosureStatement`. Mathlib's
`ObjectProperty.preservesKernels_ι` and `preservesCokernels_ι` then give
the two preservation fields for the actual full-subcategory inclusion.
This uses the proved concrete closure properties; it does not invoke an
unrestricted abelian-subcategory criterion.

`nondegeneratePartFunctor_preservesEpimorphisms` starts with an ambient
epimorphism `f`. The published `IntegerUnitization.equivalence A` sends
it to an epimorphism in `ModuleCat (Unitization ℤ A)`. Mathlib's
`ModuleCat.epi_iff_surjective` therefore supplies surjectivity of the
original underlying additive map. The published
`NonUnitalModuleHom.restrictNondegeneratePart_surjective` supplies
surjectivity on the actual nondegenerate subgroups. For an element `y`
of the target part, choose such a restricted preimage `x`. Evaluating a
cancellation equation at `x` makes two maps agree at `y`; extensionality
for the full-subcategory morphisms and original intertwiners proves the
required epimorphism.

The unitization is an internal categorical adapter. Its extension action
is `(n,a) • m = n • m + a • m` on the same additive group, and its functor
keeps the original underlying additive map. Restriction along the original
ring inclusion recovers the original action. Thus this step adds no
coefficient compatibility assumption or unit-action law to the original
modules, even when `A` itself has an identity.

`nondegeneratePartFunctor_preservesHomology` installs the published
`NondegenerateModuleCat.abelian A hA`, whose preadditive projection is
exactly the inherited pointwise addition on original Hom groups. The
actual adjunction `nondegeneratePartAdjunction hA` has inclusion on the
left and the part functor on the right, so its right-adjoint preservation
theorem supplies all limits, hence kernels. Together with the preceding
epimorphism result, Mathlib's
`Functor.preservesHomology_of_preservesEpis_and_kernels` supplies homology
preservation, including cokernels.

`nondegenerateInclusion_exact_map_iff` uses the proved abelian structure
and inclusion homology preservation with
`ShortComplex.exact_map_iff_of_faithful`. Its two directions are also
exported as `nondegenerateInclusion_map_exact` and
`nondegenerateInclusion_exact_of_map_exact`.
`nondegeneratePartFunctor_map_exact` uses part-functor homology
preservation with `ShortComplex.Exact.map`. The closed theorem assembles
the four conclusions in the published order. These are seven reusable
named interfaces in addition to the closed theorem.

All abelian, closure, adjunction and preservation certificates are
discharged inside the proof from published constructions and results.
None is an extra premise of the closed theorem. The categories retain
the original additive, associative nonunital actions, actual pointwise
additive intertwiners, actual full-subcategory inclusion and actual
restriction functor. Ring universe `uA` and carrier universe `uM` remain
independent. The Lean file checks the closed theorem and all seven
complete unapplied helper interfaces at arbitrary independent universes
and at both unequal assignments `(0,1)` and `(1,0)`. The hypotheses permit
zero rings, zero actions and trivial carriers; they require no field,
commutativity, nontriviality, dimension or finiteness assumption.

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original module conventions are printed pp.5–6/PDF11–12. I.1.2,
printed p.7/PDF13, defines the nondegenerate full subcategory and the
largest nondegenerate part and asserts submodule and quotient closure.
Printed p.8/PDF14 states exactness of taking nondegenerate parts. Its
preimage argument adjusts an ambient preimage `x` to `e • x`, where the
idempotent `e` fixes the target vector; the imported restricted-surjectivity
proof implements that argument.

The homology-preservation certificates, the route through the actual
adjunction, and faithful-inclusion reflection of exactness are internal
categorical consequences of these constructions and Mathlib's theorems.
The separate source issue with the unrestricted Appendix A.VI.1
abelian-subcategory criterion is recorded in
[the source-discrepancy note](../../notes/renard/appendix-a-corrections.md);
the published abelian proof used here includes the necessary zero and
finite-product closure. This proof does not discharge the separately
owned ambient categorical range/kernel comparison, completion, other
adjunctions, scalar comparisons or remaining book content.
