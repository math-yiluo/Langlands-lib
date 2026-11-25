# Split root data from rank-one reducedness

This is a derived internal construction. Its inputs and mathematical content
come from the published Library modules `SplitRootReflectionReduction`,
`RootReducednessReduction`, `SplitWeylRationality` and
`RootDatumFiniteWeylAssembly`. The construction in
`SplitRootReflectionReduction` is adapted by making rank-one reducedness an
explicit hypothesis. No unconditional rank-one reducedness result is asserted.

At arbitrary universe `u`, the final theorem is

```lean
rootDatumExistence_of_rankOneReducedness
    (hrank : RankOneRootReducednessStatement.{u}) : RootDatumExistenceStatement.{u}
```

The conclusion retains the original field, group, torus and maximality
hypotheses of `RootDatumExistenceStatement`. It supplies a finite index type,
a reduced root datum on the actual character and cocharacter lattices,
the actual root set, and rational normalizer representatives of its
reflections. The hypothesis concerns the actual adjoint roots of every
connected reductive group with split maximal torus whose roots are pairwise
linearly dependent over the integers. It asserts that two such roots agree
up to sign. That hypothesis is proved independently from the rank-one central
cover (`rankOneRootReducedness_of_centralCover rankOneCentralCover`), and
`rootDatumExistenceIndependent` in `Reductive.RootDatumExistenceIndependent`
applies this conditional construction to it to give an unconditional
root-datum result.

## Full root kernel in the rank-one centralizer

`RankOneCentralizerDetection.kernelCentralizer_torusHom_eq_top_of_rankOneReducedness`
takes `hrank` and a split maximal torus `i` in a connected reductive group,
with actual root `α`. The existing generic cocharacter annihilating `α`
defines the represented dynamic centralizer `L`, with factored torus `t`.
The conclusion is `RelativeRoot.kernelCentralizer t α = ⊤`. This is an
equality of subgroup functors on all test schemes, for the full
scheme-theoretic character kernel.

Dynamic centralizer reductivity makes `L` connected reductive. The torus
`t` is maximal, `α` is one of its roots, and its roots are pairwise
integrally dependent. The proof applies `hrank` to this actual group and
torus, so each root of `L` is `α` or `-α`. The represented full-kernel
centralizer contains the torus and each root subgroup. Its tangent space
contains the zero weight space by maximal-torus self-centralization.
`range_eq_top_of_torus_and_rootSubgroups` therefore makes this subgroup all
of `L`. This is the step that replaces the use of the published
unconditional `rootReducedness` in the earlier reflection construction.

## Rational integral reflections

`SplitWeylRationality.exists_reflection_of_rankOneReducedness` also takes
`hW : SplitMaximalTorusWeylRationalityStatement.{u}`. It constructs, for
any actual root `α`, a rational normalizing point `n` and an actual integral
cocharacter `ν` satisfying

```text
latticePairing T α ν = 2
weylAction i n χ = χ - latticePairing T χ ν • α
```

for every character `χ`. The existing
`SplitWeylRationality.exists_nonidentityNormalizer` supplies a nonidentity
Weyl class in `L`. This helper uses an ordinary proper Borel quotient over
an algebraic closure and `hW` to descend its action. The rank-one Weyl-action
lemma makes this class negate `α`. The full-kernel result above places its
representative in the full-kernel centralizer.
`IsSplitTorus.existsUnique_coroot_of_mem_kernelCentralizer` then extracts
`ν`. Mapping the point from `L` to the ambient group preserves its action.

`SplitWeylRationality.reflectionData_of_rankOneReducedness` chooses such a
point and cocharacter for each actual root. This gives the published
`RelativeRootReflectionData i`, with its self-pairing and action fields.
Both `hrank` and `hW` remain explicit parameters of this definition.

## Root-datum assembly

`rootDatumExistence_of_rankOneReducedness` supplies `hW` from the published
`splitMaximalTorusWeylRationality`. It supplies full reducedness from
`rootReducedness_of_rankOne hrank dynamicCentralizerReductive` and the finite
Weyl-image instance from `splitTorusWeylImageFinite`. Finally it applies
`exists_rootDatum_of_reflectionData_of_finite_weylImage` to the constructed
reflection data. The resulting index type is the actual root subtype;
its finiteness and all root-datum axioms are provided by that assembly.

## Independence and scope

The new proof terms use the explicit `hrank`; they do not use the existing
`rootReducedness`, `RootReducedness.rankOneRootReducedness`,
`rootDatumExistence`, or the positive-root uniqueness construction. Some
imported modules also contain those declarations. Their presence in an
import is separate from their use as dependencies of these new terms.
A declaration audit outside the Library followed types and opaque values of the final
conditional theorem through 22,555 project declarations. It found no dependency
on the named excluded statements, the existing contaminated proofs, or the
projective-Borel and root-vector-line structural modules checked in that audit.
This module is a
conditional reduction and does not prove the independent rank-one
hypothesis by itself.
