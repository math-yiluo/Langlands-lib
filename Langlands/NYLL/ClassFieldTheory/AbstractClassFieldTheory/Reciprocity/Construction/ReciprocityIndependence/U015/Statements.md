# NYLL finite extensions between finite intermediate fields

Worker 353, 14 November 2026.

## Source and correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`. The registered source
`nyll-classfieldtheory-fbd320cd-supplement` has content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original copyright and author header is retained. The license and notice
remain at `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

The source module is
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean`.
Unit M033.015 is `ClassFormation.FiniteIntermediateField.finite_extension_of_le`:
its docstring is at lines 247–248, its complete declaration type at lines
249–256, and its proof at lines 257–269. Its adapted statement target is
`Langlands.NYLL.ClassFormation.FiniteIntermediateField.finite_extension_of_leStatement`.

Source M004.002, `CyclicCohomology.extensionSubgroup`, is at lines 51–54
(docstring 47–50) of
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean` at the same pin.
The source expression `extensionSubgroup X Y hYX` abbreviates exactly
`Y.toSubgroup.subgroupOf X.toSubgroup`. Both occurrences in this target
reduce to that Mathlib expression, as required by Task 5849.

## Reused Library target

The definition's body applies the published declaration
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.finite_extension_over_intermediateStatement`,
imported from
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Statements`.
Its Lean/Markdown pair is at
`Langlands/NYLL/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension/Statements.lean`
and the same-stem `.md`. The declaration appears at lines 92–102 in Library
commit `9d71020c4b80abb41dbf8102ded7d93202edf495`.

That existing declaration adapts M040.025,
`ClassFormation.FiniteGaloisSubextension.finite_extension_over_intermediate`,
from the pinned
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean`,
lines 248–255 (docstring 247). Its entire telescope and conclusion are
definitionally identical to M033.015 after unfolding M004.002. The existing
target calls the last instance `hPKfinite`; this M033.015 alias retains the
original M033 name `hPfinite` and passes it explicitly.

This reuses the existing proposition by Lean name. Keeping a small alias
also supplies the required M033.015 declaration name at the required path.

## Exact proposition

At the arbitrary source universe `u`, the full telescope is, in order:

1. implicit `{G : Type u}`;
2. instances `[Group G]` and `[TopologicalSpace G]`;
3. implicit `{P M K : ClosedSubgroup G}`;
4. explicit `(hPK : P.toSubgroup ≤ K.toSubgroup)`;
5. explicit `(hMK : M.toSubgroup ≤ K.toSubgroup)`;
6. explicit `(hPM : P.toSubgroup ≤ M.toSubgroup)`;
7. instance `[hPfinite : Finite
   (K.toSubgroup ⧸ P.toSubgroup.subgroupOf K.toSubgroup)]`.

The body is an application of the reused M040.025 target to all these
parameters. Unfolding that target and M004.002 gives exactly
`Finite (M.toSubgroup ⧸ P.toSubgroup.subgroupOf M.toSubgroup)`.
Thus finite index of `P` in `K` implies finite index of `P` in the
intermediate subgroup `M`. In the source's contravariant field terminology,
a finite extension `P | K` remains finite over the intermediate field `M`.
These are coset spaces. No normality, quotient group structure, topological
group law, profiniteness or degree data is assumed.

The source theorem's namespace does not introduce a parameter of the
`FiniteIntermediateField` structure. The earlier definitions in that
namespace and the lexical degree-data dependencies are absent from this
declaration's type. The imported published module includes those supporting
definitions, but the alias introduces no such parameters.

## Modification record

1. Prefix `ClassFormation.FiniteIntermediateField` with `Langlands.NYLL`.
2. Replace the source theorem by a `def` returning `Prop` and append
   `Statement` to its name. Its body reuses the published M040.025 target
   by applying it to the complete source telescope. Omit the source proof
   at lines 257–269.
3. Expand M004.002 in the finite-coset hypothesis to its exact
   `Subgroup.subgroupOf` body described above. The reused proposition's
   conclusion reduces to the corresponding expansion for `M` and `P`.
   Retain all three explicit containment parameters in their original
   positions and pass them, together with `hPfinite`, to M040.025.
4. Replace the source's two broad NYLL imports with the published
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Statements`
   module supplying the reused target. Remove the unused
   `KummerTheory` and `CyclicCohomology` namespace openings.
5. Retain the source universe, binder kinds and order, named finiteness
   instance, noncomputable section and mathematical docstring. Add the
   module-level attribution and this correspondence record.

The file adds no data construction or instance. The M004.002 expansion
discharges the abbreviation dependency. The reused declaration is a
proposition definition; no proof is supplied by this alias.

## Validation and scope

The private development comparison `TelescopeCheck.lean` reconstructs the
complete source-spelled statement using a local copy of the original
M004.002 abbreviation. It checks by `rfl` equality of the entire
unapplied target with both this reconstruction and the reused M040.025
constant. These comparisons include the full telescope and body together
at arbitrary universe `u`.

Checks use environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`.
Both comparisons compiled with zero errors and warnings. Target inspection
reports a definition at universe `u` with `statement_returns_prop: true`
and only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

The target is a proposition definition awaiting a separate proof task.
It supplies no proof of a class-formation, reciprocity or host comparison
statement. Development compilation and comparison do not constitute
independent semantic acceptance or publication.
