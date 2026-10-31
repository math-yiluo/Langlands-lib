# Actual unramified stages and compatible finite models

Author: Worker 60.

This helper module constructs the directed family used in the proof of
`Langlands.ClassFieldTheory.Local.inertiaFixedFieldNormSurjectivity`.
All declarations are in `Langlands.ClassFieldTheory.Local.InertiaNormDescent`.
`U` abbreviates the actual fixed field of canonical absolute inertia; `Stage`
indexes actual finite Galois intermediate extensions whose canonical absolute
ramification index equals that of the original p-adic field.

The published `Langlands.PadicField.inertiaFixedFieldUnramifiedExhaustion`
supplies containment, nonemptiness from the empty set, and coverage from a
singleton. For directedness, apply exhaustion to the union of the images of
finite bases of two stages. Expanding an arbitrary element in either basis
proves inclusion of each whole stage in the new stage. Thus `stage_directed`
and `stage_cover` concern the literal pulled-back subfields of `U`.

`stageEquiv` removes the nested subtype while preserving the element in the
original closure. `stageOverBase` and `stageAlgebra` supply the canonical
algebra over the original field; `stageAlgEquiv` is an algebra equivalence,
and `stage_finite` transports finite dimensionality through it.

`finite_models` derives characteristic zero from the p-adic scalar map, then
specializes the published `Langlands.FieldTheory.finiteTowerDirectedUnionDescent`
to this directed family. The output retains the same three witnesses, all
three degrees, Galoisness, all disjointness and compositum clauses, the finite
sets and the literal commuting scalar square. The algebra on the top field
is the composite of the original two scalar maps. Explicit canonical algebra
and scalar-tower instances match the imported theorem's structures.

This is internal assembly for the finite-model argument in Serre, *Local Fields*
(1979), V.4, Lemmas 6–7 and Proposition 7, printed pages 89–90 / PDF pages
96–97, registered `serre-1979-local-fields`. The construction uses the named
published proofs; it asserts no new unramified arithmetic premise. Worker 60
read these original pages and the Local Fields section of the official 2019
corrections, registered `serre-book-corrections-2019`, PDF pages 2–3. No listed
correction affects printed pages 88–90. No unpublished peer draft was reused.
