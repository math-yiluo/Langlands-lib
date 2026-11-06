# From a geometric-point locus to the all-test Picard-zero criterion

`Langlands.AbelianScheme.PicardZeroGeometricOpenLocusBridgeStatement.{u}`
is a Prop-valued definition. It states the generic implication implemented
in Worker 390's shared draft revision 2 of
`FieldPicardZeroOpenLocusAssembly`.

The first premise is the existing proposition
`PicardZeroGeometricDetectionStatement.{u}`. For every arbitrary base
`S : Scheme.{u}`, abelian scheme `A/S`, parameter `P : Over S`, actual
rigidified family `L : RigidifiedFamily A P`, and supplied open subset
`U : P.left.Opens`, the second premise tests all maps
`s : Spec (CommRingCat.of K) ⟶ P.left`, where `K : Type u` is any
algebraically closed field. It asks for the equivalence

```text
IsPicardZeroFamily A (the actual relative pullback of L along s)
  ↔ Set.range s ⊆ U.
```

The actual slice morphism is
`Over.homMk s rfl : Over.mk (s ≫ P.hom) ⟶ P`. Pullback is exactly
`RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
(unitSection_comp A)` at that morphism. Thus the premise uses the
existing geometric-fibre translation-invariance predicate on the actual
rigidified pulled-back bundle, with its composite structure map to `S`.

The conclusion is the existing `IsPicardZeroOpenLocus A L U`.
It quantifies over every test `T : Over S` and actual slice morphism
`h : T ⟶ P`, and equates Picard-zero membership of the actual
`RigidifiedLineBundle.classifyingMap` with containment of
`Set.range h.left` in `U`. In particular, tests may be nonreduced or
non-quasi-separated. The base, parameter, fields, and tests all remain
in universe `u`.

No local finite type, universality, projectivity, representability,
existing dual scheme, or identity-component comparison is assumed.
The supplied open and its geometric-point criterion remain premises.
This proposition constructs no open set and proves neither the field
nor the relative openness theorem.

## Internal provenance and proof obligation

This is an internal compatibility statement extracted from Worker 390's
existing conditional assembly, rather than a theorem quoted from the
abelian-variety literature. Its imports supply the already defined
family predicate, actual classifier, and open-locus predicate. The
extraction changes no one of those definitions.

The intended proof uses a geometric point above every point of a scheme:
take the spectrum of the algebraic closure of its residue field and
compose with the canonical residue-field map. This detects range
containment in any subset. Geometric detection for the family pulled
back to a test `T` then reduces its Picard-zero condition to actual
further geometric-point pullbacks. Rigidified pullback coherence and
`RigidifiedLineBundle.classifyingMap_comp` compare these iterated
pullbacks with the direct composite into `P`. The supplied
geometric-point criterion gives range containment, hence the desired
all-test equivalence.

These steps are proof obligations for the separate exact proof of this
statement. This module defines the proposition and contains no proof of
it. Publication of its statement alone supplies no bridge theorem.
