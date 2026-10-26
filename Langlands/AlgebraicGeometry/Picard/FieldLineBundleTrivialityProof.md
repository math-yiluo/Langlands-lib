# Triviality of line bundles on a field spectrum

`Langlands.AlgebraicGeometry.Picard.fieldLineBundleTriviality` proves exactly
`Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityStatement.{u}`.
For every field `K : Type u` and actual locally free rank-one module sheaf
`L : LineBundle (Spec (CommRingCat.of K))`, it gives

```lean
Nonempty (L.obj ≅
  Langlands.Scheme.Modules.structureSheaf (Spec (CommRingCat.of K)))
```

The universe is arbitrary, and the theorem adds no hypotheses. It imports the
published statement and `Langlands.AlgebraicGeometry.Modules.PullbackUnit`,
using the existing line-bundle, structure-sheaf, and pullback-unit definitions
unchanged.

## Implemented proof

Write `X = Spec (CommRingCat.of K)`. The field spectrum has a distinguished
point and is a subsingleton. Apply `L.property` at that point to obtain a
trivializing neighborhood `U` and an isomorphism from the actual restriction
of `L.obj` to the structure sheaf on `U`. Every point equals the distinguished
point, so belongs to `U`; hence `U = ⊤`.

The inverse of `Scheme.Modules.restrictFunctorIsoPullback` changes this
restriction trivialization into an isomorphism `e'` from the pullback along
the top-open inclusion to the structure sheaf of the top-open scheme. Pull
`e'` back along `X.topIso.inv`. The isomorphism called `back` identifies the
double pullback of `L.obj` with `L.obj`: it composes `pullbackComp`,
`pullbackCongr X.toIso_inv_ι`, and `pullbackId`. Compose `back.symm` with the
pulled-back `e'` and `Langlands.Scheme.Modules.pullbackUnitIso` to obtain the
required global isomorphism.

This constructs an isomorphism of the actual module sheaves. It does not
assert a preferred or unique trivialization. No basis, sheaf-module
equivalence, tensor inverse, or algebraic closure is assumed.

## Internal provenance and authorship

This is an elementary internal consequence of the published local rank-one
definition, the topology of a field spectrum, and the existing restriction
and pullback comparisons. It is not presented as an explicit theorem from
an external source. The motivation recorded in the statement's companion
Markdown remains unchanged; this module proves only its field-spectrum
triviality proposition.

Worker 316 supplied the direct proof as the private `lineBundle_field_trivial`
helper in revision 1 of task `4db6f774-722f-405b-aeaa-8ab052f17c14`, in
`Langlands/AbelianScheme/FieldSymmetricMultiplicationPullbackProof.lean`.
Worker 367 extracted that helper into this minimal module, adapted it to
prove the exact published proposition, and wrote this proof documentation.
Worker 316 is a coauthor of the adapted proof. The unreviewed source draft
is provenance, not an imported dependency.
