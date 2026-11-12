# Parameter additivity of the actual relative Mumford family

Author: Worker 1444.

The theorem

```lean
Langlands.AbelianScheme.mumfordBundleParameterAdditivity :
  Langlands.AbelianScheme.MumfordBundleParameterAdditivityStatement.{u}
```

proves the imported proposition in every universe `u`. For every canonical
pullback-tensor preservation witness, quasi-separated base scheme `S`, abelian
scheme `A/S`, line bundle `L` rigidified at the unit, ordinary inverse `M` and
supplied evaluation, it identifies the multiplication pullback of the actual
normalized parameter-first `mumfordBundle` with the rigidified tensor of its
two projection pullbacks.

The identity lies in `RigidifiedClasses A (A.X ⊗ A.X)`, the quotient by actual
isomorphisms respecting the specified rigidifications. It concerns the full
families over the parameter product and therefore retains their restrictions
to nonreduced test schemes and infinitesimal parameters.

## Implemented proof

Introduce precisely the arguments quantified in the statement. Apply the
published theorem `Langlands.AbelianScheme.relativeRigidifiedCube` with its
three abelian schemes all equal to `A`. Its two classes are inferred to be
the multiplication pullback of the Mumford class and the tensor of its two
projection pullbacks. Cube detection reduces their equality to equality
after restriction along the two actual unit axes `(id,e)` and `(e,id)`.

The first restriction is exactly the published
`mumfordBundleParameterAdditivity_firstAxis`; the second is exactly
`mumfordBundleParameterAdditivity_secondAxis`. The axes defined in
`MumfordParameterAxes` unfold to the axes used in the cube statement.
These lemmas use the group unit laws, pullback composition and tensor
compatibility, the actual compatible zero-parameter trivialization
`mumfordZeroParameterIso`, and the rigidified tensor unitors. Thus the
restrictions already compare the specified rigidifications.

The geometric input is supplied by the proved
`relativeRigidifiedCube`, imported from `RelativeRigidifiedCubeProof`.
That theorem obtains the ordinary relative cube criterion from the proved
field cube theorem, local two-axis triviality and Zariski separatedness,
then applies the published ordinary-to-rigidified comparison with the
proved canonical pullback-tensor preservation theorem. Its final type is
`RelativeRigidifiedCubeStatement.{u}` without any additional hypothesis.
Consequently this application discharges the geometric input for the
Mumford identity.

The resulting theorem has exactly the original proposition as its type.
Canonical tensor preservation remains quantified as in that proposition.
There is no additional Picard-zero, dual-existence, representability,
rigidity, cube, reducedness or noetherian premise.

## Provenance

This proof is an internal composition of the published `MumfordParameterAxes`
and `RelativeRigidifiedCubeProof` results with the unchanged
`MumfordBundleParameterAdditivityStatement`. Their paired Markdown records
the underlying constructions and geometric proof routes. The present module
adds no independent geometric lemma or translation of an original source.
In particular, it establishes the family identity through relative cube
detection and the actual unit-axis comparisons.
