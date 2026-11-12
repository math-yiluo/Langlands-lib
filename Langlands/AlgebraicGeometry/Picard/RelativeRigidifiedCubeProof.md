# Relative cube detection for actual rigidified families

Author: Worker 2057.

The main theorem is

```lean
Langlands.AbelianScheme.relativeRigidifiedCube :
  Langlands.AbelianScheme.RelativeRigidifiedCubeStatement.{u}
```

It imports the published statement unchanged and retains the arbitrary
universe `u`. For every quasi-separated base scheme `S`, abelian schemes
`A`, `B`, `C` over `S`, and actual rigidified family classes `q`, `r` over
`B.X ⊗ C.X`, equality after pulling back along `(id, e_C)` and `(e_B, id)`
implies `q = r`. The classes are the Library quotient by
rigidification-compatible isomorphism of actual rank-one locally free
module sheaves on the full relative space.

The module also proves the intermediate ordinary criterion

```lean
Langlands.AbelianScheme.relativeCubeTriviality :
  Langlands.AbelianScheme.RelativeCubeTrivialityStatement.{u}
```

For three abelian schemes over any quasi-separated base, an actual line
bundle on `A.X ⨯ (B.X ⨯ C.X)` is trivial if its restrictions to the three
full faces through the unit sections are trivial.

## Implemented proof

Apply the helper reduction supplied in `FieldToRelativeCubeReduction`,
`relativeCubeTriviality_of_fieldCubeTriviality` to the published
`Langlands.AlgebraicGeometry.Picard.fieldCubeTriviality`. This proves the
ordinary relative criterion with no additional hypotheses.

The reduction uses
`RelativeCubeAssembly.nonempty_iso_structureSheaf_of_faces` with the proved
local two-axis theorem `localTwoAxisTriviality` and the proved Zariski
separatedness theorem `rigidifiedClassesZariskiSeparated`. In that assembly,
the three face trivializations give triviality on every field fibre through
the field cube theorem. After base changing the first two factors to the
third, local two-axis triviality produces full open neighbourhoods on which
the bundle is trivial. The first face supplies a rigidification. Zariski
separatedness glues the resulting rigidified class equalities, and
forgetting the rigidification recovers the ordinary module-sheaf
trivialization.

Next apply the helper
`relativeRigidifiedCube_of_relativeCubeTriviality` to that ordinary
criterion. This reduction invokes the published
`rigidifiedClasses_eq_of_ordinaryCubeTriviality` with the proved
`Langlands.Scheme.Modules.pullbackTensorComparisonIsIso`. Its difference
bundle is trivial on the three full faces: the given rigidifications supply
one face and the two unit-axis equalities supply the other two. Ordinary
cube triviality gives a carrier isomorphism, and rigidification adjustment
makes it compatible with the original rigidifications. It therefore
identifies the two actual quotient classes.

The displayed reductions keep all these inputs explicit in their own
types. Here every input is supplied by a proved theorem. The final
`relativeRigidifiedCube` has exactly the imported proposition as its type.
The proof uses the full schemes and sheaves, including nilpotents, with no
noetherian, reducedness, projectivity, representability, dual-existence or
Picard-zero premise.

## Provenance

This is a derived assembly of the published `FieldCubeTrivialityProof`,
`RelativeCubeAssembly` and `RelativeCubeDualComparison` modules, composed
through the supporting `FieldToRelativeCubeReduction` pair supplied with
this proof. Their paired Markdown describes the geometric arguments and
source comparisons. In particular, the relative assembly uses local
two-axis triviality to pass from field fibres to full neighbourhoods,
rather than discarding the nilpotent structure of the base. This module
introduces no independent geometric lemma or source translation.
