# The smooth-family representer over affine bases of finite type over the integers: proof

Module: `Langlands.AlgebraicGeometry.Picard.FiniteTypeSmoothFamilyAbelianRepresentabilityProof`.

Author: Worker 3233, for task `90a7704e-771a-4107-a91a-c67873dd035e`. The
published input theorems listed below were written by other workers.

## Result

The theorem
`Langlands.AbelianScheme.finiteTypeSmoothFamilyAbelianRepresentability`
proves the published proposition
`Langlands.AbelianScheme.FiniteTypeSmoothFamilyAbelianRepresentabilityStatement.{u}`
for every universe `u`. Its type is exactly that proposition, and it has no
hypotheses. The statement module
`Langlands.AlgebraicGeometry.Picard.FiniteTypeSmoothFamilyAbelianRepresentabilityStatement`
and its Markdown are unchanged.

Let `R : Type u` be any commutative ring of finite type over `ℤ`. `R` may be
nonreduced and need not be a domain. Let `A` be any Library abelian scheme over
`Spec R`. The theorem gives an actual abelian scheme `B` over `Spec R` and an
actual `L : RigidifiedFamily A B.X` with the unchanged
`IsUniversalSmoothFamilyOnQuasiSeparatedTests A L`. This predicate covers every
quasi-separated test in universe `u`, including nonreduced tests. The group
structure of `B` is the one that the Library's
`dualAbelianSchemeFromEvaluation` builds from the Poincaré classification.

## The proof

The theorem is one term:

```lean
theorem finiteTypeSmoothFamilyAbelianRepresentability :
    FiniteTypeSmoothFamilyAbelianRepresentabilityStatement.{u} :=
  finiteTypeSmoothFamilyAbelianRepresentability_of_picardSheafScheme
    Langlands.AlgebraicGeometry.Picard.finiteTypeAbelianPicardSheafScheme.{u}
```

It uses two inputs:

1. `Langlands.AlgebraicGeometry.Picard.finiteTypeAbelianPicardSheafScheme`
   (published module
   `Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafSchemeProof`,
   Task 5600). It proves
   `FiniteTypeAbelianPicardSheafSchemeStatement.{u}`: for the same `R` and
   `A`, the fppf Picard class sheaf `RelativePicard.classSheafPresheaf A.X.hom`
   is represented by a scheme over `Spec R`. The theorem has no hypotheses.
2. `Langlands.AbelianScheme.finiteTypeSmoothFamilyAbelianRepresentability_of_picardSheafScheme`,
   from the companion module
   `Langlands.AlgebraicGeometry.Picard.FiniteTypeSmoothFamilyAbelianRepresentabilityAssembly`
   in this contribution. It derives the target from
   `FiniteTypeAbelianPicardSheafSchemeStatement.{u}`.

The assembly theorem works as follows; its
[Markdown](FiniteTypeSmoothFamilyAbelianRepresentabilityAssembly.md) has the
details.

- A representation of the fppf Picard class sheaf is turned into a
  representation of the rigidified class presheaf. This uses the isomorphism
  given by the published `rigidifiedFppfComparison`, whose global-functions
  hypothesis is the published `smoothProperConnectedGlobalFunctions`. The
  published `RigidifiedLineBundle.representationUniversalBundle` then gives an
  actual universal rigidified family on the representing scheme.
- The published `finiteTypePicardZeroOpenLocus` gives a Picard-zero open
  locus, and `hasDualScheme_of_isPicardZeroOpenLocus` gives
  `HasDualScheme A`.
- The published `finiteTypeDualSchemeGeometry` (module
  `Langlands.AlgebraicGeometry.Picard.FiniteTypeDualSchemeGeometryProof`,
  Task 5599) shows that the chosen dual is smooth, proper and geometrically
  connected.
- `exists_isUniversalSmoothFamilyOnQuasiSeparatedTests_of_hasDualScheme`, from
  the companion module
  `Langlands.AlgebraicGeometry.Picard.SmoothFamilyUniversalOfPicardZeroUniversal`
  in this contribution, combines these. It uses the published
  `dualAbelianSchemeFromEvaluation` for the abelian-scheme structure,
  `poincareFamily_universal` for the universal Picard-zero family, and the
  published comparison `smoothFamilyPicardZeroComparison` between smooth-family
  and Picard-zero classes. Its
  [Markdown](SmoothFamilyUniversalOfPicardZeroUniversal.md) has the details.

## Checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` compiles
the two companion modules and this module with no errors or warnings. The
theorem's axioms are `propext`, `Classical.choice` and `Quot.sound`.

The import closure of this module does not depend on the target in a circular
way. Within that closure, only the statement module, this module and the
assembly module mention `FiniteTypeSmoothFamilyAbelianRepresentabilityStatement`.
No module in the closure mentions the shared
`SmoothFamilyAbelianRepresentabilityStatement`. All inputs are unconditional
published theorems, and none of them assumes a representer or a dual scheme.
