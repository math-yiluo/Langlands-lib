# Fibres of the CM forgetting transition on connected tests

The module `Langlands.Shimura.PEL.HarrisTaylorCMNormalQuotientConnectedFibre`
proves

```
cmNormalSublevelConnectedFibre :
  CMNormalSublevelConnectedFibreStatement D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor
```

the statement of `Langlands.Shimura.PEL.HarrisTaylorCMNormalQuotientPremiseStatements`:
for small levels `U' ≤ U` with `U'` normal in `U`, an admissible test `T` with
connected underlying scheme, and fine classes `c₁ c₂` in
`(smallLevelClassPresheafTower …).obj U'` on `T` with the same image under the
forgetting transition `smallCMInclusion D hle`, some `g : U.obj.subgroup`
translates `c₁` to `c₂` by the inverse right translation
`smallCMNormalInverseArrow D U U' hle g`.

## Proof

1. Connected admissibility of `T.obj`. The test is connected and locally
   noetherian, so `admissibleCMBase_iff_dualGeometry` reduces `AdmissibleCMBase`
   to dual geometry of abelian schemes over it, supplied by the Library
   theorems `relativeDualSchemeExistence` and `relativeDualSchemeGeometry`.
2. Evaluation at a geometric point. `T` is nonempty, so
   `HarrisGeometricPoint.ofResidue` gives a geometric point `a` (the algebraic
   closure of the residue field at a chosen point), and a connected component
   `c` is chosen. The composite natural isomorphism
   `disconnectedClassTowerConnectedIso … T hp c ≪≫ unpointedClassTowerEvaluationIso … X a`
   identifies the Harris-level tower of the disconnected presheaf at `T` with
   the pointed tower `geometricClassTower … a` of normalized classes at the
   fixed point `a`. The values of the presheaf tower at `T` are the values of
   `disconnectedClassTower … T` at the levels, and its transitions are the
   tower maps at the underlying transporters, by definition.
3. Transport of the hypothesis. Naturality of this isomorphism at the inclusion
   transporter carries the equality of the coarse classes of `c₁` and `c₂` to
   the equality of the coarse classes of their images `x₁ x₂` in the pointed
   tower.
4. Transitivity at the point. The Library theorem
   `classMap_exists_normalTranslate` (module
   `Langlands.Shimura.PEL.HarrisTaylorCMClassTransitivity`) gives
   `g : U.obj.subgroup` with `mapClass (normalInverseArrow g) x₁ = x₂`. Its
   remaining arguments are the admissibility data of `T`: invertibility of
   torsion orders, finite étaleness of roots of unity, quasi-separatedness and
   positive pair additivity, and the finite fibres of `a`.
5. Return. Naturality at the inverse right translation and injectivity of the
   isomorphism at level `U'` give the required equality in the presheaf at `T`.

The elaboration of the definitional identifications in steps 2–5 is heavy, so
the theorem is checked with `maxHeartbeats` raised to 2000000.

## Sources

The statement is the description of the fibres of the finite étale Galois
covering `X_{U'} ⟶ X_U` with group `U/U'` in Harris and Taylor, *The Geometry
and Cohomology of Some Simple Shimura Varieties* (2001), III.1, printed p.91,
source `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`. The
proof is internal: it transports the pointed result
`classMap_exists_normalTranslate` through the Library's evaluation and
connected-component isomorphisms.
