# Original Harris CM geometric torsors from the dominant criterion

Author: Worker 57.

This internal adapter constructs the original residual action together with
a proof of the existing `Coefficients.IsFiniteGeometricTorsor` predicate.
It derives both etaleness of original forgetting and invertibility of its
original kernel comparison from the explicit named prerequisites. It also
constructs the same original action in the actual finite-etale cover category.

## Exact actions and hypotheses

Use the arithmetic parameters, inherited prerequisites, exact representation
family `R` and small normal inclusion `V ≤ U` of
`HarrisTaylorCMNormalSmoothEtale`. Write `X_U` and `X_V` for the original
represented schemes, `p : X_V ⟶ X_U` for the original normal forgetting map,
and `Q = SmallCMResidualGroup D U V`. The quotient is the actual
`U.obj.subgroup ⧸ V.obj.subgroup.subgroupOf U.obj.subgroup`.
The original quotient action uses inverse-right frame composition, in the
existing opposite finite adelic group.

The four additional explicit inputs are
`RelativeDualSchemeExistenceStatement.{0}`,
`RelativeDualSchemeGeometryStatement.{0}`,
`CMGeometricCoarseRigidity ... U.obj` and
`DominantUnramifiedEtaleStatement.{0}`. All arithmetic and tensor, Picard,
duality, polarization, Weil, adelic-comparison and torsion prerequisites
listed in the imported cover module remain inputs. In particular this
adapter does not prove exact representability, either relative-dual
assertion, source rigidity or the generic criterion.

The kernel comparison is exactly
`representedCMNormalKernelComparison ... R U V hVU`, from the actual
scheme coproduct of copies of `X_V` indexed by `Q` to the actual
self-pullback of `p`. On summand `g` its projections are identity and
the original residual translation. No arbitrary comparison is supplied.

## Constructed torsor and finite-etale action

`representedCMNormalGeometricTorsor_of_dominantCriterion` first applies
`representedCMNormalProjection_etale_of_dominantCriterion` to derive
`Etale p`. It then applies
`representedCMNormalKernelComparison_isIso_of_dualGeometry` to derive
invertibility of the exact kernel comparison. With these instances, the
published `representedCMNormalGeometricTorsor` supplies the direct subtype

```text
{Y : Action X_U.Etale Q // Coefficients.IsFiniteGeometricTorsor X_U Y}.
```

The existing predicate requires a finite acting group, a finite and
scheme-surjective structural map, and unique residual translation between
every pair of separably closed field-valued points with equal projections.
Etaleness is already part of the small-etale action object. The imported
torsor proof derives finiteness from projectivity and etaleness,
surjectivity from original CM frame-class lifts and the dual assertions,
and unique geometric transport from the exact kernel comparison isomorphism.
No finiteness, flatness, etaleness, surjectivity, comparison invertibility or
torsor proof for `p` is an additional input to the new construction.

`representedCMNormalFiniteEtaleAction_of_dominantCriterion` derives
`Etale p` in the same way, then uses the existing
`representedCMNormalFiniteEtaleAction` to return
`Action (FiniteEtale.Cover X_U) Q`.

Each construction has `_left`, `_hom` and `_ρ_left` theorems identifying
its fine scheme, original structural map and each underlying original
residual action map. All six equations are proved by `rfl`.

The entry `cmNormalGeometricTorsor_of_dominantCriterion` and the parallel
`cmNormalFiniteEtaleAction_of_dominantCriterion` use exactly
`chosenCMLevelRepresentation ... q`, which defines `cmSchemeTower ... q`.
Their base is that chosen tower's actual coarse scheme, their source is its
actual fine scheme, and their structural map is its direct map at
`smallCMInclusion D hVU`. The same six reflexive equations are supplied for
these chosen constructions. The original schemes, map and action are
preserved through the adapters.

## Provenance and retained scope

This is an internal composition of the named imported Library constructions.
The source conventions and stronger assertion are Harris and Taylor,
*The Geometry and Cohomology of Some Simple Shimura Varieties* (2001),
III.1, printed pp.90–91, especially p.91, one-based PDF pp.98–99. The
registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The passage gives the moduli classes, right frame action, finite-etale
forgetting and normal `U/V` Galois-cover assertion. The supplied author
errata list was read and contains no correction to this cited passage;
this observation is limited to that list.

The represented category remains
`ComponentwiseAdmissibleCMBaseCategory` over the original `Spec F`.
Applicable existence, the full source-moduli comparison, source rigidity,
the generic criterion and canonical-model geometry remain obligations.
The output is the existing geometric-torsor input for coefficient descent;
it supplies no sheaf, local-system comparison or descent theorem.

All code and prose in this pair are by Worker 57. The pinned environment
is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
