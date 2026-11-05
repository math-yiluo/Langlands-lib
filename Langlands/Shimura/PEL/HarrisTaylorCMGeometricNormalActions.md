# Original residual actions on the actual geometric CM levels

Author: Worker 57.

This derived construction transports the original represented residual action
through the actual field-base-change functor defining the geometric CM tower.
It retains the existing geometric fine level and its normal forgetting map.
Under the original named finite-etale prerequisites it lifts this action to
the already constructed geometric finite-etale cover and makes the published
canonical cover comparison equivariant.

## Data and conventions

The arithmetic parameters are the original totally real field `E`, CM field `F`
quadratic over `E`, central simple unitary datum `D`, imaginary quadratic `L`
inside `F`, embedding `τ₀`, and CM-compatible signature charts `C`.
The tensor-pullback preservation, composition, unit, associativity, unitor
comparison and symmetry propositions; Picard-zero pullback, Mumford square
and universal base change; duality naturality, polarization base change,
relative finite Weil transition, rational profinite-integer/adele comparison
and torsion finite-etaleness inputs remain explicit. So does the exact
`q : CMRepresentabilityStatement ...`.

All constructions use the identical `chosenCMLevelRepresentation ... q`
witnesses. Write `X_U` for `cmSchemeTower ... q` at U, `Xbar_U` for
`cmGeometricSchemeTower ... q` at U, and `π_U` for the existing
`cmGeometricProjection ... q` at U. The geometric schemes are the existing
fiber products with `Spec (AlgebraicClosure F)` over `Spec F`, along
`cmGeometricFieldMap`. No new representing witnesses are chosen here.

Fix `hVU : V.obj.subgroup ≤ U.obj.subgroup` and normality of
`V.obj.subgroup.subgroupOf U.obj.subgroup`. The group used throughout is exactly
`SmallCMResidualGroup D U V`, the existing quotient of U by V. Normality is
inside U. The representative action is the existing inverse-right tower
convention encoded by `smallCMNormalInverseArrow D U V hVU g`.

## The action on the same geometric fine level

`cmGeometricNormalQuotientOverAction` maps the published
`representedCMNormalQuotientBaseAction` for the chosen representation through
the admissible-base inclusion followed by `Over.pullback cmGeometricFieldMap`.
Its `_V` theorem identifies the result's object with the existing geometric
level V over `Spec (AlgebraicClosure F)`, by reflexivity. The group laws come
from the original action through `Functor.mapAction`.

`cmGeometricNormalQuotientAction` then forgets only that field structure.
Its `_V` theorem identifies its scheme with `Xbar_V`. Its `_mk` theorem gives
the action of every quotient representative:

```text
ρbar([g]) = geometricSchemes.map (smallCMNormalInverseArrow ... g).
```

Both identities are reflexive. This is an action on the previously defined
geometric tower, rather than an action on a replacement scheme.

`cmGeometricNormalQuotientAction_projection` proves
`ρbar(g) ≫ π_V = π_V ≫ ρ(g)` for every residual element. The proof uses quotient
induction and the existing projection's naturality at the original
inverse-right level arrow. `cmGeometricNormalQuotientAction_over` proves that
the action preserves the actual structure morphism to the geometric field,
using `Over.w`.

Write `pbar` for `geometricSchemes.map (smallCMInclusion D hVU)`.
`cmGeometricNormalProjection_invariant` proves `ρbar(g) ≫ pbar = pbar`.
The implementation first lifts the published original normal-forgetting
identity to the slice category, using extensionality of slice morphisms.
It maps that equality through the same field-base-change functor and then
forgets to schemes; functor composition and slice-composition identities
give the displayed equation.

`cmGeometricNormalQuotientProjection` bundles `π_V` as a morphism to the
original scheme action. `cmGeometricNormalQuotientForgetting` bundles `pbar`
as a morphism to the trivial action on `Xbar_U`. These use exactly the two
preceding equivariance identities.

## Action in finite-etale covers and canonical equivariant comparison

This part additionally retains `RelativeDualSchemeExistenceStatement.{0}`,
`RelativeDualSchemeGeometryStatement.{0}`, the exact coarse-level
`CMGeometricCoarseRigidity ... U.obj`, and
`DominantUnramifiedEtaleStatement.{0}`. These are the published original
cover's named inputs. The generic criterion has the existing Library proof
`Langlands.AlgebraicGeometry.DominantUnramifiedEtaleProof.dominantUnramifiedEtale`;
the API here continues to take the named proposition explicitly.

`cmGeometricNormalFiniteEtaleAction_of_dominantCriterion` has as its object
exactly the published `cmGeometricNormalFiniteEtale_of_dominantCriterion`.
For each residual element it bundles `ρbar(g)` as a morphism over `Xbar_U`,
using normal-forgetting invariance. Extensionality first in the full
subcategory and then in the slice reduces its monoid laws to the already
constructed scheme action's laws.

Its `_V`, `_left`, `_hom` and `_ρ_left` theorems identify, by reflexivity, the
exact cover, its source `Xbar_V`, its map `pbar`, and each underlying action
map `ρbar(g)`. The ambient `FiniteEtale.Cover` is the existing full subcategory
of schemes over the base whose maps are finite and etale. This packaging
adds no surjectivity condition.

`cmGeometricNormalFiniteEtaleActionPullbackIso` is an isomorphism of actions
in `FiniteEtale.Cover Xbar_U`. Its target is the result of applying
`(FiniteEtale.pullbackFunctor π_U).mapAction` to the published original
`cmNormalFiniteEtaleAction_of_dominantCriterion`.

The underlying isomorphism is precisely the already published
`cmGeometricNormalFiniteEtalePullbackIso`. The proof supplies its equivariance
to `Action.mkIso`. Full-subcategory and slice extensionality reduce this to
equality of scheme maps into the pullback. After `pullback.hom_ext`, the
first-projection equation is the proved equivariance of `π_V`, and the
second-projection equation is the proved invariance of `pbar`. The generic
pullback-functor projection formulas and the published comparison's two
projection formulas perform these reductions. The `_hom_hom` and `_inv_hom`
theorems state, by reflexivity, that forgetting equivariance recovers the
identical published comparison and its inverse.

## Original source and retained obligations

The contextual source is Harris and Taylor, *The Geometry and Cohomology of
Some Simple Shimura Varieties* (2001), III.1, printed pp.90–91, one-based PDF
pp.98–99, especially p.91 for the moduli problem, inverse-right action,
normal-level Galois cover and finite-etale maps; and III.2, printed p.96,
PDF p.104, for the geometric base change used in cohomology.
It is registered as `harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The book's imaginary quadratic E, CM F and totally real F+ correspond to
this module's L, F and E.

The explicit functorial action on the existing geometric schemes and the
equivariant canonical cover comparison are internal deductions from the
published original action, geometric tower and cartesian cover comparison.
They are not additional displayed source assertions. The earlier source
audit found no matching correction in the supplied author
publication-with-errata list; no fresh or exhaustive errata audit is claimed.

Applicable exact representability under the original source hypotheses,
the named dual assertions, source rigidity, full moduli comparison,
canonical-model geometry and coefficient descent are not established by
this module. It supplies this conditional geometric action and cover
comparison; the host task remains incomplete.

All code and prose in this pair are by Worker 57, using only published imports.
The pinned environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
