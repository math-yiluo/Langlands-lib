# Associated full Harris coefficients on exact geometric CM levels

Author: Worker 57.

This module constructs the full integral-scalar coefficient system directly
from the exact geometric CM coefficient covers. It gives the invariant
inclusions, determines the transitions by their section equations, and
trivializes each finite reachable diagram by evaluation on its source cover.
The canonical comparison of geometric cover diagrams induces an isomorphism
of the entire associated coefficient systems.

## Inputs and retained premises

The arithmetic input is the universe-zero central simple unitary datum
`D : CentralSimpleUnitaryData E F A n`, with E totally real and F a CM field
quadratic over E, and the displayed algebra structures and scalar towers.
The algebra A is finite over ℚ. An imaginary quadratic number field L embeds
in F; the complex embedding `τ₀ : L →+* ℂ` and Harris signature charts C
are fixed.

The tensor premises are `pullbackTensorComparisonIsIsoStatement`,
`PullbackTensorCompositionStatement`, `PullbackTensorUnitCoherenceStatement`,
`ExplicitPullbackTensorAssociativityStatement`,
`TensorMonoidalLeftUnitorComparisonStatement` and
`PullbackTensorSymmetryStatement`. The Picard, duality and polarization
premises are `PicardZeroPullbackStatement`,
`MumfordBundlePicardZeroStatement`, `PicardZeroUniversalBaseChangeStatement`,
`DualAbelianBaseChangeNaturalityStatement` and
`PolarizationBaseChangeStatement`. The construction also retains
`RelativeFiniteWeilTransitionStatement`,
`h : Global.RationalProfiniteIntegerAdeleComparison` and
`htor : TorsionFiniteEtaleStatement`.

The argument `q : CMRepresentabilityStatement ...` is the exact existence
statement for the constructed CM moduli class presheaves. Both the original
scheme tower and its geometric base change use the same chosen representing
objects obtained from this q. The additional premises
`existence : RelativeDualSchemeExistenceStatement`,
`geometry : RelativeDualSchemeGeometryStatement` and
`hRigid : CMGeometricCoarseRigidity ... U.obj` are explicit. The geometric
torsors imported from
[HarrisTaylorCMGeometricCoefficientDiagram](HarrisTaylorCMGeometricCoefficientDiagram.md)
already use the published dominant-unramified-etale proof. No torsor,
coefficient sheaf, trivialization or desired comparison is an additional
output premise.

Fix a small CM level U, a number field K, a finite-dimensional K-module W,
an algebraic representation ρ of `D.rationalInvolution.baseChange K` on W,
a rational finite place p, and `m : ℕ` with `hm : m ≠ 0`. Put

```text
R = HarrisCoefficientIntegers K p,
I = harrisCoefficientScalarIdeal K p m,
M = cmHarrisCoefficientDiagram D ρ p U m hm,
G = cmHarrisCoefficientGroups D ρ p U m hm.
```

R is the full product of integral coefficient rings at all places of K over p.
The component M_k is the full stable-lattice reduction modulo I^k, with R
retained as scalar ring at every exponent. Its transitions are the original
lattice-representative reductions. G_k is the residual group at the full
coefficient kernel level `V_k = cmHarrisCoefficientLevel ... k`.
The opposite-group coefficient convention and inverse-right deck actions
are inherited without modification.

Write `Xbar = (cmGeometricSchemeTower ... q).obj U`,
`Jbar = Scheme.smallEtaleTopology Xbar`, and
`Ybar = cmHarrisGeometricCoefficientEtaleDiagram ...`.
Thus Ybar_k is the existing exact geometric scheme at V_k, over Xbar by
the original geometric forgetting map. The construction reuses the proved
finite geometric torsor property of every Ybar_k.

## Associated sheaves and their actual transitions

`cmHarrisGeometricAssociatedCoefficientSystem`, denoted F below, is

```lean
etaleAssociatedVaryingSystem Xbar Ybar coverProperty M
```

It is a functor `ℕᵒᵖ ⥤ Sheaf Jbar (ModuleCat R)`.
The `_obj` lemma identifies each component with the associated sheaf for
the existing exact geometric torsor and the original action M_k. The
`_map` lemma identifies a transition as coefficient reduction followed
by the inverse of the proved cover-comparison isomorphism.
`_comparison_isIso` specializes that invertibility result, and
`_map_comparison` recovers exactly the original coefficient reduction
after composition with the comparison leg.

`cmHarrisGeometricAssociatedCoefficientSystemInclusion k`, written ι_k,
is the actual invariant inclusion into coefficient-valued sections on
Ybar_k. It is a monomorphism. The `_invariant` theorem says that this
inclusion is fixed by the published diagonal action, combining the
coefficient action with the inverse-right action on the cover coordinate.

For `f : i ⟶ j`, let `b_f = Ybar.obj.map f` and let `c_f` be the map
between constant sheaves induced by `M.obj.map f`. The theorem
`cmHarrisGeometricAssociatedCoefficientSystem_map_inclusion` gives

```text
F.map f ≫ ι_j ≫ coverPullback b_f
  = ι_i ≫ (productSheaf Ybar_i).map c_f.
```

The theorem `_map_unique` proves that this equation determines the actual
transition uniquely among all maps F_i → F_j. It applies the published
transition extensionality theorem and the displayed equation. Thus the
maps are compatible invariant-section reductions on the exact cover
diagram.

## Evaluation and simultaneous source-cover trivialization

For an etale object Z over Xbar, let
`L_Z = Jbar.overPullback (ModuleCat R) Z`.
Constants below are formed on Jbar and then localized by L_Z.
For any actual map `a : Z ⟶ Ybar_k`,
`cmHarrisGeometricAssociatedCoefficientTrivializationAlong k a` is an
isomorphism

```text
L_Z(F_k) ≅ L_Z(constantSheaf_Jbar(M_k)).
```

Its `_hom` lemma identifies the forward map with
`etaleAssociatedEvaluationAlong Xbar Ybar M k a`.
This first localizes the invariant inclusion and then evaluates along
the graph of the given lift into the cover. Invertibility is inherited
from the proved geometric torsor section-splitting construction.

The theorem `cmHarrisGeometricAssociatedCoefficientSystem_evaluationAlong`
proves, for every transition f and map `a : Z → Ybar_i`,

```text
L_Z.map (F.map f) ≫ eval_j(a ≫ b_f)
  = eval_i(a) ≫ L_Z.map c_f.
```

For a fixed `k : ℕᵒᵖ`, an object of `Under k` is an arrow k → i.
`cmHarrisGeometricAssociatedCoefficientSourceSystem k` restricts F
to these objects and localizes on Ybar_k.
`cmHarrisGeometricConstantCoefficientSourceSystem k` applies the same
restriction and localization to the original constant coefficient
diagram. The definition
`cmHarrisGeometricAssociatedCoefficientSourceTrivialization k`
is an isomorphism between these entire diagrams.
Its `_hom_app` lemma identifies the component at i with evaluation along
the exact geometric cover map `Ybar.obj.map i.hom`.
Its `_transition` equation is naturality of this same evaluation:
every transition becomes the original full-lattice coefficient reduction.

In `ℕᵒᵖ`, the exponents reachable from k are those at most k.unop.
No fixed finite cover is asserted to trivialize all larger exponents.
Taking Z = Ybar_k and a the identity gives a trivialization of F_k
on its actual cover; that cover covers the final object by the imported
geometric coefficient-diagram result.

## Comparison induced by the canonical cartesian cover diagram

Let `π = (cmGeometricProjection ... q).app U`, let Y be the original
`cmHarrisCoefficientEtaleDiagram ...`, and put

```text
Ypull = (etaleTorsorDiagramPullback π G).obj Y.
```

This generic pullback of covers permits an arbitrary base morphism.
Let `e : Ybar ≅ Ypull` be the already published
`cmHarrisGeometricCoefficientEtaleDiagramPullbackIso`.
Its components are the canonical cartesian comparisons of the exact
geometric scheme levels, and it respects all cover transitions and actions.

The entry definition
`cmHarrisGeometricAssociatedCoefficientSystemCoverIso` is

```text
etaleAssociatedVaryingSystem Xbar Ypull pulledProperty M ≅ F.
```

It evaluates the existing contravariant
`etaleAssociatedVaryingSystemCoverIso` at the same coefficient diagram M.
The `_hom_app` and `_inv_app` lemmas identify its components with
`etaleCrossCoverMap` along e.hom and e.inv respectively, with the identity
map on the unchanged coefficient action. The `_transition` theorem is
naturality for every specified system transition.
Finally, `_hom_inclusion` proves that the forward comparison commutes
with the actual invariant inclusions and pulls back only the cover
coordinate along e.hom. The proof first uses the component formula and
then the published pure-cover-change inclusion identity.

## Provenance and remaining scope

This is an internal specialization of
`HarrisTaylorCMGeometricCoefficientDiagram`,
`Coefficients.VaryingCoverInverse`,
`Coefficients.VaryingCoverLocalTrivialization` and
`Coefficients.VaryingSystemCoverChange`, using the unchanged full
`HarrisTaylorCMCoefficientDiagram`. The generic invariant, transition,
evaluation, section-splitting and contravariant cover-change proofs
provide the intrinsic laws. The exact geometric covers provide their
geometric premises. The contribution adds no external-literature claim;
original-source provenance remains with the imported arithmetic and
geometric constructions.

The existing `cmHarrisGeometricCoefficientSystem` is defined instead by
applying the arbitrary scheme inverse-image functor to the original
coefficient system. This module does not identify that functor with
association on pulled-back covers. It therefore does not identify F
with that existing inverse-image system. The arbitrary-morphism descent
comparison remains a separate generic obligation; etaleness of π is
neither assumed nor proved here.

Exact source-moduli existence, rigidity, canonical-model geometry and
the other named premises remain obligations. There is no new
quotient-ring scalar comparison, inverse-limit construction, lisse-adic
theorem or cohomology assertion. This focused construction does not
complete the host task.
