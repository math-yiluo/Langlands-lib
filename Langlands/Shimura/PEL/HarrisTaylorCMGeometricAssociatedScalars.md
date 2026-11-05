# Quotient-ring coefficients on exact geometric CM torsors

Author: Worker 57.

This internal specialization constructs quotient-ring coefficient sheaves directly
on the existing exact geometric CM coefficient torsors. Restriction of scalars
identifies them with the components of the published integral associated system.
The comparison preserves invariant inclusions and actual local evaluation.
Transport of the existing transitions supplies an inverse system of these
restricted quotient sheaves and a simultaneous trivialization on each source
cover, with the original full-lattice coefficient reductions.

## Inputs and retained premises

All arithmetic, group, scheme and module carriers have universe zero. The input
`D : CentralSimpleUnitaryData E F A n` has E totally real, F CM and quadratic
over E, the displayed algebra structures and scalar towers, and A finite over
ℚ. An imaginary quadratic number field L embeds in F; a complex embedding
`τ₀ : L →+* ℂ` and the compatible Harris signature charts C are fixed.
The coefficient input is a number field K, a finite-dimensional K-module W,
an algebraic representation ρ of `D.rationalInvolution.baseChange K` on W,
a rational finite place p, a small CM level U, and a natural m with `hm : m ≠ 0`.
Every nonnegative exponent is allowed, including zero.

The construction retains these explicit premises:

- `pullbackTensorComparisonIsIsoStatement`,
  `PullbackTensorCompositionStatement`, `PullbackTensorUnitCoherenceStatement`,
  `ExplicitPullbackTensorAssociativityStatement`,
  `TensorMonoidalLeftUnitorComparisonStatement` and `PullbackTensorSymmetryStatement`;
- `PicardZeroPullbackStatement`, `MumfordBundlePicardZeroStatement`,
  `PicardZeroUniversalBaseChangeStatement`, `DualAbelianBaseChangeNaturalityStatement`
  and `PolarizationBaseChangeStatement`;
- `RelativeFiniteWeilTransitionStatement`,
  `h : Global.RationalProfiniteIntegerAdeleComparison` and
  `htor : TorsionFiniteEtaleStatement`.

The precise representability premise is

```text
q : CMRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor.
```

The same q supplies the previously constructed representing objects and the
geometric tower. The arguments
`existence : RelativeDualSchemeExistenceStatement`,
`geometry : RelativeDualSchemeGeometryStatement` and
`hRigid : CMGeometricCoarseRigidity ... U.obj` remain explicit.
These premises are not proved in this unit. The exact geometric finite torsors
already use the published dominant-unramified-etale criterion proof. No output
sheaf, scalar comparison, trivialization or transition law is an extra premise.

Write

```text
X = (cmGeometricSchemeTower ... q).obj U,
J = Scheme.smallEtaleTopology X,
R = HarrisCoefficientIntegers K p,
I = harrisCoefficientScalarIdeal K p m,
S_k = HarrisCoefficientReductionRing K p m k = R / I^k,
φ_k = Ideal.Quotient.mk (I^k),
M = cmHarrisCoefficientDiagram D ρ p U m hm,
V_k = cmHarrisCoefficientLevel D ρ p U m hm k,
Q_k = SmallCMResidualGroup D U V_k.
```

R is the full product of integral coefficient rings over all places of K above p.
The coefficient carrier is the existing full stable-lattice reduction; no single
place is selected. Let N_k be the S_k-module Q_k-action
`cmHarrisCoefficientAction D ρ p U m hm k`, and let Y_k be
`cmHarrisGeometricCoefficientTorsor ... k`. This is the exact geometric fine
scheme at V_k with its existing map to X and inverse-right deck action.
The coefficient and opposite-group conventions are unchanged.

Let A denote `cmHarrisGeometricAssociatedCoefficientSystem ...`, and let
`incR_k` be its invariant inclusion at `op k`. Both are imported from
[HarrisTaylorCMGeometricAssociatedSystem](HarrisTaylorCMGeometricAssociatedSystem.md).

## Direct quotient-ring association

`cmHarrisGeometricAssociatedCoefficientSheaf k` constructs

```text
B_k = (etaleAssociatedFunctor X Y_k.val).obj N_k
    : Sheaf J (ModuleCat S_k).
```

The imported functor first makes the coefficient module sheaf constant by
sheafification, then forms the diagonal invariant limit of coefficient-valued
sections on Y_k. Thus B_k is an actual sheaf on the small-etale site of X.
`cmHarrisGeometricAssociatedCoefficientInclusion k` is its inclusion into
`productSheaf J Y_k.val.V` of the constant sheaf on N_k.V. It is monic by the
published associated-inclusion theorem. Its `_invariant` theorem states
`incq_k ≫ diagonal(g) = incq_k` for every g in Q_k, with the existing coefficient
and inverse-deck actions.

`cmHarrisGeometricAssociatedCoefficientTrivialization k` is an isomorphism
between B_k and the constant N_k.V sheaf after localization on Y_k.val.V.
It specializes `constantAssociatedTrivializationOfSplitting`, using the proved
`etaleTorsorSectionSplitting` for the exact finite geometric torsor. Its `_hom`
formula identifies the forward map as the localized invariant inclusion followed
by `productEvaluation` on that same cover. This specifies the actual evaluation
map as well as its invertibility.

## Scalar restriction and invariant inclusions

Let F_k be `sheafCompose J (ModuleCat.restrictScalars φ_k)`.
The published `cmHarrisCoefficientActionRestrictIso` compares N_k restricted
along φ_k with `M.action (op k)`. Its underlying forward and inverse module maps
are the identity on the original quotient carrier. This pure coefficient
comparison is reused; it does not depend on an arithmetic or geometric base
scheme.

`cmHarrisGeometricAssociatedCoefficientSheafRestrictIso k` constructs

```text
e_k : F_k.obj B_k ≅ A.obj (op k).
```

It composes `constantAssociatedRestrictScalarsIso` for Y_k with the associated
functor applied to that published action comparison. The first factor includes
the canonical comparison for sheafified constant modules and the invariant
limit, so e_k is not asserted to be a definitional identity.
Let

```text
c_k = (constantRestrictScalarsIso J φ_k).app N_k.V.
```

The forward and inverse inclusion theorems prove

```text
e_k.hom ≫ incR_k
  = F_k.map incq_k ≫ (productSheaf J Y_k.val.V).map c_k.hom,

e_k.inv ≫ F_k.map incq_k
  = incR_k ≫ (productSheaf J Y_k.val.V).map c_k.inv.
```

Their proofs combine the published scalar-restriction inclusion equations with
naturality of the associated inclusion for the identity-on-carrier action
comparison. Preservation of identities by the constant and product functors
removes its extra underlying maps; associativity yields the displayed formulas.
These are sheaf-morphism equalities on the same exact geometric cover.

## Restricted inverse system and actual evaluation

`cmHarrisGeometricAssociatedRestrictedCoefficientSystem` is the functor H from
ℕᵒᵖ to `Sheaf J (ModuleCat R)` obtained with `Functor.copyObj` from A and e_k.
Its object and map lemmas identify

```text
H.obj k = F_(k.unop).obj B_(k.unop),
H.map f = e_(i.unop).hom ≫ A.map f ≫ e_(j.unop).inv  (f : i ⟶ j).
```

The functor laws follow from the proved transport construction.
`cmHarrisGeometricAssociatedRestrictedCoefficientSystemIso` is the natural
isomorphism H ≅ A given by `isoCopyObj`; its component at k is exactly
`e_(k.unop)`. The transitions are therefore the particular transitions
transported from A. No independently specified maps between the varying S_k
module categories are assumed. A already uses original coefficient reduction
and the inverse of the proved exact geometric cover comparison.

Let L_k be the R-module sheaf localization on Y_k.val.V, and let Lq_k be the
S_k-module localization on the same object. Let t_k be the integral evaluation
isomorphism `cmHarrisGeometricAssociatedCoefficientTrivializationAlong` at
`op k` and the identity lift into Y_k.val.V. Let tq_k be the quotient-ring
trivialization above. Scalar restriction on the slice site commutes
definitionally with localization: both use the same componentwise restriction
of module scalars. Hence
`cmHarrisGeometricAssociatedRestrictedCoefficientTrivialization k` constructs

```text
r_k = (sheafCompose (J.over Y_k.val.V) (ModuleCat.restrictScalars φ_k)).mapIso tq_k
        ≪≫ L_k.mapIso c_k.
```

The local scalar-comparison theorems prove

```text
L_k.map e_k.hom ≫ t_k.hom = r_k.hom,
L_k.mapIso e_k ≪≫ t_k = r_k,
L_k.map e_k.inv ≫ r_k.hom = t_k.hom.
```

The first proof localizes the forward invariant-inclusion formula and applies
`productEvaluation_natural` to c_k.hom. Thus the comparison preserves actual
invariant evaluation. Equality of the isomorphisms follows by `Iso.ext`; the
inverse formula follows from the inverse identities and functoriality.

## A simultaneous source-cover trivialization

For k in ℕᵒᵖ, let L^k be localization on the existing cover
`(cmHarrisGeometricCoefficientEtaleDiagram ...).obj.obj k`.
`cmHarrisGeometricAssociatedRestrictedCoefficientSourceSystem k` is

```text
Under.forget k ⋙ H ⋙ L^k.
```

`cmHarrisGeometricAssociatedRestrictedCoefficientSourceTrivialization k`
compares this with `cmHarrisGeometricConstantCoefficientSourceSystem ... k`.
Its first factor is the natural scalar-system comparison whiskered with
`Under.forget k` and L^k. Its second factor is the published source-cover
evaluation trivialization of A. For `i : Under k`, its forward component is
exactly

```text
L^k.map e_(i.right.unop).hom
  ≫ etaleAssociatedEvaluationAlong X covers M i.right (covers.obj.map i.hom).
```

The `_transition` theorem is the naturality of this constructed isomorphism.
For every `f : i ⟶ j` in Under k it gives

```text
L^k.map (H.map f.right) ≫ u_j
  = u_i ≫ L^k.map ((constantSheaf J (ModuleCat R)).map (M.obj.map f.right)).
```

Thus every reachable transition becomes the original full-lattice reduction
on the constant coefficient diagram, with the actual geometric forgetting
maps used in evaluation. In the opposite natural-number order these reachable
indices have exponent at most k.unop. This is a simultaneous trivialization of
that finite reachable diagram; no fixed finite cover is asserted to trivialize
all exponents.

## Internal provenance and remaining scope

This pair is an internal deduction from published Lean constructions, with no
new external-source assertion. It reuses the exact geometric covers of
[HarrisTaylorCMGeometricCoefficientDiagram](HarrisTaylorCMGeometricCoefficientDiagram.md),
the integral associated system and source evaluation of
[HarrisTaylorCMGeometricAssociatedSystem](HarrisTaylorCMGeometricAssociatedSystem.md),
the pure action comparison of
[HarrisTaylorCMCoefficientScalars](HarrisTaylorCMCoefficientScalars.md), and
[ConstantScalarRestriction](../Coefficients/ConstantScalarRestriction.md).
The local proof follows the already published argument in
[HarrisTaylorCMCoefficientLocalScalars](HarrisTaylorCMCoefficientLocalScalars.md)
on these exact geometric torsors. Only published results and Worker 57's own
published proof pattern are reused; there is no reused unpublished draft.

The named representability, relative dual existence/geometry and coarse-rigidity
premises remain obligations of their respective developments. This module does
not compare direct association with the existing arbitrary scheme inverse-image
system `cmHarrisGeometricCoefficientSystem`. Such a comparison requires the
separate arbitrary-morphism descent result. It makes no claim about finite free
coefficient modules, independence of choices, completed lisse adic objects,
scalar extension, tensor-with-invariants, source canonical-model identification,
or completion of the host task.

The pinned environment is Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
