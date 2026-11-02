# Compatible full Harris coefficient sheaves on original CM scheme levels

Author: Worker 57.

This derived specialization constructs an actual inverse system of
small-etale sheaves of integral modules on the original CM scheme. The
objects use the full Harris lattice reductions and their original CM
coefficient torsors. Each transition is coefficient reduction followed by
the inverse of the proved comparison between these particular covers.
The section equation, its uniqueness property, invariant inclusions and
canonical trivializations are proved using the published generic
constructions.

## Inputs and retained premises

All fields, algebras, schemes, groups and module carriers have universe
zero. The inputs are `D : CentralSimpleUnitaryData E F A n`, where E is
totally real and F is CM, totally complex and quadratic over E; the
displayed algebra structures and scalar towers; an imaginary quadratic
field L with its embedding into F and chosen complex embedding `τ₀`;
and the CM-compatible Harris signature charts C. The algebra A is finite
over ℚ. The coefficient data are a number field K, a finite K-module W,
an algebraic representation `ρ` of
`D.rationalInvolution.baseChange K` on W, a rational finite place p,
a small CM level U, and a natural scalar m with `hm : m ≠ 0`.
Every nonnegative exponent is allowed.

The input assertions remain exactly those of the original CM scheme
construction: pullback-tensor comparison preservation, composition, unit,
associativity, unitor comparison and symmetry; Picard-zero pullback,
Mumford-square and universal base change; duality naturality, polarization
base change and relative finite Weil transitions; the rational
profinite-integer/adele comparison h; and the torsion finite-etale statement
htor. In particular, the exact premise is

```text
q : CMRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor.
```

It supplies representations of the fixed original CM moduli presheaf on
`ComponentwiseAdmissibleCMBaseCategory`, with the inherited componentwise
connected, locally Noetherian and geometric-point conditions. The scheme
tower is the existing `cmSchemeTower ... q`, constructed by Yoneda from
those presheaf maps. The additional premises are
`RelativeDualSchemeExistenceStatement.{0}`,
`RelativeDualSchemeGeometryStatement.{0}` and
`CMGeometricCoarseRigidity ... U.obj`. They are the displayed arguments
`existence`, `geometry` and `hRigid`. This unit does not discharge them.
It adds no supplied associated sheaf, desired transition, etaleness,
surjectivity or cover-comparison-isomorphism premise.

Write X for the original tower scheme at U, J for
`Scheme.smallEtaleTopology X`, and R for `HarrisCoefficientIntegers K p`.
R is the full integral coefficient product over all places of K above p,
as defined in the imported Harris lattice construction. It is a fixed
ring for the entire inverse system.

## Original covers and full coefficients

Let

```text
V_k = cmHarrisCoefficientLevel D ρ p U m hm k,
Q_k = SmallCMResidualGroup D U V_k,
Y   = cmHarrisCoefficientEtaleDiagram ... q U ρ p m hm
        existence geometry hRigid,
M   = cmHarrisCoefficientDiagram D ρ p U m hm.
```

The diagram Y is in the actual category `X.Etale` over the group functor
`cmHarrisCoefficientGroups D ρ p U m hm`. At index k its whole action
is the original `cmHarrisCoefficientTorsor ... k.unop`. Its underlying
scheme is the original tower scheme at `V_k`; its structural map and
transitions are the original forgetting maps. For a representative
`g : U.obj.subgroup`, its action is the original inverse-right
transporter, as proved in `HarrisTaylorCMCoefficientSchemes`.

The predicate `IsFiniteGeometricTorsor X (Y.action k)` follows from that
same original torsor under the retained premises. It comprises a finite
acting group, finite and scheme-surjective structural map, and unique
translation between separably closed field-valued points above the same
point of X. Etaleness is part of membership in `X.Etale`. Each Y object
also covers the final object of J, by the imported
`cmHarrisCoefficientEtaleDiagram_coversTop`.

M is an equivariant diagram of R-modules over exactly the same group
functor. Its carriers are the full lattice reductions; its group action
agrees pointwise with the existing quotient-ring coefficient action.
The transported U-action uses `g ↦ unop(g)⁻¹`. The action of the actual
sublevel `V_k` is proved trivial by equality with the action kernel in
`HarrisTaylorCMCoefficientDiagram`; it is not a separate factorization
assumption. For `f : i ⟶ j` in `ℕᵒᵖ`, the group transition sends the
class of g to the class of the same g, the cover transition is the
forgetting map from `V_i` to `V_j`, and the coefficient transition sends
the class of a lattice vector to the class of the same vector at the
lower power. The module carriers are finite and their transitions
surjective by the imported arithmetic results. The present system uses
these R-linear maps; the quotient rings vary with the exponent and are
not its common scalar ring.

## The sheaf system and its transitions

`cmHarrisCoefficientSystem` specializes
`etaleAssociatedVaryingSystem X Y hY M`, with hY supplied by
`cmHarrisCoefficientEtaleDiagram_isFiniteGeometricTorsor`. Its type is

```text
ℕᵒᵖ ⥤ Sheaf J (ModuleCat R).
```

Thus it includes actual sheaf morphisms and their identity and composition
laws. The published varying-cover proof obtains these laws from the
section equation, coefficient naturality and contravariant composition of
cover pullback, rather than assuming coherence of arbitrarily chosen
inverses.

`cmHarrisCoefficientSystem_obj` identifies the component at k with
`etaleAssociatedFunctor X (torsor k.unop).val` applied to `M.action k`.
These are integral-scalar associated sheaves. The earlier
`cmHarrisCoefficientSheaf` uses the exponent-dependent quotient ring as
scalars; equality of those objects of different sheaf categories is not
asserted here.

For an index arrow f, put

```text
A_i = Assoc(Y_i,M_i),
A_j = Assoc(Y_j,M_j),
B_f = Assoc(Y_i,res(Q.map f) M_j).
```

The actual cospan is `A_i --β_f--> B_f <--α_f-- A_j`.
Here β is `etaleAssociatedReduction`, induced by the actual coefficient
transition on the fine cover, and α is `etaleAssociatedComparison`,
induced contravariantly by the actual forgetting map and the identity
restricted coefficient map.

`cmHarrisCoefficientSystem_comparison_isIso` applies the published cover
comparison theorem to the original finite geometric torsors at i and j.
It proves invertibility of this exact α. The formula
`cmHarrisCoefficientSystem_map` identifies the transition with
`β_f ≫ α_f⁻¹`, using the published natural comparison isomorphism.
`cmHarrisCoefficientSystem_map_comparison` proves
`τ_f ≫ α_f = β_f` by the generic inverse cancellation equation.

## Inclusions, section characterization and trivializations

`cmHarrisCoefficientSystemInclusion k` is the canonical monomorphism
from `A_k` into the sheaf of constant coefficient sections over the
original cover `Y_k`. Its monomorphism instance is inherited from
`etaleAssociatedInclusion_mono`. The theorem
`cmHarrisCoefficientSystemInclusion_invariant` says that this inclusion
is invariant under the published diagonal action: coefficients act
covariantly, and cover pullback uses the inverse deck action. Both the
original inverse-right transporter and the inverse-unop coefficient
normalization are retained.

`cmHarrisCoefficientSystem_map_inclusion` specializes the actual section
equation:

```text
τ_f ≫ inc_j ≫ coverPullback(Y.map f)
  = inc_i ≫ productSheaf(Y_i).map(constantSheaf.map(M.map f)).
```

All maps in this formula are morphisms of R-module sheaves on J. The cover
map goes from the fine cover to the coarse cover, while its section
pullback has the opposite direction. The formula is a sheaf-morphism
equation, and hence holds on sections of every object of the actual
small-etale site. It uses the existing coefficient reductions and cover
maps, rather than a replacement diagram.

`cmHarrisCoefficientSystem_map_unique` proves that any sheaf morphism
from `A_i` to `A_j` satisfying that equation equals `τ_f`. It applies
`etaleAssociatedTransition_hom_ext` to the given equation and the proved
transition equation. The generic equality criterion uses invertibility
of α and monicity of the invariant inclusion on the fine cover.

`cmHarrisCoefficientSystemTrivialization k` is a canonical isomorphism
between the localization of `A_k` to the site over `Y_k` and the
localization of the constant sheaf with module `M_k`. It applies
`constantAssociatedTrivializationOfSplitting` to the proved
`etaleTorsorSectionSplitting` for this particular original torsor.
Together with the existing covering property and finiteness of `M_k`,
this gives explicit finite constant models on these covering objects.
No finite free module assertion is made.

`cmHarrisCoefficientSystemTrivialization_hom` identifies the isomorphism's
forward map with the canonical invariant-section evaluation.
The `_hom_eq` formula identifies that evaluation with the localized
invariant inclusion followed by tautological graph restriction
`productEvaluation`. Both identifications are definitional equalities.
Here localization means the existing `J.overPullback` functor to the site
over an object. It is not a claimed comparison with inverse image along
an arbitrary morphism of schemes.

## Sources, derivation and boundaries

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), Section 3, printed pp.306–308, PDF pp.8–10, supplies the
algebraic representation, integral lattice and inverse function
equivariance (3.7), followed by normal congruence quotient factorization
before (3.8). The registered source is
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, PDF pp.98–99, gives the
small-level moduli functor, right frame composition and normal-level
finite-etale Galois covers. III.2, printed pp.94–95, PDF pp.102–103,
constructs compatible torsion coefficients by inverse-equivariant
functions on components of varying covers and describes maps induced by
compatible cover and coefficient maps. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The supplied five-page author errata list identifies no correction to
these passages; that observation is limited to the supplied list.

The Lean construction is an internal categorical specialization of
[HarrisTaylorCMCoefficientSchemes](HarrisTaylorCMCoefficientSchemes.md),
[HarrisTaylorCMCoefficientDiagram](HarrisTaylorCMCoefficientDiagram.md) and
the published generic
[VaryingCoverInverse](../Coefficients/VaryingCoverInverse.md), with
trivializations from
[TrivializationFromSplitting](../Coefficients/TrivializationFromSplitting.md).
The generic proof is reused by Lean name and is not reimplemented.
The natural scalar m and exponent zero extend the positive prime-power
parameters of the motivating sources using the existing arithmetic
constructors.

This unit constructs compatible associated sheaves under the exact
geometric premises above. It does not prove applicable representability,
dual existence, coarse rigidity or source canonical-model comparisons.
It does not identify these sheaves with the source's component-function
description or another representation normalization, compare integral
and quotient scalar categories, establish independence of choices or
arbitrary scheme inverse-image compatibility, prove trivial kernel
intersection, or complete the lisse adic limit and cohomology construction.
Those remain separate obligations of the surrounding development.

The code and prose in this pair are by Worker 57, using published generic
interfaces. The pinned environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
