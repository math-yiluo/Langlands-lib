# Quotient-ring and integral-scalar Harris coefficient sheaves

Author: Worker 57.

This derived specialization compares two existing coefficient constructions on
the same original CM scheme. Restriction of scalars sends each original
quotient-ring coefficient sheaf canonically to the corresponding integral
component of `cmHarrisCoefficientSystem`. The comparison preserves both
invariant inclusions. Transporting the constructed integral transitions gives
an inverse system whose objects are exactly these restricted original sheaves,
together with a natural isomorphism to the integral system.

## Inputs and retained geometric premises

All field, algebra, scheme, group and module carriers have universe zero. The
inputs are the central-simple unitary data
`D : CentralSimpleUnitaryData E F A n`, with E totally real, F CM and
quadratic over E, and the displayed algebra structures and scalar towers.
A is finite over ℚ. There is an imaginary quadratic field L embedded in F,
a chosen complex embedding `τ₀` of L, and compatible Harris signature charts C.
The coefficient inputs are a number field K, a finite-dimensional K-module W,
an algebraic representation ρ of `D.rationalInvolution.baseChange K` on W,
a rational finite place p, a small CM level U, a natural scalar m and
`hm : m ≠ 0`. Every nonnegative exponent is allowed.

The arguments preserve all premises of
[HarrisTaylorCMCoefficientSystem](HarrisTaylorCMCoefficientSystem.md):
pullback-tensor comparison preservation, composition, unit, associativity,
unitor comparison and symmetry; Picard-zero pullback, Mumford-square and
universal base change; duality naturality, polarization base change and
relative finite Weil transitions; the rational profinite-integer/adele
comparison h; and the torsion finite-etale assertion htor. The exact
representability premise is

```text
q : CMRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor.
```

It concerns the fixed original moduli presheaf on
`ComponentwiseAdmissibleCMBaseCategory`, retaining its componentwise connected,
locally Noetherian and geometric-point conditions. The schemes and maps are
those of the existing Yoneda-derived `cmSchemeTower ... q`.
`RelativeDualSchemeExistenceStatement.{0}`,
`RelativeDualSchemeGeometryStatement.{0}` and
`CMGeometricCoarseRigidity ... U.obj` remain the explicit arguments
`existence`, `geometry` and `hRigid`. This unit does not prove these premises.
It adds no supplied scalar comparison, inverse system or transition
compatibility assumption.

## Rings, actions and component comparisons

Write X for that tower's scheme at U, J for its actual
`Scheme.smallEtaleTopology X`, and R for `HarrisCoefficientIntegers K p`.
R retains the full product of integral coefficient rings over every place of
K above p. Put

```text
I   = harrisCoefficientScalarIdeal K p m,
S_k = HarrisCoefficientReductionRing K p m k = R / I^k,
φ_k = Ideal.Quotient.mk (I^k),
V_k = cmHarrisCoefficientLevel D ρ p U m hm k,
Q_k = SmallCMResidualGroup D U V_k.
```

Let Y_k be the original `cmHarrisCoefficientTorsor ... k`. Its scheme is the
original fine scheme at V_k and its map to X is the original forgetting map.
The quotient group Q_k acts by the previously constructed inverse-right deck
action. The retained premises supply this same finite geometric torsor.
Let N_k be the S_k-module action `cmHarrisCoefficientAction D ρ p U m hm k`,
and let M_k be the R-module action at `op k` of
`cmHarrisCoefficientDiagram D ρ p U m hm`.
Both have the same full lattice-reduction carrier. Their action conventions
retain the original transport `g ↦ unop(g)⁻¹`.

`cmHarrisCoefficientActionRestrictIso` is an isomorphism of Q_k-actions
from N_k restricted along φ_k to M_k. It applies `Action.mkIso` to the
identity module isomorphism. The equivariance proof uses the existing
pointwise equality `cmHarrisCoefficientDiagram_action`; no new action
factorization hypothesis is introduced. The `_hom_hom` and `_inv_hom`
lemmas say that both underlying module morphisms are definitionally the
identity. These are equalities after scalar restriction, in one module
category.

Write

```text
F_k = sheafCompose J (ModuleCat.restrictScalars φ_k),
B_k = cmHarrisCoefficientSheaf ... k,
A_k = (cmHarrisCoefficientSystem ...).obj (op k).
```

Here B_k is the existing associated sheaf over S_k on the original torsor,
while A_k is the existing associated sheaf over R on that same torsor.
`cmHarrisCoefficientSheafRestrictIso` constructs

```text
e_k : F_k.obj B_k ≅ A_k.
```

Its first factor is the published `constantAssociatedRestrictScalarsIso`
at N_k and Y_k. Its second factor is the associated-sheaf functor applied to
the action isomorphism just constructed. The generic first factor proves
that scalar restriction commutes with the actual sheafified constant-module
construction and its invariant limit. It does not require a supplied
constant-sheaf comparison. The sheaf isomorphism is not asserted to be a
definitional identity: its constant-sheaf comparison is part of the
construction.

## Invariant inclusions

Let `incq_k` be the original `cmHarrisCoefficientInclusion ... k`, and
`incR_k` be `cmHarrisCoefficientSystemInclusion ... (op k)`.
Let c_k be `constantRestrictScalarsIso J φ_k` evaluated at the underlying
S_k-module of N_k. Both of the following are proved as equalities of
R-module sheaf morphisms:

```text
e_k.hom ≫ incR_k
  = F_k.map incq_k ≫ (productSheaf J Y_k.V).map c_k.hom,

e_k.inv ≫ F_k.map incq_k
  = incR_k ≫ (productSheaf J Y_k.V).map c_k.inv.
```

These are
`cmHarrisCoefficientSheafRestrictIso_hom_inclusion` and
`cmHarrisCoefficientSheafRestrictIso_inv_inclusion`.
The product targets are the actual constant coefficient section sheaves on
the same cover, with the canonical scalar comparison inserted. Thus both
formulas also hold on sections of every object of the small-etale site.

The proofs combine the published forward or inverse scalar-restriction
inclusion equation with `etaleAssociatedInclusion_natural` for the actual
action isomorphism. Since that action isomorphism has identity underlying
maps, functorial preservation of identities removes the extra constant and
product maps. Associativity then yields the displayed equations.
The coefficient action and inverse deck action in the diagonal invariant
condition are unchanged by these comparisons.

## An inverse system of the restricted original sheaves

`cmHarrisRestrictedCoefficientSystem` is an actual functor

```text
ℕᵒᵖ ⥤ Sheaf J (ModuleCat R).
```

It uses Mathlib's proved `Functor.copyObj` construction to transport the
integral system along the inverses of the e_k. Its `_obj` theorem gives
exactly `F_k.obj B_k` at `op k`. If `f : i ⟶ j` is an index arrow and
τ_f is the integral system's existing transition, its `_map` theorem is
the definitional equality

```text
σ_f = e_(i.unop).hom ≫ τ_f ≫ e_(j.unop).inv.
```

The identity and composition laws follow from `copyObj`; transitions are
constructed by this transport rather than taken as additional data.
The integral τ_f already uses the original coefficient reduction and the
inverse of the proved comparison between the original coefficient covers.
This unit transports those particular transitions. It does not posit
independently specified transitions between the varying scalar categories.

`cmHarrisRestrictedCoefficientSystemIso` is a natural isomorphism from
this restricted system to `cmHarrisCoefficientSystem`. It is the inverse
of the standard `isoCopyObj`. The `_app` theorem identifies its component
at k definitionally with `e_(k.unop)`. Its naturality therefore includes
the full transition compatibility

```text
σ_f ≫ e_(j.unop).hom = e_(i.unop).hom ≫ τ_f.
```

The fixed ring R is essential to putting all restricted components and
these maps in one sheaf category.

## Sources, derivation and scope

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), Section 3, printed pp.306–308, one-based PDF pp.8–10, gives the
algebraic coefficient representation, stable integral lattice and inverse
function-equivariance formula (3.7). The paragraph before (3.8) uses a normal
congruence quotient and finite free torsion coefficients. The registered
source is `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99,
gives the small-level moduli description, right frame composition and normal
finite-etale covers. III.2, printed pp.94–95, one-based PDF pp.102–103,
uses torsion lattice reductions on varying covers with inverse function
equivariance and compatible coefficient and cover maps. The registered
source is `harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The supplied five-page author errata list contains no correction to these
passages; this observation concerns only that supplied list.

The scalar comparison and transported system are internal deductions, not
theorems quoted from those passages. They reuse
[ConstantScalarRestriction](../Coefficients/ConstantScalarRestriction.md),
[HarrisTaylorCMCoefficientSheaf](HarrisTaylorCMCoefficientSheaf.md) and
[HarrisTaylorCMCoefficientSystem](HarrisTaylorCMCoefficientSystem.md),
with the latter's arithmetic and scheme diagrams. The generic comparison
is imported by Lean name. The allowed nonzero natural m and exponent zero
come from the existing arithmetic constructors and extend the sources'
positive prime-power parameters.

This unit proves scalar restriction and transport of an already constructed
conditional inverse system. It does not prove applicable representability,
dual existence, coarse rigidity or source canonical-model comparisons.
It does not identify the sheaves with the sources' component-function
description, prove independence of lattice or tower choices, compare
arbitrary scheme inverse images, assert free reductions or faithful
representations, prove trivial kernel intersection, or construct the
completed lisse adic object and its cohomology. No scalar-extension or
tensor-with-invariants comparison is asserted.

This pair is by Worker 57 using published generic results. The pinned
environment is Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
