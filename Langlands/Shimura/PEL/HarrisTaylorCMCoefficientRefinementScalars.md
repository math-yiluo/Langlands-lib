# Integral scalars under original CM coefficient refinement

Author: Worker 57.

Construct the integral coefficient sheaf independently on any original CM
normal cover below the full coefficient-kernel level. Construct its comparison
with the corresponding component of the existing integral inverse system.
Prove that original cover refinement commutes with restriction from the
coefficient quotient ring to the fixed integral ring. Both comparisons preserve
the actual invariant-section inclusions.

## Arithmetic inputs and exact geometric premises

The arithmetic carriers and coefficient modules have universe zero. Retain the
totally real number field `E`, CM number field `F`, quadratic extension `E → F`,
algebra `A` with the displayed scalar structures and towers, and
`D : CentralSimpleUnitaryData E F A n`. Assume `Module.Finite ℚ A`. Retain an
imaginary quadratic number field `L`, its algebra map into `F`, its chosen
complex embedding `τ₀`, and the Harris signature charts `C`.

Let `K` be a number field, `W` a finite `K`-module, and `ρ` an algebraic
representation of `D.rationalInvolution.baseChange K` on `W`. Fix a rational
finite place `p`, a small CM level `U`, a natural scalar `m` with
`hm : m ≠ 0`, and an exponent `k : ℕ`.

All the named geometric premises of the imported
[HarrisTaylorCMCoefficientRefinement](HarrisTaylorCMCoefficientRefinement.md)
and [HarrisTaylorCMCoefficientScalars](HarrisTaylorCMCoefficientScalars.md)
are retained:

- `pullbackTensorComparisonIsIsoStatement`,
  `PullbackTensorCompositionStatement`,
  `PullbackTensorUnitCoherenceStatement`,
  `ExplicitPullbackTensorAssociativityStatement`,
  `TensorMonoidalLeftUnitorComparisonStatement` and
  `PullbackTensorSymmetryStatement`;
- `PicardZeroPullbackStatement`, `MumfordBundlePicardZeroStatement`,
  `PicardZeroUniversalBaseChangeStatement`,
  `DualAbelianBaseChangeNaturalityStatement` and
  `PolarizationBaseChangeStatement`;
- `RelativeFiniteWeilTransitionStatement`, the rational
  profinite-integer/adele comparison `h`, and
  `TorsionFiniteEtaleStatement`;
- `CMRepresentabilityStatement ... q`,
  `RelativeDualSchemeExistenceStatement`,
  `RelativeDualSchemeGeometryStatement`, and
  `CMGeometricCoarseRigidity ... U.obj`.

The representability assertion concerns the fixed original CM moduli
presheaf, with its componentwise connected, locally Noetherian and
geometric-point conditions. The tower and its morphisms are constructed
from representing witnesses for that presheaf. They are not arbitrary
scheme outputs. The imported construction derives the original normal
finite geometric torsors from these premises, including the existing
dominant-unramified-etale result. This unit does not prove representability,
dual existence and geometry, or coarse rigidity.

Use the notation

```text
S  = cmSchemeTower ... q
X  = S.obj U
J  = Scheme.smallEtaleTopology X
R  = HarrisCoefficientIntegers K p
I  = harrisCoefficientScalarIdeal K p m
T  = HarrisCoefficientReductionRing K p m k = R / I^k
π  = Ideal.Quotient.mk (I^k)
V₀ = cmHarrisCoefficientLevel D ρ p U m hm k
G  = SmallCMResidualGroup D U V₀
N  = cmHarrisCoefficientAction D ρ p U m hm k
M  = (cmHarrisCoefficientDiagram D ρ p U m hm).action (op k).
```

The integral ring `R` retains the full product over all coefficient places
of `K` above `p`. The actions use the published stable-lattice reductions
and original inverse-unop convention; no coefficient place is selected.
The allowed exponent includes zero. No free or nonzero reduction module
is asserted.

Choose another small CM level `V`, assume
`(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal`, and retain

```text
hV : V.obj.subgroup ≤ V₀.obj.subgroup.
```

The published `cmHarrisRefinement_kernel_le` gives the needed kernel
containment. Put

```text
Q = SmallCMResidualGroup D U V
φ = smallCMResidualQuotientMap D U V₀ V hV : Q →* G
P = cmHarrisResidualCoefficientAction ... V ...
Y = cmHarrisCoefficientTorsor ... k
Z = cmHarrisRefinementTorsor ... k V hV
a = cmHarrisCoefficientRefinementCover ... k V hV.
```

Here `P` is the independently factored `T`-module action on the same
reduction module as `N`. The cover morphism has type
`Z.val ⟶ (Action.res X.Etale φ).obj Y.val`. Its underlying scheme map
is the original tower map `S.map (smallCMInclusion D hV)`, and the
imported construction proves its compatibility with the structure maps
over `Spec F`. Both covers have the inherited inverse-right deck action.
No additional torsor, splitting, comparison isomorphism, or desired
compatibility equation is supplied.

## Independent integral descent on the finer cover

`cmHarrisRefinementIntegralAction` is the actual restriction of `P`
along the quotient map:

```text
P_R = ((ModuleCat.restrictScalars π).mapAction Q).obj P.
```

`cmHarrisRefinementIntegralActionIso` constructs

```text
d : (Action.res (ModuleCat R) φ).obj M ≅ P_R.
```

It uses `Action.mkIso` with the identity underlying module
isomorphism. To prove equivariance, quotient induction reduces each
operator equation to the same operator of `cmHarrisTorsionSystem`
followed or preceded by an identity. The theorem
`cmHarrisRefinementIntegralActionIso_hom_hom` identifies `d.hom.hom`
with the identity. This proves the action compatibility rather than
assuming it.

`cmHarrisRefinementIntegralSheaf` constructs

```text
B_R = (etaleAssociatedFunctor X Z.val).obj P_R
      : Sheaf J (ModuleCat R).
```

It is invariant descent of the independently factored action, not a
definition by transport from the old coefficient-system component.
Let `C_R` be the constant `R`-module sheaf on the underlying module
of `M`. The definition `cmHarrisRefinementIntegralInclusion` is the
canonical invariant inclusion

```text
i_R : B_R ⟶ (productSheaf J Z.val.V).obj C_R.
```

The instance `cmHarrisRefinementIntegralInclusion_mono` derives its
monomorphism property from the published invariant inclusion.

Write

```text
A_k = (cmHarrisCoefficientSystem ...).obj (op k)
i_A = cmHarrisCoefficientSystemInclusion ... (op k).
```

`cmHarrisRefinementIntegralIso` constructs `e_R : A_k ≅ B_R`.
First form the actual cross-cover morphism with identity coefficient
map,

```text
r_R = etaleCrossCoverMap X φ a
        (𝟙 ((Action.res (ModuleCat R) φ).obj M)).
```

The proved finite geometric torsor properties of `Y` and `Z` imply
`IsIso r_R` by `etaleAssociatedCoverComparison`. Compose `asIso r_R`
with `(etaleAssociatedFunctor X Z.val).mapIso d` to obtain `e_R`.
Invertibility of the cross-cover map is derived, not retained as a
premise.

`cmHarrisRefinementIntegralIso_hom_inclusion` proves the normalization

```text
e_R.hom ≫ i_R = i_A ≫ coverPullback J a.hom C_R.
```

The proof applies naturality of the invariant inclusion to `d.hom`.
Because its underlying module map is the identity, preservation of
identities by the constant-sheaf and product functors removes the extra
maps. The existing `etaleCrossCoverMap_identity_inclusion` then gives
the displayed equation. Thus the integral comparison restricts actual
cover sections along original scheme forgetting. The theorem has a
`reassoc` variant.

## Scalar restriction on the finer cover

Let

```text
F_π = sheafCompose J (ModuleCat.restrictScalars π)
B_T = cmHarrisRefinementCoefficientSheaf ... k V hV
i_T = cmHarrisRefinementCoefficientInclusion ... k V hV
C_T = (constantSheaf J (ModuleCat T)).obj N.V
c   = (constantRestrictScalarsIso J π).app N.V.
```

The sheaf `B_T` is the previously constructed independent invariant
descent of `P` on `Z`. Its underlying constant module has the same
carrier as `N.V`. The constant-sheaf comparison is
`c : F_π.obj C_T ≅ C_R`.

`cmHarrisRefinementSheafRestrictIso` is

```text
s_V : F_π.obj B_T ≅ B_R.
```

It evaluates the published `constantAssociatedRestrictScalarsIso` at
`P` and `Z`. This comparison includes sheafification of the constant
modules and the invariant construction; it is not declared to be a
definitional identity. Its invariant-inclusion equation is

```text
s_V.hom ≫ i_R
  = F_π.map i_T ≫ (productSheaf J Z.val.V).map c.hom.
```

This is `cmHarrisRefinementSheafRestrictIso_hom_inclusion`, a
specialization of the generic proved normalization. It has a
`reassoc` variant.

## Commutation of the two comparisons

Let `B₀` be the original quotient-ring coefficient sheaf on `Y`, and
write

```text
e_T = cmHarrisCoefficientRefinementIso ... k V hV
      : B₀ ≅ B_T
s₀  = cmHarrisCoefficientSheafRestrictIso ... k
      : F_π.obj B₀ ≅ A_k.
```

`cmHarrisRefinementScalar_square` proves, in the actual category of
`R`-module sheaves on `J`,

```text
F_π.map e_T.hom ≫ s_V.hom = s₀.hom ≫ e_R.hom.
```

The proof cancels the monomorphism `i_R`. On the left, use the
fine scalar normalization, functoriality of `F_π`, and the published
quotient-ring refinement normalization. On the right, use the integral
refinement normalization and the published coarse scalar normalization.
The remaining equation is naturality of `coverPullback` at `c.hom`.
Restriction of scalars commutes definitionally with that cover pullback,
which is implemented by the original sheaf's restriction maps. The
proof uses typed composition equalities for these steps. No
scalar/refinement equality is assumed.

`cmHarrisRefinementScalar_iso` upgrades the result to equality of the
complete isomorphisms:

```text
F_π.mapIso e_T ≪≫ s_V = s₀ ≪≫ e_R.
```

The proof applies `Iso.ext` and the preceding square. The map
equation also has a `reassoc` variant.

## Sources, derivation and remaining scope

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), Section 3, printed pp.306–308, one-based PDF pp.8–10, supplies
the algebraic representation, stable integral lattice, inverse
function-equivariance in (3.7), and normal quotient factorization for
finite torsion coefficients preceding (3.8). Registered source:
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99,
gives the original small-level moduli, right composition of level
frames, and normal finite-etale covers. III.2, printed pp.94–96,
one-based PDF pp.102–104, constructs torsion coefficient sheaves
using inverse-equivariant component functions, states independence
of choices, and defines compatible coefficient and cover maps with
their composition law. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The supplied five-page author errata list contains no correction to
these passages; this observation concerns only that supplied list.

The integral fine-cover descent, its normalized comparison and the
commuting scalar/refinement square are internal deductions using the
published CM constructions,
[ConstantScalarRestriction](../Coefficients/ConstantScalarRestriction.md)
and
[VaryingSystemCoverChange](../Coefficients/VaryingSystemCoverChange.md).
The original sources supply the geometric and coefficient context and
conventions. The new Lean formulas are not attributed as verbatim
statements in those sources. The nonzero natural scalar and exponent
zero are inherited from the existing arithmetic constructors, extending
the sources' positive prime-power parameters.

This is a comparison at fixed coarse level, representation, stable
lattice, scalar and exponent. The exponent inverse system is imported,
and no new varying-cover inverse system is defined here. Applicable
representability and dual existence theorems, source rigidity, full
source-moduli and canonical-model geometry, and identification with
the sources' component-function sheaves remain obligations of the
surrounding program. This unit also does not prove independence of
the lattice or coefficient data, arbitrary scheme inverse-image
compatibility, scalar extension, or completion to a lisse adic sheaf.
Those broader obligations remain assigned and required.

Only published dependencies are imported. This pair is by Worker 57,
using Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
