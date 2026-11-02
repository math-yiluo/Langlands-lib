# Integral evaluation on original CM normal refinements

Author: Worker 57.

Construct canonical evaluation of the independently descended integral
coefficient sheaf on a finer original CM normal cover. Prove that both
integral cover refinement and quotient-ring scalar restriction preserve
this evaluation, as equalities of actual morphisms and of complete
isomorphisms on the localized small-etale site.

## Inputs and retained premises

All arithmetic carriers and coefficient modules have universe zero.
Retain the totally real number field `E`, the CM number field `F`, the
quadratic extension `E → F`, the algebra `A` with every displayed scalar
structure and tower, and `D : CentralSimpleUnitaryData E F A n`. Retain
`Module.Finite ℚ A`, the imaginary quadratic number field `L`, its map
into `F`, the chosen complex embedding `τ₀`, and the Harris signature
charts `C`. Let `K` be a number field, `W` a finite `K`-module, and `ρ`
an algebraic representation of `D.rationalInvolution.baseChange K` on
`W`. Fix the rational finite place `p`, small CM level `U`, natural
scalar `m` with `hm : m ≠ 0`, and exponent `k : ℕ`.

This unit retains every named premise of
[HarrisTaylorCMCoefficientRefinementScalars](HarrisTaylorCMCoefficientRefinementScalars.md):

- `pullbackTensorComparisonIsIsoStatement`,
  `PullbackTensorCompositionStatement`,
  `PullbackTensorUnitCoherenceStatement`,
  `ExplicitPullbackTensorAssociativityStatement`,
  `TensorMonoidalLeftUnitorComparisonStatement`, and
  `PullbackTensorSymmetryStatement`;
- `PicardZeroPullbackStatement`, `MumfordBundlePicardZeroStatement`,
  `PicardZeroUniversalBaseChangeStatement`,
  `DualAbelianBaseChangeNaturalityStatement`, and
  `PolarizationBaseChangeStatement`;
- `RelativeFiniteWeilTransitionStatement`, the rational
  profinite-integer/adele comparison `h`, and
  `TorsionFiniteEtaleStatement`;
- `CMRepresentabilityStatement ... q`,
  `RelativeDualSchemeExistenceStatement`,
  `RelativeDualSchemeGeometryStatement`, and
  `CMGeometricCoarseRigidity ... U.obj`.

The representability premise concerns the fixed original CM moduli
presheaf and its connected, locally Noetherian and geometric-point
conditions. The actual scheme tower and its maps are constructed from
representing witnesses for that presheaf. The imported original-cover
results derive the finite geometric torsors from these exact premises.
No arbitrary scheme outputs, chosen trivializations or desired
comparison equations are additional inputs to this unit.

Use the notation

```text
S   = cmSchemeTower ... q
X   = S.obj U
J   = Scheme.smallEtaleTopology X
R   = HarrisCoefficientIntegers K p
I   = harrisCoefficientScalarIdeal K p m
T   = HarrisCoefficientReductionRing K p m k = R / I^k
π   = Ideal.Quotient.mk (I^k)
V₀  = cmHarrisCoefficientLevel D ρ p U m hm k
G   = SmallCMResidualGroup D U V₀
N   = cmHarrisCoefficientAction D ρ p U m hm k
M   = (cmHarrisCoefficientDiagram D ρ p U m hm).action (op k)
A_k = (cmHarrisCoefficientSystem ...).obj (op k).
```

The integral ring retains the full product over all coefficient places
of `K` above `p`. The actions come from the published stable-lattice
reductions and retain the original inverse-unop convention. The
underlying module of `M` is the restriction of `N.V` to `R`. Exponent
zero is allowed; no nonzero or free reduction module is asserted.

Choose `V : SmallCMLevel D` with
`(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal` and
`hV : V.obj.subgroup ≤ V₀.obj.subgroup`. Put

```text
Q   = SmallCMResidualGroup D U V
φ   = smallCMResidualQuotientMap D U V₀ V hV : Q →* G
Y   = cmHarrisCoefficientTorsor ... k
Z   = cmHarrisRefinementTorsor ... k V hV
a   = cmHarrisCoefficientRefinementCover ... k V hV
P_R = cmHarrisRefinementIntegralAction D U ρ p m hm k V hV
B_R = cmHarrisRefinementIntegralSheaf ... k V hV
B_T = cmHarrisRefinementCoefficientSheaf ... k V hV.
```

Here `P_R` is the scalar restriction of the independently factored
fine quotient action, and `B_R` and `B_T` are the corresponding
independent invariant descents on `Z`. Their invariant inclusions
are denoted by `i_R` and `i_T`; write `i_A` for
`cmHarrisCoefficientSystemInclusion ... (op k)`. The morphism `a`
is a map of actions into the restriction of `Y` along `φ`. Its
underlying map is the actual tower forgetting map for `hV`, with
its proved `Spec F` compatibility. Both covers retain the original
inverse-right deck convention.

Let

```text
C_R = (constantSheaf J (ModuleCat R)).obj M.V
C_T = (constantSheaf J (ModuleCat T)).obj N.V
F_π = sheafCompose J (ModuleCat.restrictScalars π)
L_Z = J.overPullback (ModuleCat R) Z.val.V
F_π,Z = sheafCompose (J.over Z.val.V) (ModuleCat.restrictScalars π)
c   = (constantRestrictScalarsIso J π).app N.V.
```

Thus `c : F_π.obj C_T ≅ C_R`. The localization here is the
published restriction to the slice of the small-etale site over the
actual cover object `Z.val.V`. It is not a construction of an arbitrary
scheme inverse-image functor.

## Canonical integral evaluation

`cmHarrisRefinementIntegralTrivialization` constructs

```text
t_R : L_Z.obj B_R ≅ L_Z.obj C_R.
```

It evaluates `constantAssociatedTrivializationOfSplitting` at `P_R`.
The required bijectivity of translated graph restrictions is supplied
by `etaleTorsorSectionSplitting` applied to the proved geometric
torsor `Z`. Invertibility is consequently derived from the actual
torsor; a splitting or isomorphism is not assumed. The forward map
is the canonical invariant inclusion followed by tautological graph
evaluation:

```text
t_R.hom = L_Z.map i_R ≫ productEvaluation J Z.val C_R.
```

This is `cmHarrisRefinementIntegralTrivialization_hom`, proved by
reflexivity. For an object `u` over `Z.val.V`, the product evaluation
restricts sections along `prod.lift u.hom (𝟙 u.left)`.

`cmHarrisIntegralTrivializationAlongRefinement` independently constructs

```text
t_a : L_Z.obj A_k ≅ L_Z.obj C_R.
```

It uses `associatedTrivializationAlongOfSplitting` for the original
cover `Y`, the actual map `a.hom`, and the constant-sheaf action of
`M`. The splitting needed here is derived from `Y` itself. The theorem
`cmHarrisIntegralTrivializationAlongRefinement_hom` identifies its
forward map with `associatedEvaluationAlong J Y.val a.hom ...`, again
by reflexivity. Explicitly this is

```text
t_a.hom = L_Z.map i_A ≫ productEvaluationAlong J a.hom C_R.
```

On the object `u`, this product evaluation restricts along
`prod.lift (u.hom ≫ a.hom) (𝟙 u.left)`. Thus this construction
evaluates the original invariant sections along original forgetting;
it is defined without using the refinement isomorphism.

Write `e_R = cmHarrisRefinementIntegralIso ... k V hV : A_k ≅ B_R`.
`cmHarrisRefinementIntegralIso_evaluation` proves

```text
L_Z.map e_R.hom ≫ t_R.hom = t_a.hom.
```

The proof expands the two evaluation maps, uses functoriality of
localization and the published invariant-inclusion normalization
of `e_R`, then applies `coverPullback_productEvaluation`. The last
identity states that cover restriction followed by graph evaluation
is evaluation along the cover map. No compatibility assertion is an
input to the proof. The theorem has a `reassoc` variant.

`cmHarrisRefinementIntegralIso_trivialization` applies `Iso.ext` to
this equation and gives equality of complete isomorphisms:

```text
L_Z.mapIso e_R ≪≫ t_R = t_a.
```

## Scalar-compatible fine evaluation

Let `t_T = cmHarrisRefinementCoefficientTrivialization ... k V hV`
be the published canonical quotient-ring evaluation on `Z`.
`cmHarrisRefinementRestrictedTrivialization` defines

```text
t_π : L_Z.obj (F_π.obj B_T) ≅ L_Z.obj C_R
    = F_π,Z.mapIso t_T ≪≫ L_Z.mapIso c.
```

This definition restricts the independently constructed quotient-ring
evaluation, then compares constant sheaves. Restriction of scalars
commutes definitionally with the displayed localization, so the
domain and codomain above are the actual ones used in Lean.

Write `s_V = cmHarrisRefinementSheafRestrictIso ... k V hV`, whose
type is `F_π.obj B_T ≅ B_R`.
`cmHarrisRefinementSheafRestrictIso_evaluation` proves

```text
L_Z.map s_V.hom ≫ t_R.hom = t_π.hom.
```

The proof localizes the published normalization
`s_V.hom ≫ i_R = F_π.map i_T ≫ (productSheaf ...).map c.hom`.
Functoriality of `L_Z`, associativity, and
`productEvaluation_natural` move `c.hom` past graph evaluation.
The result is the defining composite for `t_π`. It does not assume
that the constant-sheaf scalar comparison is a definitional identity.

`cmHarrisRefinementSheafRestrictIso_trivialization` gives the full
isomorphism equality

```text
L_Z.mapIso s_V ≪≫ t_R = t_π.
```

The theorem `cmHarrisRefinementSheafRestrictIso_inv_evaluation` also
proves the explicit inverse equation

```text
L_Z.map s_V.inv ≫ t_π.hom = t_R.hom.
```

It substitutes the forward equation and uses functoriality and
`s_V.inv ≫ s_V.hom = 𝟙 _`. Both morphism equations have `reassoc`
variants.

## Combined scalar and refinement compatibility

Let

```text
e_T = cmHarrisCoefficientRefinementIso ... k V hV
s₀  = cmHarrisCoefficientSheafRestrictIso ... k.
```

The published scalar/refinement square is
`F_π.map e_T.hom ≫ s_V.hom = s₀.hom ≫ e_R.hom`.
`cmHarrisRefinementScalar_evaluation` proves its compatibility with
the original local evaluation:

```text
L_Z.map (F_π.map e_T.hom) ≫ t_π.hom
  = L_Z.map s₀.hom ≫ t_a.hom.
```

The implemented proof explicitly instantiates the fine scalar
evaluation equation, the scalar/refinement square, and the integral
refinement evaluation equation. It maps the square through `L_Z`,
uses its composition law, and composes with `t_R.hom`. Associativity
and the two evaluation equations give the result. A typed calculation
keeps all arithmetic and geometric parameters fixed. The theorem
has a `reassoc` variant.

`cmHarrisRefinementScalar_trivialization` proves equality of complete
isomorphisms by `Iso.ext`:

```text
L_Z.mapIso (F_π.mapIso e_T) ≪≫ t_π
  = L_Z.mapIso s₀ ≪≫ t_a.
```

All these maps live in the actual category of `R`-module sheaves on
the localized small-etale site.

## Sources, provenance and remaining scope

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), Section 3, printed pp.306–308, one-based PDF pp.8–10, supplies
the algebraic representation, stable integral lattice, inverse
function-equivariance in (3.7), normal quotient factorization for finite
torsion coefficients preceding (3.8), and the identity-evaluation
formula (3.11). Registered source:
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99,
gives the original small-level moduli, right frame composition and
normal finite-etale covers. III.2, printed pp.94–96, one-based PDF
pp.102–104, defines torsion coefficient sheaves by inverse-equivariant
component functions, states choice independence, and gives compatible
coefficient and cover maps and composition. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The supplied five-page author errata list contains no correction to
these passages; this observation concerns only that list.

The new local integral isomorphisms and evaluation equations are
internal deductions from the published original CM constructions and
the generic graph-splitting and cover-evaluation results in
[TrivializationFromSplitting](../Coefficients/TrivializationFromSplitting.md)
and [CrossCoverEvaluation](../Coefficients/CrossCoverEvaluation.md).
They are not attributed as verbatim statements of the original
sources. The nonzero natural scalar and exponent zero are the existing
arithmetic constructors' extension of the sources' positive prime-power
parameters.

This unit fixes the coarse level, algebraic representation, stable
lattice, scalar and exponent. Applicable representability and dual
existence/geometry theorems, source rigidity, full source-moduli and
canonical-model geometry, and identification with the original
component-function sheaves remain required in the surrounding program.
This unit does not establish lattice independence, scalar extension,
arbitrary scheme inverse-image compatibility or completion to a lisse
adic sheaf. It does not construct a varying-cover exponent system.

Only published dependencies are imported. This pair is by Worker 57,
using Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
