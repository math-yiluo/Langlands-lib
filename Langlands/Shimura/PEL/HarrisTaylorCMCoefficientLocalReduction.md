# Simultaneous local models for original CM coefficient reductions

Author: Worker 57.

This derived construction trivializes the original CM coefficient sheaves
along actual fine-to-coarse covering maps. It proves that the existing sheaf
transitions become the constant full-lattice reductions under these
independently constructed evaluations. For each exponent k it assembles all
stages with exponent at most k into one natural isomorphism on the original
cover at k.

## Inputs and retained geometric premises

All field, algebra, scheme, group and coefficient carriers have universe
zero. Retain `D : CentralSimpleUnitaryData E F A n`, where E is a totally
real number field, F is a totally complex CM number field quadratic over E,
and A has the displayed E-, F- and rational algebra structures with their
compatible scalar towers. Assume `Module.Finite ℚ A`. Retain the imaginary
quadratic number field L, its algebra map into F, a complex embedding
`τ₀ : L →+* ℂ`, and

```text
C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀).
```

The code explicitly takes the following assertions:

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
- `RelativeFiniteWeilTransitionStatement`,
  `h : Global.RationalProfiniteIntegerAdeleComparison`, and
  `htor : TorsionFiniteEtaleStatement.{0}`.

For the fixed small coarse level `U : SmallCMLevel D`, the additional
premises are

```text
q : CMRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor,
existence : RelativeDualSchemeExistenceStatement.{0},
geometry : RelativeDualSchemeGeometryStatement.{0},
hRigid : CMGeometricCoarseRigidity D C preservation composition
      unitCoherence associativity comparison symmetry stability square
      universality compatibility h htor U.obj.
```

Representability concerns the existing original CM moduli presheaf on
`ComponentwiseAdmissibleCMBaseCategory`, with its componentwise connected,
locally Noetherian and geometric-point conditions. The scheme tower is the
existing Yoneda construction from this precise assertion. These
representability, dual-existence, geometry and rigidity obligations remain
premises. No replacement scheme, sheaf, transition, evaluation, graph
splitting or desired compatibility is given as input.

The coefficient input is a number field K, a finite K-module W, an
algebraic representation `ρ` of `D.rationalInvolution.baseChange K` on W,
a rational finite place p, and a natural scalar m with `hm : m ≠ 0`.
The imported construction chooses the stable full lattice. All
nonnegative exponents, including zero, are allowed.

## Original covers, coefficients and localizations

Use the following notation:

```text
S   = cmSchemeTower ... q
X   = S.obj U
J   = Scheme.smallEtaleTopology X
R   = HarrisCoefficientIntegers K p
Q   = cmHarrisCoefficientGroups D ρ p U m hm
M   = cmHarrisCoefficientDiagram D ρ p U m hm
Y   = cmHarrisCoefficientEtaleDiagram ... q U ρ p m hm
        existence geometry hRigid
A   = cmHarrisCoefficientSystem ... q U ρ p m hm
        existence geometry hRigid
C_j = (constantSheaf J (ModuleCat R)).obj (M.obj.obj j)
P_k = J.overPullback (ModuleCat R) (Y.obj.obj k).
```

The scalar ring R is the fixed full integral product over all coefficient
places of K above p. It is not replaced by a single factor or by the
exponent-dependent quotient ring. If `I = harrisCoefficientScalarIdeal K p m`,
the coefficient carriers are the existing full reductions Λ/I^jΛ,
viewed as R-modules.

At `j : ℕᵒᵖ`, `Y_j` is the original scheme level at
`cmHarrisCoefficientLevel D ρ p U m hm j.unop`. Its residual group is
`SmallCMResidualGroup D U V_j`. The action on this cover retains the
original inverse-right convention, and the coefficient action retains
`g ↦ unop(g)⁻¹`. The structural and transition maps are the original
forgetting maps.

The imported `cmHarrisCoefficientEtaleDiagram_isFiniteGeometricTorsor`
establishes the finite geometric torsor property for these actual covers,
under the listed premises. Their covering property is supplied by
`cmHarrisCoefficientEtaleDiagram_coversTop`. The modules are finite by the
existing coefficient diagram result. These facts make the constant models
below finite constant models on covering objects.

Write `ι_j = cmHarrisCoefficientSystemInclusion ... j` for the original
invariant-section inclusion into `(productSheaf J Y_j).obj C_j`.
Write `t_j = cmHarrisCoefficientSystemTrivialization ... j` for the
existing original-cover isomorphism `P_j.obj A_j ≅ P_j.obj C_j`.
All localizations in this file are restrictions to sites over cover
objects in the small-etale site.

## Independent evaluation along the actual forgetting maps

For `f : i ⟶ j` in `ℕᵒᵖ`, hence `j.unop ≤ i.unop`, the definition
`cmHarrisCoefficientSystemTrivializationAlong ... f` constructs

```text
e_f : P_i.obj A_j ≅ P_i.obj C_j.
```

It applies the published `associatedTrivializationAlongOfSplitting` to the
original coarse action `Y.action j`, the actual map `Y.obj.map f`, and
the constant-sheaf action of `M.action j`. The required graph-splitting
property is derived by `etaleTorsorSectionSplitting` for this same
coarse geometric torsor. In particular, e_f is constructed independently
of the original coefficient transition `A.map f` and of t_i.

`cmHarrisCoefficientSystemTrivializationAlong_hom` identifies its forward
map by reflexivity:

```text
e_f.hom = P_i.map ι_j ≫ productEvaluationAlong J (Y.obj.map f) C_j.
```

At an object `T : Over Y_i`, the evaluation restricts sections along

```text
prod.lift (T.hom ≫ Y.obj.map f) (𝟙 T.left) : T.left → Y_j × T.left.
```

The theorem `cmHarrisCoefficientSystemTrivializationAlong_id` proves
`e_(𝟙 i) = t_i` as an equality of complete isomorphisms. It uses the
cover functor's identity law and the published identity-evaluation lemma.

## The actual reductions in local coordinates

`cmHarrisCoefficientSystem_map_evaluation` proves

```text
P_i.map (A.map f) ≫ e_f.hom
  = t_i.hom ≫ P_i.map ((constantSheaf J (ModuleCat R)).map (M.obj.map f)).
```

The right side uses the actual full-lattice quotient reduction from
`cmHarrisCoefficientDiagram`. The left side uses the existing transition
of `cmHarrisCoefficientSystem`, including its inverse original-cover
comparison. No transition is redefined using the desired local formula.

The proof starts with `cmHarrisCoefficientSystem_map_inclusion`, the
published section equation for that original transition. It applies P_i
to the equation and postcomposes with evaluation. The equation
`coverPullback_productEvaluation` composes the two graph restrictions.
`productEvaluation_natural` moves the constant coefficient reduction
across evaluation. Functoriality and associativity give the stated square.

For any further arrow `a : k ⟶ i`,
`cmHarrisCoefficientSystem_map_evaluationAlong` proves the stronger
common-cover equation

```text
P_k.map (A.map f) ≫ e_(a ≫ f).hom
  = e_a.hom ≫ P_k.map ((constantSheaf J (ModuleCat R)).map (M.obj.map f)).
```

Its private helper proves that first pulling the cover coordinate back
along `Y.obj.map f`, then evaluating along `Y.obj.map a`, is evaluation
along `Y.obj.map (a ≫ f)`. The proof composes the actual sheaf restriction
maps, applies the product projections and uses the original cover
functor's composition law. Applying P_k to the same original section
equation, followed by this helper and
`productEvaluationAlong_natural`, proves the stronger square.

## One natural isomorphism for the stages below k

An object of `Under k` is an arrow `a : k ⟶ j` in `ℕᵒᵖ`, so it selects a
stage whose exponent is at most `k.unop`. A morphism from a to b has
underlying arrow f with `a.hom ≫ f.right = b.hom`. Let
`F_k = Under.forget k`. Then
`cmHarrisCoefficientSystemLocalDiagramIso ... k` constructs

```text
(F_k ⋙ A) ⋙ P_k
  ≅ (F_k ⋙ M.obj ⋙ constantSheaf J (ModuleCat R)) ⋙ P_k.
```

The component at a is the independent e_(a.hom), as recorded by
`cmHarrisCoefficientSystemLocalDiagramIso_app`. Its naturality is the
common-cover square above, with the equation `Under.w f` identifying
the composite arrow with b.hom. Mathlib's `NatIso.ofComponents` therefore
assembles the original evaluations into an isomorphism of entire
diagrams. At `Under.mk (𝟙 k)`, the theorem
`cmHarrisCoefficientSystemLocalDiagramIso_app_id` identifies the
component with the original t_k.

This describes the original finite-stage transitions in a common local
model. It asserts no single finite cover trivializing all unbounded
exponents at once.

## Sources, internal provenance and scope

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), Section 3, printed pp.306–308, one-based PDF pp.8–10, gives the
algebraic coefficient representation, stable integral lattice and inverse
function equivariance (3.7), followed by normal congruence quotient
factorization before (3.8). The registered source is
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99,
gives the original small-level moduli, right frame composition and
normal finite-etale covers. III.2, printed pp.94–96, PDF pp.102–104,
gives stable-lattice torsion coefficients, inverse-equivariant component
functions, and compatible coefficient/cover maps and their composition.
The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The independent evaluations, compatibility squares and simultaneous
natural isomorphism are internal deductions from the published
[original sheaf system](HarrisTaylorCMCoefficientSystem.md) and
[cross-cover evaluation](../Coefficients/CrossCoverEvaluation.md).
The generic evaluation and graph-splitting proofs are imported by Lean
name; this file specializes them to the actual original CM diagrams.
The common-cover helper only computes composition for these particular
cover maps. These conclusions are not attributed to a separately stated
theorem in the cited passages. Allowing any nonzero natural scalar and
exponent zero is an extension supplied by the imported arithmetic
construction.

This unit retains the substantial geometric premises listed above.
It does not prove applicable representability, dual existence, coarse
rigidity or a source canonical-model theorem, or construct arbitrary
scheme inverse image, lattice independence, an unbounded adic limit or
cohomology. The finite constant models are sheaves localized to the
over-site, with no extra comparison to another scheme's small-etale
site asserted.

The code and prose in this pair are by Worker 57, using published
generic interfaces. The pinned environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

## Shared source-diagram construction

The diagram isomorphism `cmHarrisCoefficientSystemLocalDiagramIso` reuses
`cmHarrisCoefficientSourceTrivialization` from
[HarrisTaylorCMCoefficientSourceTrivialization](HarrisTaylorCMCoefficientSourceTrivialization.md).
Both have the same original cover, integral coefficient system and constant
full-lattice reduction diagram, with the same graph-evaluation components.
The component and identity-stage formulas above expose this shared construction;
the along-map evaluation and transition comparisons retain their stated scope.
