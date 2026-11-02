# Local linear models for exact original CM coefficient reductions

Author: Worker 57.

This derived construction identifies the entire original CM coefficient
reduction sequence, localized to its original fine cover, with the constant
sequence of the ordinary linear kernel and the actual full-lattice
reduction. The kernel model and both coefficient evaluations are constructed
independently of the desired commuting squares. The squares are then proved
for the existing inclusion and system transition.

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

The explicit assertions are
`pullbackTensorComparisonIsIsoStatement`,
`PullbackTensorCompositionStatement`,
`PullbackTensorUnitCoherenceStatement`,
`ExplicitPullbackTensorAssociativityStatement`,
`TensorMonoidalLeftUnitorComparisonStatement`,
`PullbackTensorSymmetryStatement`,
`PicardZeroPullbackStatement`,
`MumfordBundlePicardZeroStatement`,
`PicardZeroUniversalBaseChangeStatement`,
`DualAbelianBaseChangeNaturalityStatement`,
`PolarizationBaseChangeStatement`,
`RelativeFiniteWeilTransitionStatement`,
`h : Global.RationalProfiniteIntegerAdeleComparison`, and
`htor : TorsionFiniteEtaleStatement.{0}`.

For the fixed coarse small level `U : SmallCMLevel D`, the further
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
locally Noetherian and geometric-point conditions. The scheme tower is
the existing Yoneda construction from that assertion. The applicable
representability, dual existence, geometry and rigidity results remain
premises.

The coefficient input is a number field K, a finite K-module W, an
algebraic representation `ρ` of `D.rationalInvolution.baseChange K` on W,
a rational finite place p, and a natural scalar m with `hm : m ≠ 0`.
The lattice is the actual stable full lattice chosen by the imported
Harris construction. All nonnegative exponents, including zero, are
allowed.

## Original objects and maps

Write

```text
X = (cmSchemeTower ... q).obj U
J = Scheme.smallEtaleTopology X
R = HarrisCoefficientIntegers K p
Q = cmHarrisCoefficientGroups D ρ p U m hm
M = cmHarrisCoefficientDiagram D ρ p U m hm
Y = cmHarrisCoefficientEtaleDiagram ... q U ρ p m hm
      existence geometry hRigid
A = cmHarrisCoefficientSystem ... q U ρ p m hm
      existence geometry hRigid
C = constantSheaf J (ModuleCat R)
P_i = J.overPullback (ModuleCat R) (Y.obj.obj i).
```

In these abbreviations C denotes the constant-sheaf functor; the signature
charts remain the original input above. R is the fixed full integral
product over all places of K above p. If
`I = harrisCoefficientScalarIdeal K p m`, the modules M_i are the existing
full reductions `Λ/I^(i.unop)Λ`, viewed as R-modules. The covers Y_i are
the original levels at
`cmHarrisCoefficientLevel D ρ p U m hm i.unop`; their residual groups are
`SmallCMResidualGroup D U V_i`. They retain the original forgetting
maps and inverse-right cover action, with coefficient action
`g ↦ unop(g)⁻¹`.

Fix `f : i ⟶ j` in `ℕᵒᵖ`, so `j.unop ≤ i.unop`. Put
`φ = M.transition f`, an equivariant map from M_i to M_j with its action
restricted to Q_i. Its underlying linear map keeps the same lattice
representative at the lower exponent. The existing constructions from
[HarrisTaylorCMCoefficientExact](HarrisTaylorCMCoefficientExact.md) give

```text
H = kernel φ                         in Q_i-actions on R-modules
K_f = cmHarrisCoefficientSystemKernelSheaf ... f
inc_f = cmHarrisCoefficientSystemKernelInclusion ... f
S_f = cmHarrisCoefficientReductionSequence ... f
    = (K_f --inc_f--> A_i --A.map f--> A_j).
```

K_f is independently descended from H on the actual fine torsor Y_i.
The existing short exactness proof concerns this very sequence, with the
original system transition as its second arrow. In particular,
`A.map f` retains coefficient reduction followed by the inverse proved
original-cover comparison.

The finite geometric torsor property and covering property of Y_i are
the imported results for these actual schemes under the displayed
premises. P_i is restriction to the site over Y_i in J. Every
isomorphism below lives in that over-site's category of R-module sheaves.

## The ordinary kernel and its inclusion

The imported `cmHarrisCoefficientTransitionKernelModuleIso` is

```text
u_f : H.V ≅ ModuleCat.of R (LinearMap.ker φ.hom.hom).
```

It first forgets the action while preserving the categorical kernel,
then applies `ModuleCat.kernelIsoKer`. The theorem
`cmHarrisCoefficientTransitionKernelModuleIso_hom_subtype` proves

```text
u_f.hom ≫ ModuleCat.ofHom (LinearMap.ker φ.hom.hom).subtype
  = (kernel.ι φ).hom.
```

The proof unfolds this existing comparison, uses the normalization of
`ModuleCat.kernelIsoKer`, rewrites the kernel-preservation isomorphism,
and applies `kernelComparison_comp_ι` for `Action.forget`. Thus the
ordinary kernel identification preserves the actual inclusion.

Let `t_i = cmHarrisCoefficientSystemTrivialization ... i`, and let
`s_f = cmHarrisCoefficientSystemKernelTrivialization ... f`.
These are the existing constant models of A_i and K_f on Y_i.
The theorem `cmHarrisCoefficientSystemKernelInclusion_evaluation`
proves

```text
P_i.map inc_f ≫ t_i.hom
  = s_f.hom ≫ P_i.map (C.map (kernel.ι φ).hom).
```

This is exactly the naturality equation of
`constantAssociatedTrivializationOfSplitting` applied to the
equivariant kernel inclusion. The splitting is supplied by
`etaleTorsorSectionSplitting` for the original fine geometric torsor;
the inclusion square is not an additional input.

`cmHarrisCoefficientSystemKernelLinearTrivialization` defines

```text
l_f : P_i.obj K_f ≅
        P_i.obj (C.obj (ModuleCat.of R (LinearMap.ker φ.hom.hom)))
l_f = s_f ≪≫ P_i.mapIso (C.mapIso u_f).
```

The theorem
`cmHarrisCoefficientSystemKernelInclusion_evaluation_linear`
combines the two preceding normalization equations to obtain

```text
P_i.map inc_f ≫ t_i.hom
  = l_f.hom ≫
      P_i.map (C.map (ModuleCat.ofHom (LinearMap.ker φ.hom.hom).subtype)).
```

Its proof uses functoriality and associativity to substitute the
normalized ordinary inclusion into the preceding naturality square.

## Isomorphism of the whole localized sequence

`cmHarrisCoefficientLinearReductionSequence` is the concrete short
complex of R-modules

```text
L_f = (ker(φ.hom.hom) --subtype--> M_i --φ.hom--> M_j).
```

Its zero-composite field is proved pointwise from membership in the
linear kernel. The ordinary kernel here is a submodule of the existing
finite M_i; no ideal-power formula for it is required.

Let `e_f = cmHarrisCoefficientSystemTrivializationAlong ... f` from
[HarrisTaylorCMCoefficientLocalReduction](HarrisTaylorCMCoefficientLocalReduction.md).
This evaluates A_j on Y_i along the graph of the actual forgetting
map Y_i → Y_j. The construction uses splitting of the original coarse
torsor independently of `A.map f`. Its published reduction square is

```text
P_i.map (A.map f) ≫ e_f.hom
  = t_i.hom ≫ P_i.map (C.map φ.hom).
```

`cmHarrisCoefficientReductionSequenceLocalIso` constructs

```text
S_f.map P_i ≅ L_f.map (C ⋙ P_i).
```

It uses `ShortComplex.isoMk` with components l_f, t_i and e_f,
respectively. The first commuting square is the proved linear
kernel-inclusion equation; the second is the published original
reduction equation. The short complexes use their actual maps and
zero-composite proofs, so this is an isomorphism of complete short
complexes, not merely three unrelated object isomorphisms.

`Langlands.Sheaf.SourceSliceExact` supplies the existing additivity
instance for P_i. Additivity of C and P_i makes mapping these short
complexes preserve their zero-composite equations. The generic slice
restriction and torsor descent constructions are reused by Lean name.

## Sources, internal provenance and scope

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), Section 3, printed pp.306–308, one-based PDF pp.8–10, gives the
algebraic coefficient representation, stable integral lattice, inverse
function equivariance (3.7), and normal congruence quotient
factorization before (3.8). The registered source is
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99,
gives the original small-level moduli, right frame composition and
normal finite-etale covers. III.2, printed pp.94–96, PDF pp.102–104,
gives stable-lattice torsion coefficients, inverse-equivariant functions,
and compatible coefficient/cover maps and composition. The registered
source is `harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The ordinary inclusion normalization, its descended evaluation square,
and the complete short-complex isomorphism are internal deductions from
the published exact reduction and evaluation constructions. Their proof
route uses action-kernel preservation, the ordinary module kernel,
naturality of the existing constant associated trivialization, and
`ShortComplex.isoMk`. These conclusions are not attributed to a
separately stated theorem in the cited source passages. The allowance
of any nonzero natural scalar and of exponent zero comes from the
imported arithmetic construction.

This unit retains all geometric assertions listed above. It does not
prove applicable representability, dual existence, coarse rigidity,
canonical models, an ideal-power kernel formula, exactness of global
sections, lattice independence or an unbounded adic limit. The local
model uses the actual over-site restriction; it asserts no additional
comparison with another scheme's small-etale site.

The code and prose in this pair are by Worker 57, using published
generic interfaces. The pinned environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
