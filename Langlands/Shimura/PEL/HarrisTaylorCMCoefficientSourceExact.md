# Exact original CM coefficient sequences on common source covers

Author: Worker 57.

This derived construction models the entire original CM coefficient
reduction sequence on every common finer original cover. It includes
the independently descended kernel, its actual inclusion, and the
original system transition. The resulting isomorphism of short complexes
respects further source-cover refinement and recovers the existing
fine-cover model at the identity arrow.

## Inputs and retained premises

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

The named assertions retained from
[HarrisTaylorCMCoefficientLocalExact](HarrisTaylorCMCoefficientLocalExact.md)
are
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

For a fixed `U : SmallCMLevel D`, retain

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

Here q is the exact representability assertion for the original CM
moduli presheaf on `ComponentwiseAdmissibleCMBaseCategory`, including
its componentwise connected, locally Noetherian and geometric-point
conditions. The scheme tower is the existing Yoneda construction from q.
Applicable representability, dual existence, geometry and coarse rigidity
remain premises of this construction.

The coefficient input is a number field K, a finite K-module W, an
algebraic representation `ρ` of `D.rationalInvolution.baseChange K` on W,
a rational finite place p, and `m : ℕ` with `hm : m ≠ 0`. The imported
construction chooses its actual stable full lattice. Every nonnegative
exponent, including zero, is retained.

## Original sequence and a common source cover

Write

```text
X = (cmSchemeTower ... q).obj U
J = Scheme.smallEtaleTopology X
R = HarrisCoefficientIntegers K p
M = cmHarrisCoefficientDiagram D ρ p U m hm
Y = cmHarrisCoefficientEtaleDiagram ... q U ρ p m hm
      existence geometry hRigid
A = cmHarrisCoefficientSystem ... q U ρ p m hm
      existence geometry hRigid
Const = constantSheaf J (ModuleCat R)
P_k = J.overPullback (ModuleCat R) (Y.obj.obj k).
```

R is the full integral product over all places of K above p. With
`I = harrisCoefficientScalarIdeal K p m`, M_i is the original
full reduction `Λ/I^(i.unop)Λ`. Y_i is the original scheme level at
`cmHarrisCoefficientLevel D ρ p U m hm i.unop`, with its original
forgetting maps, residual group `SmallCMResidualGroup D U V_i`,
and inverse-right cover action. The coefficient action is the existing
`g ↦ unop(g)⁻¹`.

Fix `f : i ⟶ j` and `a : k ⟶ i` in `ℕᵒᵖ`; hence
`j.unop ≤ i.unop ≤ k.unop`. These give actual cover maps
`Y_k → Y_i → Y_j`. Put

```text
φ = M.transition f
H = cmHarrisCoefficientTransitionKernel D U ρ p m hm f
u_f = cmHarrisCoefficientTransitionKernelModuleIso D U ρ p m hm f
K_f = cmHarrisCoefficientSystemKernelSheaf ... f
inc_f = cmHarrisCoefficientSystemKernelInclusion ... f
S_f = cmHarrisCoefficientReductionSequence ... f
    = (K_f --inc_f--> A_i --A.map f--> A_j)
L_f = cmHarrisCoefficientLinearReductionSequence D U ρ p m hm f
    = (ker(φ.hom.hom) --subtype--> M_i --φ.hom--> M_j).
```

H is the categorical kernel of φ in actions of the fine residual group.
The target action of φ is the restricted coarse action, and its underlying
map preserves the lattice representative when reducing the exponent.
K_f and inc_f are independently descended from H and its inclusion
on Y_i. The second arrow of S_f is the existing varying-cover system
transition. The short exactness of this original sequence is an imported
result. L_f is the existing ordinary module short complex.

The finite geometric torsor and covering properties of Y_i are imported
results under the retained premises. P_k restricts sheaves to the
over-site of the actual object Y_k in J. All localized isomorphisms below
live in that over-site's category of R-module sheaves.

## Kernel evaluation and its actual inclusion

Let `e_a = cmHarrisCoefficientSystemTrivializationAlong ... a`, the
existing independently constructed evaluation

```text
e_a : P_k.obj A_i ≅ P_k.obj (Const.obj M_i).
```

`cmHarrisCoefficientSystemKernelTrivializationAlong` constructs

```text
s_a : P_k.obj K_f ≅ P_k.obj (Const.obj H.V).
```

It applies `associatedTrivializationAlongOfSplitting` to the original
fine action, the actual map `Y.obj.map a`, and the constant coefficient
action of H. The required splitting is the existing
`etaleTorsorSectionSplitting` for Y_i. Its forward map is the existing
`associatedEvaluationAlong`: it restricts the original inclusion of
invariant sections and evaluates on the graph of the map into Y_i.
Its construction does not use the desired inclusion square.

`cmHarrisCoefficientSystemKernelInclusion_evaluationAlong` proves

```text
P_k.map inc_f ≫ e_a.hom
  = s_a.hom ≫ P_k.map (Const.map (kernel.ι φ).hom).
```

This is naturality of `associatedEvaluationAlongNat` at the actual
equivariant kernel inclusion. The existing ordinary kernel comparison

```text
u_f : H.V ≅ ModuleCat.of R (LinearMap.ker φ.hom.hom)
```

is already normalized by
`cmHarrisCoefficientTransitionKernelModuleIso_hom_subtype`:
its composite with the ordinary subtype inclusion is `(kernel.ι φ).hom`.
The definition
`cmHarrisCoefficientSystemKernelLinearTrivializationAlong` sets

```text
l_a = s_a ≪≫ P_k.mapIso (Const.mapIso u_f).
```

The theorem
`cmHarrisCoefficientSystemKernelInclusion_evaluationAlong_linear`
uses functoriality, associativity and that existing normalization to give

```text
P_k.map inc_f ≫ e_a.hom
  = l_a.hom ≫
      P_k.map (Const.map
        (ModuleCat.ofHom (LinearMap.ker φ.hom.hom).subtype)).
```

Thus the kernel model preserves the actual ordinary subtype inclusion.

## The whole sequence and identity recovery

`cmHarrisCoefficientReductionSequenceSourceIso` constructs

```text
Θ_a : S_f.map P_k ≅ L_f.map (Const ⋙ P_k).
```

The three components are `l_a`, `e_a`, and `e_(a ≫ f)`.
`ShortComplex.isoMk` uses the proved ordinary kernel-inclusion square
and the imported `cmHarrisCoefficientSystem_map_evaluationAlong` square

```text
P_k.map (A.map f) ≫ e_(a ≫ f).hom
  = e_a.hom ≫ P_k.map (Const.map φ.hom).
```

Both original arrows are therefore preserved by an isomorphism of
complete short complexes. Additivity of Const and the imported
`Langlands.Sheaf.SourceSliceExact` additivity of P_k supply the
zero-composite equations when mapping the complexes.

The three identity-recovery theorems
`cmHarrisCoefficientSystemKernelTrivializationAlong_id`,
`cmHarrisCoefficientSystemKernelLinearTrivializationAlong_id`, and
`cmHarrisCoefficientReductionSequenceSourceIso_id`
identify these isomorphisms at `a = 𝟙 i` with the existing original
fine-cover kernel, ordinary kernel, and whole-sequence models.
For the first, the proof rewrites `Y.obj.map (𝟙 i)` and uses the generic
identity evaluation equation. The second follows by composing with
the same constant kernel-module comparison. The third is equality of
isomorphisms, proved by extensionality on their three forward components;
the coefficient components use existing identity recovery and
`𝟙 i ≫ f = f`.

## Compatibility with further source-cover refinement

For `b : l ⟶ k`, let

```text
B_b = J.overMapPullback (ModuleCat R) (Y.obj.map b)
c_b = overPullbackMapIso J (ModuleCat R) (Y.obj.map b)
    : P_k ⋙ B_b ≅ P_l.
```

This is the existing canonical comparison of the actual over-site
restriction functors. The following are proved with that comparison:

```text
B_b.map e_a.hom ≫ c_b.hom.app (Const.obj M_i)
  = c_b.hom.app A_i ≫ e_(b ≫ a).hom

B_b.map s_a.hom ≫ c_b.hom.app (Const.obj H.V)
  = c_b.hom.app K_f ≫ s_(b ≫ a).hom

B_b.map l_a.hom ≫
    c_b.hom.app (Const.obj (ModuleCat.of R (LinearMap.ker φ.hom.hom)))
  = c_b.hom.app K_f ≫ l_(b ≫ a).hom.
```

The corresponding declarations are
`cmHarrisCoefficientSystemTrivializationAlong_sourceChange`,
`cmHarrisCoefficientSystemKernelTrivializationAlong_sourceChange`, and
`cmHarrisCoefficientSystemKernelLinearTrivializationAlong_sourceChange`.
The first two specialize the published generic
`etaleAssociatedEvaluationAlong_sourceChange` and
`associatedEvaluationAlong_sourceChange`, using
`Y.obj.map (b ≫ a) = Y.obj.map b ≫ Y.obj.map a`.
The third combines the kernel equation with naturality of c_b at
`Const.map u_f.hom`.

Finally,
`cmHarrisCoefficientReductionSequenceSourceIso_sourceChange` proves
the equality of actual short-complex morphisms

```text
B_b.mapShortComplex.map Θ_a.hom ≫
    (L_f.mapNatIso (Functor.isoWhiskerLeft Const c_b)).hom
  = (S_f.mapNatIso c_b).hom ≫ Θ_(b ≫ a).hom.
```

The `mapNatIso` maps are the canonical comparisons on the entire
constant and descended complexes. The proof uses
`ShortComplex.hom_ext`: the first two components are the preceding
linear-kernel and stage equations, and the third is the stage equation
for `a ≫ f`, with associativity identifying `(b ≫ a) ≫ f`.
This states compatibility of the complete model under further source
refinement, including the kernel term.

## Sources, internal provenance and scope

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), Section 3, printed pp.306–308, one-based PDF pp.8–10, gives the
algebraic coefficient representation, stable integral lattice, inverse
function equivariance (3.7), and normal congruence quotient factorization
before (3.8). The registered source is
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99,
gives the original small-level moduli, right frame composition and normal
finite-etale covers. III.2, printed pp.94–96, PDF pp.102–104, gives
stable-lattice torsion coefficients, inverse-equivariant functions, and
compatible coefficient/cover maps and composition. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The common-source kernel model, both inclusion squares, complete
short-complex isomorphism, identity recovery and source-change equations
are internal deductions from the existing original CM exact sequence,
ordinary kernel normalization and graph evaluation constructions.
They are not attributed to separately stated theorems in these source
passages. The nonzero natural scalar and exponent zero come from the
imported arithmetic construction. The proof imports generic torsor
descent and slice comparisons by Lean name.

This unit retains the exact geometric premises above. It proves no
applicable representability or canonical-model existence, dual existence,
coarse rigidity, ideal-power kernel formula, exactness of global sections,
lattice independence or unbounded adic-limit assertion. Its restriction
functors concern actual over-sites; comparison with another scheme's
small-etale site is outside this unit.

The code and prose are by Worker 57 using published generic interfaces.
The pinned environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
