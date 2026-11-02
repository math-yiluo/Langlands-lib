# Exact reduction sequences for original CM coefficient sheaves

Author: Worker 57.

This derived construction descends the actual finite kernels of the full
Harris lattice reductions on the original fine CM covers. It constructs
short exact sequences whose second arrows are exactly the transitions of
`cmHarrisCoefficientSystem`. The descended kernel is then identified with
the categorical kernel, with its inclusion normalized, and has an explicit
finite constant model on the fine cover.

## Inputs and retained geometric premises

All field, algebra, scheme, group and coefficient carriers have universe
zero. The unitary input is `D : CentralSimpleUnitaryData E F A n`, with E
totally real, F totally complex and CM, quadratic over E, and the displayed
E-, F- and rational algebra structures and compatible scalar towers on A.
The algebra A is finite as a rational module. The CM input also includes
an imaginary quadratic field L, an embedding of L into F, a complex
embedding `τ₀` of L, and
`C : HarrisSignatureCharts D.toSecondKindInvolution n
(harrisCMSection E (algebraMap L F) τ₀)`.

The explicit assertions are pullback-tensor comparison preservation,
composition, unit coherence, associativity, unitor comparison and
symmetry; Picard-zero pullback, the Mumford-square assertion and universal
base change; duality naturality, polarization base change and relative
finite Weil transitions; `h : Global.RationalProfiniteIntegerAdeleComparison`;
and `htor : TorsionFiniteEtaleStatement.{0}`. In addition,

```text
q : CMRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor,
existence : RelativeDualSchemeExistenceStatement.{0},
geometry : RelativeDualSchemeGeometryStatement.{0},
hRigid : CMGeometricCoarseRigidity D C preservation composition
      unitCoherence associativity comparison symmetry stability square
      universality compatibility h htor U.obj
```

remain premises. Here U is the fixed `SmallCMLevel D`. Representability
is for the existing original CM moduli presheaf on
`ComponentwiseAdmissibleCMBaseCategory`, with its inherited componentwise
connected, locally Noetherian and geometric-point conditions. The tower
is the existing Yoneda construction `cmSchemeTower ... q`. This unit
does not discharge these assertions or assume a replacement cover,
associated sheaf, transition, exactness or comparison isomorphism.

The coefficient input is a number field K, a finite K-module W, an
algebraic representation `ρ` of
`D.rationalInvolution.baseChange K` on W, a rational finite place p,
and a natural scalar m with `hm : m ≠ 0`. The stable full lattice is the
one chosen by the imported Harris construction. All nonnegative
exponents, including zero, are allowed.

Write X for the original tower scheme at U, J for
`Scheme.smallEtaleTopology X`, and R for `HarrisCoefficientIntegers K p`.
R is the full integral product over all places of K above p. It is the
fixed scalar ring for the entire sequence, rather than one of the
exponent-dependent quotient rings.

## The actual finite kernel action

Use the existing diagrams

```text
Q = cmHarrisCoefficientGroups D ρ p U m hm,
M = cmHarrisCoefficientDiagram D ρ p U m hm,
Y = cmHarrisCoefficientEtaleDiagram ... q U ρ p m hm
      existence geometry hRigid.
```

At k the original cover Y_k is the scheme level at
`V_k = cmHarrisCoefficientLevel D ρ p U m hm k.unop`, with residual
group `Q_k = SmallCMResidualGroup D U V_k`. Its structural and transition
maps are the original forgetting maps. Its action retains the original
inverse-right transporter, and the coefficient action retains
`g ↦ unop(g)⁻¹`. The imported
`cmHarrisCoefficientEtaleDiagram_isFiniteGeometricTorsor` proves the
finite geometric torsor property for these very covers under the stated
premises; `cmHarrisCoefficientEtaleDiagram_coversTop` gives their
covering property.

For `f : i ⟶ j` in `ℕᵒᵖ`, so that `j.unop ≤ i.unop`, let

```text
φ_f : M_i ⟶ res(Q.map f)(M_j)
```

be `M.transition f` in the category of R-module actions of the fine
group Q_i. The target action is restricted along the actual residual
quotient map. On carriers, φ_f is the original lattice reduction that
keeps the same lattice representative at the lower exponent. If
I is `harrisCoefficientScalarIdeal K p m`, the carriers are the
existing full reductions Λ/I^kΛ.

`cmHarrisCoefficientTransitionKernel` is `kernel φ_f` in this action
category. Its action is therefore inherited from the actual fine
residual action. `cmHarrisCoefficientTransitionKernelModuleIso`
identifies its underlying module with the ordinary linear kernel of
`φ_f.hom.hom`: it composes kernel preservation by `Action.forget` with
`ModuleCat.kernelIsoKer`. No ideal-power description of this kernel is
assumed or proved.

`cmHarrisCoefficientTransitionKernel_finite` proves that its carrier is
finite. The source M_i is finite by
`cmHarrisCoefficientDiagram_finite`; the forgotten kernel inclusion is
monic and hence injective as a linear map. Finiteness follows by that
injection. The instance `cmHarrisCoefficientDiagram_transition_epi`
uses the already proved surjectivity of this same lattice reduction,
`ModuleCat.epi_iff_surjective`, and reflection of epimorphisms by the
faithful action-forgetful functor.

## Descent and exactness of the original transition

Let F_i be `etaleAssociatedFunctor (R := R) X (Y.action i)`. Define

```text
K_f   = cmHarrisCoefficientSystemKernelSheaf ... f
      = F_i(kernel φ_f),
inc_f = cmHarrisCoefficientSystemKernelInclusion ... f
      = F_i.map(kernel.ι φ_f).
```

Thus K_f is descended from the concrete kernel action independently of
the sheaf kernel of a desired transition. Its inclusion lands in the
original sheaf `A_i = (cmHarrisCoefficientSystem ...).obj i`.

Write τ_f for the existing system transition, β_f for `F_i.map φ_f`,
and α_f for the proved cover comparison from A_j to
`F_i(res(Q.map f)(M_j))`. By the original system construction,
`τ_f = β_f ≫ α_f⁻¹`.
`cmHarrisCoefficientSystemKernelInclusion_comp` proves
`inc_f ≫ τ_f = 0` by functoriality, the original module-kernel
condition, and this formula. The definition
`cmHarrisCoefficientReductionSequence` is the resulting short complex

```text
K_f --inc_f--> A_i --τ_f--> A_j.
```

Its second arrow is exactly `(cmHarrisCoefficientSystem ...).map f`.
The definition does not replace that arrow by an unspecified epimorphism.

`cmHarrisCoefficientReductionSequenceIso` compares this short complex
with `(ShortComplex.kernelSequence φ_f).map F_i`. The first two
components are identities, and the third is α_f⁻¹. The commuting
squares use the actual original transition formula.

`cmHarrisCoefficientReductionSequence_shortExact` proves short
exactness. First the coefficient kernel sequence is exact and its
second map is epi by the actual reduction-surjectivity result above.
For this specific original fine geometric torsor, the published
`etaleAssociatedFunctorPreservesFiniteLimits` and
`etaleAssociatedFunctorPreservesFiniteColimits` certify exactness of
F_i. Mathlib's `ShortComplex.ShortExact.map_of_exact` maps the
coefficient short exact sequence, and `ShortComplex.shortExact_of_iso`
transports it across the displayed comparison. The generic torsor
exactness proof is imported by Lean name from
[EtaleExact](../Coefficients/EtaleExact.md); it is not duplicated.
In particular, no invertibility of the residual group order in R is
required.

The instances `cmHarrisCoefficientSystem_map_epi` and
`cmHarrisCoefficientSystemKernelInclusion_mono` extract the epi and
mono conclusions for the actual original transition and inclusion.
They are statements in the category of module sheaves on J, not
surjectivity statements about sections over every site object.

## Kernel identification and finite constant model

`cmHarrisCoefficientSystemKernelIso` identifies the independently
descended K_f with `kernel τ_f`. It uses the limiting kernel fork
supplied by short exactness and uniqueness of a limit cone.
`cmHarrisCoefficientSystemKernelIso_hom_ι` proves the normalization

```text
KernelIso.hom ≫ kernel.ι τ_f = inc_f.
```

This specifies the inclusion as well as the kernel object. Its proof
is the component equation for `IsLimit.conePointUniqueUpToIso`.

`cmHarrisCoefficientSystemKernelTrivialization` is an isomorphism
between the pullback of K_f to the site over the original fine cover
Y_i and the pullback of the constant sheaf with module
`(kernel φ_f).V`. It applies
`constantAssociatedTrivializationOfSplitting` to the actual
`etaleTorsorSectionSplitting` for `Y.action i`. Together with the
proved finiteness of this module and the existing covering property of
Y_i, this supplies an explicit finite constant model on a covering
object. Localization here is `J.overPullback` to the site over Y_i.
It is not an asserted arbitrary-scheme inverse-image comparison.

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
The supplied five-page author errata list contains no correction to
these cited passages; this observation is limited to that supplied list.

The new kernel actions, descent, exact sequence, kernel comparison and
trivialization are internal categorical deductions from the published
[coefficient diagram](HarrisTaylorCMCoefficientDiagram.md),
[original sheaf system](HarrisTaylorCMCoefficientSystem.md), and
[generic torsor exactness](../Coefficients/EtaleExact.md), using
Mathlib's action kernels, module kernels and short exact complexes.
They are not attributed to a separately stated theorem in those source
passages. The allowance of any nonzero natural scalar and of exponent
zero is an extension supplied by the imported arithmetic construction.

No applicable representability, dual-existence, coarse-rigidity or
source canonical-model theorem is proved here. This unit does not
identify the kernel with an ideal-power quotient, prove finite freeness
or exactness of global sections, supply arbitrary scheme inverse image,
prove independence of the lattice, or construct the full lisse adic
limit and cohomology. Those are separate obligations of the surrounding
development.

The code and prose in this pair are by Worker 57, using published
generic interfaces. The pinned environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
