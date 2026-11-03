# Complementary scalar powers on original CM coefficient sheaves

Author: Worker 57.

This internal construction proves the finite-stage scalar-flatness condition
for the existing original CM coefficient sheaves. If `A_k` is the sheaf at
exponent k, then multiplication by `m^k` is zero on `A_k`, and for every pair
of nonnegative integers a and b the sequence

```text
A_(a+b) --(m^a)•id--> A_(a+b) --(m^b)•id--> A_(a+b)
```

is exact at its middle term in the category of integral module sheaves.
Here “scalar flatness” means this complementary-power condition, as in
`DivisibleSystem.flat`. This unit makes no assertion of flatness over an
arbitrary scalar ring. It derives the condition from cancellation on the
actual full Harris lattice and exact association on the original coefficient
cover.

## Inputs and actual objects

All carriers have universe zero. The arithmetic input is
`D : CentralSimpleUnitaryData E F A n`, with E a totally real number field,
F a totally complex CM number field quadratic over E, compatible E-, F-
and rational algebra structures on A, and A finite over the rationals.
The signature data retain an imaginary quadratic number field L, an
L-algebra structure on F, an embedding `τ₀ : L →+* ℂ` and
`C : HarrisSignatureCharts D.toSecondKindInvolution n
(harrisCMSection E (algebraMap L F) τ₀)`.

The sheaf assertions retain the named pullback-tensor comparison,
composition, unit coherence, associativity, unitor comparison and symmetry
premises, Picard-zero pullback, the Mumford-square assertion, universal base
change, duality naturality, polarization base change and relative finite
Weil transition premises. They also retain
`h : Global.RationalProfiniteIntegerAdeleComparison` and
`htor : TorsionFiniteEtaleStatement.{0}`. The geometric premises are

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

The fixed level is `U : SmallCMLevel D`. Representability concerns the
original moduli presheaf on `ComponentwiseAdmissibleCMBaseCategory`, with
its connected-component, locally Noetherian and geometric-point
conditions. X is its existing scheme level `(cmSchemeTower ... q).obj U`,
and J is `Scheme.smallEtaleTopology X`. This unit retains these geometric
assertions as premises.

The coefficient data are a number field K, a finite K-module W, an
algebraic representation `ρ` of `D.rationalInvolution.baseChange K` on W,
a rational finite place p, and a natural scalar m with `hm : m ≠ 0`.
R denotes `HarrisCoefficientIntegers K p`, the full product of the
valuation rings at every coefficient place above p. With
`ordinaryLevel = CompactOpenLevel.inverseOpposite U.obj`, let

```text
Λ = (harrisLatticeAction ρ p ordinaryLevel).V,
M = cmHarrisCoefficientDiagram D ρ p U m hm,
Y = cmHarrisCoefficientEtaleDiagram ...,
A = cmHarrisCoefficientSystem ....
```

Λ is the actual full stable lattice in
`(K ⊗[ℚ] Global.FiniteCompletion ℚ p) ⊗[K] W`. The carrier of `M.action
(op k)` is `Λ / (m)^k Λ`; its residual action retains the original
inverse-unop convention. `Y.action (op k)` is the original cover at the
coefficient-kernel level, and `A.obj (op k)` is the existing sheaf
associated to M on that cover. Its finite geometric torsor property is
the imported proved result under the displayed premises. No replacement
cover or replacement coefficient object is chosen here.

## Cancellation and exactness on the full lattice reductions

`cmHarrisLattice_nsmul_injective` proves that for every nonzero natural
integer r, the map `x ↦ r • x` on Λ is injective. The ambient tensor module
is a vector space over the characteristic-zero field K, so
`IsAddTorsionFree.of_isTorsionFree K` makes its additive group torsion-free.
Equality in Λ is reflected by its subtype inclusion into that space;
`nsmul_right_injective` then cancels r. This lemma requires only the
arithmetic lattice data, not the geometric premises.

`cmHarrisCoefficientDiagram_powSMul_eq_zero` proves

```text
powSMul m k (M.action (op k)) = 0.
```

The imported `powSMul m k` is `(m^k : ℕ) • 𝟙`. The proof forgets the
action and lifts a quotient element to a lattice representative y.
The resulting class of `m^k • y` is zero because it belongs to `(m)^k Λ`.
The published `mem_principalPower_smul_top` supplies the divisibility
description; the witness is y. `Nat.cast_pow` and
`Nat.cast_smul_eq_nsmul` identify the natural and ring scalar actions.

`cmHarrisCoefficientPowerActionSequence` forms the short complex with
arrows `powSMul m a` and `powSMul m b` on `M.action (op (a+b))`.
Its zero-composite relation follows from `powSMul_comp_powSMul` and the
preceding annihilation result.
`cmHarrisCoefficientPowerActionSequence_exact` proves its exactness.
The faithful action-forgetful functor reflects exactness through
`ShortComplex.exact_map_iff_of_faithful`; `moduleCat_exact_iff` then asks
for a scalar preimage of every kernel element.

Choose a representative y of a class killed by `m^b`. Its vanishing
means that there is a lattice element z with

```text
m^(a+b) • z = m^b • y.
```

Rewrite the left side as `m^b • (m^a • z)`. Since m is nonzero,
`m^b ≠ 0`, and lattice cancellation gives `m^a • z = y`.
The class of z in the same quotient is the required preimage.
This proves equality of the image of the first scalar map and the
kernel of the second, without claiming either map is injective.

## Exact association on the original cover

`cmHarrisCoefficientSystem_powSMul_eq_zero` proves
`powSMul m k (A.obj (op k)) = 0`. For the association functor B on
`Y.action (op k)`, additivity gives
`B.map (powSMul m k M_k) = powSMul m k (B.obj M_k)`.
Mapping the action-level zero equation through B therefore proves
annihilation on the existing sheaf.

`cmHarrisCoefficientPowerSequence` forms the sheaf short complex displayed
at the start. `cmHarrisCoefficientPowerSequenceIso` identifies it with
the action short complex mapped by

```text
etaleAssociatedFunctor (R := R) X (Y.action (op (a+b))).
```

All three components of this isomorphism are identities. Both commuting
squares are the imported additive-functor identity `map_powSMul`.
Thus the comparison preserves the specified scalar endomorphisms.

`cmHarrisCoefficientPowerSequence_exact` uses the published preservation
of finite limits and finite colimits by association on this original
finite geometric torsor. It maps action exactness and transports it
along the short-complex isomorphism. The result is exactness of the
original small-etale module sheaves, with no assumption that the residual
group order is invertible.

All exponents are nonnegative, including a or b equal to zero.
For exponent zero the quotient is zero; for a zero power scalar the
endomorphism is the identity. The proofs also allow m equal to one,
when every reduction is zero. They require no primality hypothesis on m.

## Original sources and internal provenance

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), Section 3, printed pp.306–308, one-based PDF pp.8–10, supplies
the algebraic representation, stable integral lattice, inverse
function-equivariance (3.7), and normal congruence quotient factorization
preceding (3.8). Registered source:
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, PDF pp.98–99, supplies
the original small-level moduli, frame composition on the right and
normal finite-etale covers. III.2, printed pp.94–96, PDF pp.102–104,
supplies stable-lattice torsion coefficients, inverse-equivariant
functions and compatible coefficient/cover maps. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

Lattice cancellation, the complementary-power short complexes, and
their exactness after association are internal deductions in this unit,
not separately quoted theorems of these source passages. The arbitrary
nonzero natural scalar and exponent-zero cases come from the published
arithmetic constructions. This module reuses the
[actual full lattice](../Coefficients/HarrisLattice.md),
[principal-power divisibility](../Coefficients/HarrisReduction.md),
[original CM coefficient diagram](HarrisTaylorCMCoefficientDiagram.md),
[original sheaf system](HarrisTaylorCMCoefficientSystem.md),
[exact torsor association](../Coefficients/EtaleExact.md), and
[generic scalar notation](../../Cohomology/DivisibleSystem.md).

This finite-stage result does not construct inclusions between different
exponents or a complete `DivisibleSystem`, form an infinite adic limit,
prove exactness of global sections or independence of lattice choices,
or discharge geometric existence, representability, rigidity and
canonical-model obligations.

The code and paired prose are by Worker 57, using published interfaces.
The environment is Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
