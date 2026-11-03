# Divisible system on the original CM coefficient sheaves

Author: Worker 57.

This construction equips the existing original CM coefficient sheaf tower with
its varying-exponent inclusions and proves all fields of the published
`Langlands.Cohomology.DivisibleSystem` structure. Write `A_k` for its component
at exponent k and `j_(s,r) : A_s ⟶ A_r` for its existing reduction, for r ≤ s.
For every r < s the constructed map `i_(r,s) : A_r ⟶ A_s` satisfies

```text
j_(s,r) ≫ i_(r,s) = (m^(s-r)) • id_(A_s),
0 ⟶ A_r --i_(r,s)--> A_s --j_(s,s-r)--> A_(s-r) ⟶ 0.
```

The second row is short exact in the abelian category of integral module
sheaves on the small-etale site of the existing CM scheme level. The assembled
system has exactly the original inverse tower, including its reduction maps.
Its inclusions are constructed by scalar cokernel descent; they are not
supplied as additional geometric or sheaf data.

## Inputs and original objects

All arithmetic carriers have universe zero. The input
`D : CentralSimpleUnitaryData E F A n` retains a totally real number field E,
a totally complex CM number field F quadratic over E, compatible E-, F- and
rational algebra structures on A, and finite rational dimension of A. The
signature input retains an imaginary quadratic number field L, an L-algebra
structure on F, an embedding `τ₀ : L →+* ℂ` and
`C : HarrisSignatureCharts D.toSecondKindInvolution n
(harrisCMSection E (algebraMap L F) τ₀)`.

The construction retains the named pullback-tensor comparison, composition,
unit coherence, associativity, unitor comparison and symmetry assertions;
Picard-zero pullback, the Mumford-square assertion, universal base change,
duality naturality, polarization base change and relative finite Weil
transition assertions; `h : Global.RationalProfiniteIntegerAdeleComparison`;
and `htor : TorsionFiniteEtaleStatement.{0}`. Its geometric premises remain

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

Here `U : SmallCMLevel D`. The representability assertion concerns the original
moduli presheaf on `ComponentwiseAdmissibleCMBaseCategory`, retaining its
connected-component, locally Noetherian and geometric-point conditions. Set
`X = (cmSchemeTower ... q).obj U` and `J = Scheme.smallEtaleTopology X`.
No assertion listed above is discharged by this module.

The coefficient input is a number field K, a finite K-module W, an algebraic
representation `ρ` of `D.rationalInvolution.baseChange K` on W, a rational
finite place p and a natural scalar m with `hm : m ≠ 0`. Let

```text
R = HarrisCoefficientIntegers K p,
T = cmHarrisCoefficientSystem D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U
      ρ p m hm existence geometry hRigid,
A_k = T.obj (op k).
```

R is the full product of the valuation rings at coefficient places above p.
The published coefficient diagram uses the actual full stable lattice for
`CompactOpenLevel.inverseOpposite U.obj`, its quotients by `(m)^k`, and the
inverse-unop residual action. Each `A_k` is the existing sheaf associated on
the original coefficient-kernel cover of X. Its reduction `j_(s,r)` is
`T.map (homOfLE hrs).op` for `hrs : r ≤ s`. The original finite geometric
torsor theorem and exact association remain the published dependencies under
the displayed premises. The current module does not choose another cover,
coefficient sheaf or tower.

## Cokernel-defined inclusions

The published scalar construction supplies

```text
scalarIso_(s,r) : cokernel (powSMul m r A_s) ≅ A_r,
cokernel.π (powSMul m r A_s) ≫ scalarIso_(s,r).hom = j_(s,r).
```

Here `powSMul m r A_s` is `(m^r : ℕ) • 𝟙 A_s`. The published finite-stage
flatness construction supplies `powSMul m s A_s = 0` and exactness of the
complementary scalar powers. For r < s, the composite of multiplication by
`m^r` and `m^(s-r)` on `A_s` is zero, since r + (s-r) = s.
`cmHarrisCoefficientDivisibleInclusion` defines

```text
i_(r,s) = scalarIso_(s,r).inv ≫
  cokernel.desc (powSMul m r A_s) (powSMul m (s-r) A_s) (zero-composite proof).
```

Thus the original transition's cokernel property, rather than an arbitrary
choice of inclusion, defines the map.
`cmHarrisCoefficientDivisibleInclusion_normalization` rewrites the transition
as the cokernel projection followed by `scalarIso.hom`, cancels the adjacent
isomorphism components and applies `cokernel.π_desc`. This proves the first
displayed equation, including its reassociated form.

`cmHarrisCoefficientDivisibleInclusion_mono` uses exactness of

```text
A_s --(m^r)•id--> A_s --(m^(s-r))•id--> A_s.
```

It specializes complementary-power exactness at r + (s-r) = s, applies
`ShortComplex.Exact.mono_cokernelDesc`, and composes that monomorphism with
`scalarIso.inv`. No scalar endomorphism of the torsion quotient is claimed
to be injective.

`cmHarrisCoefficientDivisibleInclusion_comp` proves
`i_(r,s) ≫ j_(s,s-r) = 0`. Cancel the epimorphism `j_(s,r)` on the left,
apply normalization, then use the published equation that multiplication by
`m^(s-r)` followed by the transition to exponent s-r is zero.
`cmHarrisCoefficientDivisibleSequence` uses these actual arrows and this
zero-composite proof to form the original short complex.

## Exact rows and the complete system

`cmHarrisCoefficientDivisibleSequenceComparison` constructs a morphism of
short complexes

```text
A_s --(m^(s-r))•id--> A_s --j_(s,s-r)--> A_(s-r)
 | j_(s,r)                   | id                | id
 v                           v                   v
A_r ------i_(r,s)-------> A_s --j_(s,s-r)--> A_(s-r).
```

The top row is the published `cmHarrisCoefficientScalarSequence` for the
actual transition to exponent s-r. Its first square is precisely the
normalization equation; its second square is the identity equation.
`cmHarrisCoefficientDivisibleSequence_exact` uses epimorphy of the first
component, invertibility of the middle component and monomorphy of the last
component in `ShortComplex.exact_iff_of_epi_of_isIso_of_mono`. Exactness of the
published top row therefore proves exactness of the constructed bottom row.
`cmHarrisCoefficientDivisibleSequence_shortExact` combines this exactness,
the proved monicity of the inclusion and the published epimorphy of the
original transition.

`cmHarrisCoefficientDivisibleSystem` applies the published
`DivisibleSystem.ofFlat` to T, the constructed inclusions, the original
annihilation result, the proved zero composites and short exact rows, and the
published complementary-power exactness. The generic constructor derives its
torsion condition from these inputs: the short complex

```text
A_r --i_(r,s)--> A_s --(m^r)•id--> A_s
```

is exact. Together with monicity this identifies `A_r` with the kernel of
multiplication by `m^r` on `A_s`. Its proof refines generalized elements using
complementary scalar exactness and then the short exact row; the current
module reuses that published argument.

The assembled object has type

```text
DivisibleSystem (Sheaf J (ModuleCat.{0} R)) m.
```

`cmHarrisCoefficientDivisibleSystem_tower` and
`cmHarrisCoefficientDivisibleSystem_inclusion` are definitional equalities.
The former retains every original component and reduction; the latter retains
the normalized cokernel inclusions just constructed. All exponents are
nonnegative, including r = 0, and m = 1 is allowed. The zero component is zero
by defining-power annihilation. No primality of m or invertibility of a
residual group order is required.

## Original sources, provenance and scope

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), Section 2, printed p.304, one-based PDF p.6, defines divisible systems,
the torsion identification and the short exact row (2.1). The published
categorical `DivisibleSystem` renders the scalar freeness condition by
complementary-power exactness. This module constructs that categorical
structure on the original integral coefficient sheaves; it does not assert
that they are free modules over an arbitrary coefficient ring.
Section 3, printed pp.306–308, PDF pp.8–10, supplies the algebraic
representation, full local scalar algebra, stable integral lattice, inverse
function-equivariance (3.7), and normal congruence quotient factorization
preceding (3.8). Registered source:
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), III.1, printed pp.90–91, one-based PDF pp.98–99, supplies the original
small-level moduli, right frame composition and normal finite-etale covers.
III.2, printed pp.94–96, PDF pp.102–104, supplies stable-lattice torsion
coefficients, inverse-equivariant functions and compatible coefficient/cover
maps. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The scalar cokernel descent, its normalization, the comparison of short
complexes and its specialization of the generic divisible-system constructor
are internal deductions. They are not attributed as separate results quoted
from these passages. The proof uses the published
[original coefficient system](HarrisTaylorCMCoefficientSystem.md),
[scalar cokernel construction](HarrisTaylorCMCoefficientScalar.md),
[complementary scalar powers](HarrisTaylorCMCoefficientFlat.md), and
[generic constructor and derived torsion condition](../../Cohomology/DivisibleSystem/Cokernel.md).
The construction is conditional on the exact geometric premises above.
Representability, actual geometric existence, source rigidity, canonical-model
comparisons, adic limits, exactness of global sections and independence of
lattice choices remain separate obligations. In particular, a finite-level
small-etale sheaf system is not here identified with an analytic system of
smooth equivariant complexes from Harris Section 2.

The Lean and paired English prose are by Worker 57 using published interfaces.
The environment is Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
