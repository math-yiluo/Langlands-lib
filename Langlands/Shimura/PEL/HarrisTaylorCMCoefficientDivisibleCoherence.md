# Coherent inclusions on the original CM coefficient sheaves

Author: Worker 57.

This internal construction proves the composition and mixed reduction laws for
the normalized inclusions of the existing original CM coefficient sheaves.
It extends those inclusions to equal exponents, constructs a direct functor on
all natural exponents, and constructs natural maps between the existing
inverse tower and each of its finite shifts. No coefficient object, reduction
or cover is replaced.

Write T for the original inverse tower, A_r for `T.obj (op r)`, and
`j_(s,r) : A_s ⟶ A_r` for its reduction when r ≤ s. The constructed inclusions
`i_(r,s) : A_r ⟶ A_s` satisfy

```text
j_(s,r) ≫ i_(r,s) = (m^(s-r)) • id_(A_s),
i_(r,s) ≫ j_(s,r) = (m^(s-r)) • id_(A_r),
i_(r,r) = id_(A_r),
i_(r,s) ≫ i_(s,t) = i_(r,t)             (r ≤ s ≤ t).
```

The notation `≫` means composition in the order displayed. Every inclusion
is monic. For r < s it is definitionally the previously constructed
`cmHarrisCoefficientDivisibleInclusion`. These are proved equations for the
specified original sheaves, rather than extra compatibility assumptions.

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

Here `U : SmallCMLevel D`. Representability concerns the original moduli
presheaf on `ComponentwiseAdmissibleCMBaseCategory`, retaining its connected
component, locally Noetherian and geometric point conditions. Set
`X = (cmSchemeTower ... q).obj U` and `J = Scheme.smallEtaleTopology X`.
This module does not discharge these premises.

The coefficient data are a number field K, a finite K-module W, an algebraic
representation `ρ` of `D.rationalInvolution.baseChange K` on W, a rational
finite place p, and a natural scalar m with `hm : m ≠ 0`. Set

```text
R = HarrisCoefficientIntegers K p,
T = cmHarrisCoefficientSystem D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U
      ρ p m hm existence geometry hRigid.
```

R is the full product of the valuation rings at coefficient places above p.
The published coefficient diagram retains the full stable lattice for
`CompactOpenLevel.inverseOpposite U.obj`, its quotients by `(m)^r`, and the
inverse-unop residual action. Each A_r is the existing associated sheaf on
the original coefficient-kernel cover of X. Its original finite geometric
torsor property and exact association are reused under the displayed
premises. All constructions below lie in `Sheaf J (ModuleCat.{0} R)` or in
functor categories valued in that category.

## Equal exponents, normalization and composition

`cmHarrisCoefficientInclusionLE` uses the same scalar cokernel formula as the
published strict inclusion, now for every r ≤ s:

```text
i_(r,s) = scalarIso_(s,r).inv ≫
  cokernel.desc (powSMul m r A_s) (powSMul m (s-r) A_s) (zero-composite proof).
```

Here `scalarIso_(s,r) : cokernel (powSMul m r A_s) ≅ A_r` is the published
isomorphism for the actual original reduction. `powSMul m a B` means
`(m^a : ℕ) • 𝟙 B`. The formula descends because r + (s-r) = s and
multiplication by m^s annihilates A_s. The lemma
`cmHarrisCoefficientInclusionLE_of_lt` identifies it definitionally with the
published inclusion for r < s; proof irrelevance identifies the displayed
inequality proofs.

`cmHarrisCoefficientInclusionLE_normalization` rewrites j as the cokernel
projection followed by `scalarIso.hom`, cancels adjacent isomorphism maps,
and applies `cokernel.π_desc`. This proves the first displayed normalization.
Since every original j is epi,
`cmHarrisCoefficientInclusionLE_unique` proves that any map with this same
normalization equals the constructed inclusion. The map is therefore fixed
by the specified reduction and scalar power.

`cmHarrisCoefficientInclusionLE_refl` specializes normalization to r = s.
The inverse tower sends the identity index arrow to the identity, and
`powSMul m 0` is the identity. Thus the equal-exponent inclusion is the
identity, without an arbitrary equality-case choice.
`cmHarrisCoefficientInclusionLE_reduction` proves the reverse normalization:
precompose both proposed maps A_r → A_r with epi j_(s,r), apply the first
normalization, and commute the scalar endomorphism past j.

`cmHarrisCoefficientReduction_trans` records the original inverse tower's
composition law for the explicitly indexed reduction arrows.
`cmHarrisCoefficientInclusionLE_trans` then precomposes the desired inclusion
composition with epi j_(t,r). Factor that reduction through A_s. Apply the
normalization for i_(r,s), commute its scalar past j_(t,s), then apply the
normalization for i_(s,t). The two scalar powers compose to exponent
(s-r) + (t-s) = t-r. The normalization for i_(r,t) gives the same map, so
epimorphic cancellation proves composition.

`cmHarrisCoefficientDirectSystem` is the resulting functor

```text
ℕ ⥤ Sheaf J (ModuleCat.{0} R),
r ↦ A_r,
(homOfLE hrs) ↦ i_(r,s).
```

Its identity and composition fields are the proved reflexivity and
transitivity equations. The instance
`cmHarrisCoefficientInclusionLE_mono` uses the published strict monicity
when r < s and identity monicity when r = s. The theorem
`cmHarrisCoefficientDivisibleInclusion_trans` specializes the composition
law to the existing published strict inclusions.

## Compatibility with every finite shift of the inverse system

For s ≤ r and every k ≥ 0,
`cmHarrisCoefficientInclusionLE_shift_naturality` proves the square

```text
A_r       --i_(r,r+k)--> A_(r+k)
 | j_(r,s)                | j_(r+k,s+k)
 v                        v
A_s       --i_(s,s+k)--> A_(s+k).
```

Precompose with epi j_(r+k,r). The top route becomes multiplication by m^k
followed by j_(r+k,s+k). Functorial reduction factors the other route
through A_(s+k), where its normalization becomes j_(r+k,s+k) followed by
multiplication by m^k. Scalar naturality equates the two composites.

`cmHarrisCoefficientShiftedSystem k` reindexes the existing inverse tower
by the opposite of the monotone functor r ↦ r+k. Its objects are A_(r+k)
and its arrows are the original reductions between these exponents.
`cmHarrisCoefficientShiftInclusion k : T ⟶ shifted k` has component
`i_(r,r+k)`. Its naturality field is the proved square above, with the
orientation required for natural transformations.
`cmHarrisCoefficientShiftReduction k : shifted k ⟶ T` has component
`j_(r+k,r)`. Its naturality field follows from functorial reduction.

The last two theorems express both normalization equations as equalities of
natural transformations:

```text
shiftInclusion k ≫ shiftReduction k = powSMul m k T,
shiftReduction k ≫ shiftInclusion k = powSMul m k (shifted k).
```

The right sides are scalar endomorphisms in the respective functor category,
with the specified scalar endomorphism at each component. The implemented
proofs use extensionality at each index and the two proved normalization
equations; `(r+k)-r = k` supplies their exponents.

All exponents are nonnegative, including zero, and k may be zero. The scalar
m may be one. No primality assumption, inverse residual group order, or
infinite-limit argument is used. The new direct system and shifted natural
maps retain the actual original sheaves and reductions; this module does not
identify the direct system with any separately constructed rational torsion
quotient or prove a direct- or inverse-limit comparison.

## Original sources, internal provenance and retained scope

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), Section 2, printed p.304, one-based PDF p.6, supplies divisible
systems and row (2.1). Section 3, printed pp.306–308, PDF pp.8–10, supplies
the algebraic representation, full local scalar algebra, stable integral
lattice, inverse function-equivariance (3.7), and the normal congruence
quotient factorization preceding (3.8). Registered source:
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), III.1, printed pp.90–91, one-based PDF pp.98–99, supplies the
original small-level moduli, right frame composition and normal finite-etale
covers. III.2, printed pp.94–96, PDF pp.102–104, supplies stable-lattice
torsion coefficients, inverse-equivariant functions and compatible
coefficient/cover maps. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The equal-exponent cokernel formula, normalization uniqueness, direct functor,
mixed square, shifted natural maps and their scalar composites are internal
deductions from the published original CM coefficient system and scalar
cokernel normalization. They are not attributed as separately quoted results
of these passages. The cited sources determine the underlying coefficient
and geometric setting. The implemented proof uses the
[original CM inverse system](HarrisTaylorCMCoefficientSystem.md),
[original scalar cokernel](HarrisTaylorCMCoefficientScalar.md), and
[published normalized inclusions and divisible system](HarrisTaylorCMCoefficientDivisible.md).

The original representability, dual existence and geometry, rigidity and
other named premises remain assumptions. Actual geometric existence,
canonical-model comparisons, lattice-choice independence, adic limits,
exactness of global sections, and the comparison with Harris's analytic
smooth-equivariant complexes remain separate obligations. This focused
coherence construction does not complete the broader unitary Shimura task.

The Lean and paired English prose are by Worker 57 using published
interfaces. The environment is Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
