# Scalar cokernels of original CM coefficient reductions

Author: Worker 57.

This internal construction identifies each actual transition of the original
CM coefficient sheaf system as a scalar cokernel. For `f : i ⟶ j` in
`ℕᵒᵖ`, write `a = i.unop` and `b = j.unop`, so `b ≤ a`. If `A_k` is the
original coefficient sheaf at k, the construction gives

```text
cokernel ((m^b : ℕ) • 𝟙 A_i) ≅ A_j.
```

The cokernel projection, followed by this isomorphism, is exactly the
original transition `A.map f`. The construction derives this from the
actual full lattice reductions and exact association on the original fine
coefficient cover.

## Inputs and retained premises

All carriers have universe zero. The unitary input is
`D : CentralSimpleUnitaryData E F A n`: E is totally real, F is totally
complex and CM and quadratic over E, and the E-, F- and rational algebra
structures on A have the displayed compatible scalar towers. A is finite
as a rational module. The signature input includes an imaginary quadratic
field L, an L-algebra structure on F, a complex embedding `τ₀` of L and
`C : HarrisSignatureCharts D.toSecondKindInvolution n
(harrisCMSection E (algebraMap L F) τ₀)`.

The existing pullback-tensor comparison, composition, unit coherence,
associativity, unitor comparison and symmetry assertions remain explicit,
as do Picard-zero pullback, the Mumford-square assertion, universal base
change, duality naturality, polarization base change and relative finite
Weil transitions. The parameters also retain
`h : Global.RationalProfiniteIntegerAdeleComparison` and
`htor : TorsionFiniteEtaleStatement.{0}`. For the original scheme tower
and fixed `U : SmallCMLevel D`, the additional premises are

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

Representability concerns the existing original moduli presheaf on
`ComponentwiseAdmissibleCMBaseCategory`, with its inherited connected
component, locally Noetherian and geometric-point conditions. The tower is
the existing Yoneda construction `cmSchemeTower ... q`; none of these
geometric assertions is proved by this unit.

The coefficient data are a number field K, a finite K-module W, an
algebraic representation `ρ` of `D.rationalInvolution.baseChange K` on W,
a rational finite place p and a natural scalar m with `hm : m ≠ 0`.
The lattice is the actual chosen full stable Harris lattice. Every
nonnegative exponent is allowed, including zero, and m need not be prime.

Write X for the original scheme level at U, J for its small-etale topology
and R for `HarrisCoefficientIntegers K p`, the full integral product over
places of K above p. Let Q, M and Y be the published
`cmHarrisCoefficientGroups`, `cmHarrisCoefficientDiagram` and
`cmHarrisCoefficientEtaleDiagram` for these inputs. The covers in Y are
exactly the original coefficient-kernel levels with their original
forgetting maps. Their finite geometric torsor property is the imported
proved result under the displayed geometric premises. The coefficient
action retains the original inverse-unop convention.

## Scalar-image exactness on the actual reductions

For the chosen f let `φ = M.transition f`. It is a morphism from the
fine action M_i to M_j restricted along the actual residual quotient
`Q.map f`. Its carriers are the full lattice quotients
`Λ / I^a Λ → Λ / I^b Λ`, where `I = (m)` in R, and the map keeps the
same lattice representative.

`cmHarrisCoefficientDiagram_scalar_comp` proves

```text
((m^b : ℕ) • 𝟙 M_i) ≫ φ = 0.
```

After forgetting the action, choose a lattice representative y. The
composite is the class of `(m^b : ℕ) • y` in `Λ / I^b Λ`. The published
`mem_principalPower_smul_top` identifies membership in `I^b Λ` with
scalar divisibility. The witness is y itself, using
`Nat.cast_pow` and `Nat.cast_smul_eq_nsmul` to identify the natural
scalar with `(m : R)^b`.

`cmHarrisCoefficientScalarActionSequence` is the resulting short complex

```text
M_i --(m^b)•id--> M_i --φ--> res(Q.map f)(M_j).
```

`cmHarrisCoefficientScalarActionSequence_exact` proves exactness. The
faithful action-forgetful functor preserves homology, so exactness is
reflected from modules by `ShortComplex.exact_map_iff_of_faithful`.
Mathlib's `moduleCat_exact_iff` reduces the assertion to a preimage for
each element of the kernel. Choose y representing a fine quotient element
whose coarse reduction is zero. Then `y ∈ I^b Λ`, hence
`(m : R)^b • z = y` for a lattice element z. The class of z in the fine
quotient is the required scalar preimage. This uses no injectivity of
multiplication on Λ or on its reductions.

## Exact descent to the original sheaf transition

Let B be `etaleAssociatedFunctor (R := R) X (Y.action i)`. By the existing
system construction, `A_i = B.obj M_i` and

```text
A.map f = B.map φ ≫ α⁻¹,
```

where α is the proved `etaleAssociatedComparisonIso` component for f.
Additivity gives `B.map ((m^b) • 𝟙 M_i) = (m^b) • 𝟙 A_i`.
`cmHarrisCoefficientSystem_scalar_comp` maps the action-level zero
composite through B and composes with α⁻¹. Its equation is

```text
((m^b : ℕ) • 𝟙 A_i) ≫ A.map f = 0.
```

`cmHarrisCoefficientScalarSequence` uses these two actual arrows.
`cmHarrisCoefficientScalarSequenceIso` identifies it with the action
sequence mapped through B. Its first two components are identities and
its third component is α⁻¹. The first commuting square is additivity and
preservation of identity; the second is the original transition formula.

`cmHarrisCoefficientScalarSequence_exact` installs the published finite
limit and finite colimit preservation results for B on this original
finite geometric torsor, maps the action exactness and transports it
across that short-complex isomorphism. It proves exactness in the category
of R-module sheaves on J. No averaging over Q_i or invertibility of its
order is used. The scalar arrow is not asserted to be monic.

## Normalized cokernel construction

The existing `cmHarrisCoefficientSystem_map_epi` supplies epimorphy of the
actual transition. Exactness and this epimorphy give
`cmHarrisCoefficientSystemScalarIsCokernel`, an `IsColimit` of the
cokernel cofork whose projection is `A.map f` and whose relation is
multiplication by `m^b` on A_i. The Lean construction is
`ShortComplex.Exact.gIsCokernel` applied to the displayed exact sequence.

`cmHarrisCoefficientSystemScalarCokernelIso` compares this cofork with the
categorically chosen cokernel by uniqueness of colimits. The theorem
`cmHarrisCoefficientSystemScalarCokernelIso_π_hom` proves

```text
cokernel.π ((m^b : ℕ) • 𝟙 A_i) ≫ ScalarCokernelIso.hom = A.map f.
```

It is the component equation for
`IsColimit.coconePointUniqueUpToIso`, so the comparison retains the
specific original transition as well as the coarse object. In particular,
any sheaf morphism out of A_i killing this scalar map factors uniquely
through the actual transition, by the constructed cokernel property.

## Original sources and internal provenance

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), Section 3, printed pp.306–308, one-based PDF pp.8–10, supplies the
algebraic coefficient representation, stable integral lattice, inverse
function-equivariance (3.7), and normal congruence quotient factorization
before (3.8). Registered source:
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, PDF pp.98–99, supplies the
original small-level moduli, right frame composition and normal
finite-etale covers. III.2, printed pp.94–96, PDF pp.102–104, supplies
stable-lattice torsion coefficients, inverse-equivariant functions and
compatible coefficient/cover maps. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The scalar-image sequence, its exact descent and its normalized cokernel
are internal deductions. They are not separately quoted theorems of these
passages. The construction imports the actual
[CM coefficient diagram](HarrisTaylorCMCoefficientDiagram.md),
[original sheaf system](HarrisTaylorCMCoefficientSystem.md),
[existing transition epimorphy](HarrisTaylorCMCoefficientExact.md),
[principal-power divisibility](../Coefficients/HarrisReduction.md) and
[exact torsor association](../Coefficients/EtaleExact.md). The allowance of
an arbitrary nonzero natural scalar and exponent zero comes from those
published arithmetic constructions.

This unit provides a finite-stage cokernel in the sheaf category. It does
not prove exactness of global sections, freeness or lattice independence,
construct an infinite adic limit, or discharge the retained geometric
existence, representability, rigidity and canonical-model obligations.
Generic adic-system and arbitrary inverse-image constructions remain
separate from this concrete original-CM specialization.

The code and paired prose are by Worker 57, using published interfaces.
The environment is Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
