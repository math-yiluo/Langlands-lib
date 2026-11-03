# Ordinary cohomology of the original CM coefficient tower

Author: Worker 57.

This internal construction applies the existing small-etale derived-section
and cohomology functors to the actual original CM coefficient sheaves and
their specified reductions. It constructs the resulting inverse diagrams,
compares degree zero with global sections, and transports the finite-shift
maps and their scalar identities to every nonnegative cohomological degree.
The scheme in this module is the original level over F. Its geometric base
change to an algebraic closure of F is a separate construction.

## Inputs and original coefficient sheaves

All arithmetic carriers have universe zero. The input
`D : CentralSimpleUnitaryData E F A n` retains a totally real number field E,
a totally complex CM number field F quadratic over E, compatible E-, F- and
rational algebra structures on A, and finite rational dimension of A. The
signature input retains an imaginary quadratic number field L, an L-algebra
structure on F, an embedding `τ₀ : L →+* ℂ` and
`C : HarrisSignatureCharts D.toSecondKindInvolution n
(harrisCMSection E (algebraMap L F) τ₀)`.

The named premises are the pullback-tensor comparison, composition, unit
coherence, associativity, unitor comparison and symmetry assertions;
Picard-zero pullback, the Mumford-square assertion, universal base change,
duality naturality, polarization base change and relative finite Weil
transition assertions; `h : Global.RationalProfiniteIntegerAdeleComparison`;
and `htor : TorsionFiniteEtaleStatement.{0}`. The following geometric
premises also remain explicit, with `U : SmallCMLevel D`:

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

Representability is the existing assertion for the original moduli presheaf
on `ComponentwiseAdmissibleCMBaseCategory`, with its connected-component,
locally Noetherian and geometric-point conditions. This module does not prove
any of these named premises or supply arbitrary schemes as substitutes.

The coefficient data are a number field K, a finite K-module W, an algebraic
representation `ρ` of `D.rationalInvolution.baseChange K` on W, a rational
finite place p, and a natural scalar m with `hm : m ≠ 0`. Set

```text
X = (cmSchemeTower ... q).obj U,
J = Scheme.smallEtaleTopology X,
R = HarrisCoefficientIntegers K p,
T = cmHarrisCoefficientSystem D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U
      ρ p m hm existence geometry hRigid,
A_r = T.obj (op r).
```

R is the full product of the valuation rings at coefficient places above p.
The [original coefficient system](HarrisTaylorCMCoefficientSystem.md)
retains the stable lattice for `CompactOpenLevel.inverseOpposite U.obj`,
its quotients by `(m)^r`, and the inverse-unop residual action. Each A_r is
the associated module sheaf on its original coefficient-kernel cover of X.
The transition `j_(s,r) : A_s ⟶ A_r`, for r ≤ s, is the specified original
coefficient reduction followed by the inverse cover-comparison isomorphism.
All coefficient objects and reductions below are these original ones.

## Derived sections, cohomology and degree zero

Use the [scheme small-etale constructions](../../Geometry/EtaleDerivedSections.md)
with this X and R. Write Γ for `EtaleDerivedSections.sections X R`, RH for
`EtaleDerivedSections.homotopyFunctor X R`, and H_d for
`EtaleDerivedSections.cohomology X R d`. These use the genuine category
`Sheaf J (ModuleCat.{0} R)`. Its enough-injectives structure and the
injective-resolution construction come from the existing Library and
Mathlib; no cohomology object or resolution property is an extra input.

The two inverse diagrams are defined by functor composition:

```text
cmHarrisCoefficientDerivedSystem = T ⋙ RH,
cmHarrisCoefficientCohomologySystem d = T ⋙ H_d.
```

The first takes values in
`HomotopyCategory (ModuleCat.{0} R) (ComplexShape.up ℕ)`. The second takes
values in `ModuleCat.{0} R`. In particular its component at r is H_d(A_r),
and `cmHarrisCoefficientCohomologySystem_map` states definitionally that its
transition is H_d applied to the specified original reduction. The identity
and composition laws follow from the two functors being composed.

`cmHarrisCoefficientCohomologyZeroIso` is the natural isomorphism

```text
T ⋙ H_0 ≅ T ⋙ Γ.
```

It is left whiskering of `EtaleDerivedSections.cohomologyZeroIso X R` by T,
so it respects every original inverse-index transition. It uses the proved
degree-zero comparison for the left-exact global-section functor. It does
not assume that global sections preserve arbitrary short exact sequences.

For each index r, `cmHarrisCoefficientDerivedSystemObjIso` identifies the
derived component with the image, under the homotopy-category quotient, of
`EtaleDerivedSections.complex X R A_r`. This complex is Γ applied to the
chosen injective resolution of A_r. For every d,
`cmHarrisCoefficientCohomologySystemObjIso` identifies H_d(A_r) with its
homology in degree d. Both definitions reuse the existing resolution
comparison isomorphisms; they do not assert a new choice-free cochain-level
identification of the entire inverse diagram.

## Scalar powers and finite shifts

For an object B in a preadditive category, `powSMul m a B` means
`(m^a : ℕ) • 𝟙 B`. The local instance `cmCohomology_additive` reuses
`Langlands.AlgebraicGeometry.Modules.CechResolution.rightDerived_additive`
with F = Γ. Thus H_d preserves zero morphisms and these scalar
endomorphisms. This general additivity proof is imported, rather than
reimplemented or assumed for the CM specialization.

`cmHarrisCoefficientCohomologySystem_powSMul_eq_zero` proves

```text
powSMul m r (H_d(A_r)) = 0.
```

Its proof rewrites this endomorphism as H_d applied to
`powSMul m r A_r`, uses the original sheaf annihilation theorem
`cmHarrisCoefficientSystem_powSMul_eq_zero`, and maps the zero morphism to
zero. This argument requires additivity, without any exactness assertion
for higher cohomology.

The [original finite-shift constructions](HarrisTaylorCMCoefficientDivisibleCoherence.md)
supply T[k], with component A_(r+k), and natural transformations
`I_k : T ⟶ T[k]` and `P_k : T[k] ⟶ T`. Their components are respectively
the normalized original inclusion `i_(r,r+k)` and the original reduction
`j_(r+k,r)`. Define

```text
cmHarrisCoefficientCohomologyShiftedSystem d k = T[k] ⋙ H_d,
cmHarrisCoefficientCohomologyShiftInclusion d k = I_k ▷ H_d,
cmHarrisCoefficientCohomologyShiftReduction d k = P_k ▷ H_d.
```

Here right whiskering applies H_d to each component of a natural
transformation. Consequently the constructed maps have components
H_d(i_(r,r+k)) and H_d(j_(r+k,r)), and are natural for all original
reduction arrows. The name `ShiftInclusion` records the originating sheaf
map; this module does not assert that its cohomology image is monic.

Writing these cohomology maps as I_(d,k) and P_(d,k), the last two theorems
prove equalities in the respective functor categories:

```text
I_(d,k) ≫ P_(d,k) = powSMul m k (T ⋙ H_d),
P_(d,k) ≫ I_(d,k) = powSMul m k (T[k] ⋙ H_d).
```

The notation `≫` means composition in the order displayed. For each
identity, natural-transformation extensionality reduces the goal to one
index. Functoriality combines the two cohomology maps into the image of
the original composite. The corresponding original shift identity makes
that composite a scalar endomorphism, and `map_powSMul` transports it
through the additive H_d. These proofs use no extra compatibility
hypothesis and no assertion that H_d is exact.

The indices r, degrees d and shifts k range over all natural numbers,
including zero. The scalar m is any nonzero natural number, including one;
there is no additional primality or residual-group-order assumption.

## Original sources, internal provenance and retained scope

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), Section 2, printed p.304, one-based PDF p.6, gives divisible
systems and row (2.1) for analytic smooth-equivariant sheaves. Section 3,
printed pp.306–308, PDF pp.8–10, gives the algebraic representation, full
local coefficient algebra, stable lattice, inverse function-equivariance
(3.7), and finite normal congruence quotient. Section 4, printed p.309,
PDF p.11, supplies the scheme-etale coefficient/cohomology target of
Proposition 4.4. Registered source:
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), III.1, printed pp.90–91, one-based PDF pp.98–99, supplies the
original small-level moduli, right frame convention and finite-etale covers.
III.2, printed pp.94–96, PDF pp.102–104, supplies stable-lattice torsion
sheaves, inverse-equivariant functions and compatible coefficient/cover
maps. The cohomology displayed on p.96 uses X_U base-changed to F^ac and
a direct limit over levels. The X used in this module is the original
scheme over F, and neither that geometric base change nor that limit is
identified with this fixed-level construction. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The cited sources determine the geometric and coefficient setting. The
functor compositions, whiskered maps, annihilation and scalar-composite
identities here are internal deductions from the original coefficient
system, its proved finite-shift equations and the Library's ordinary
small-etale cohomology functors. They are not attributed as separate
quoted theorems of these passages. Harris's Lemma 2.8 on p.306 concerns a
specified inverse system of complexes with additional properties; this
module does not apply that lemma to arbitrary derived sections.

The named geometric premises remain assumptions. This unit does not prove
geometric existence, the canonical-model comparisons, higher-cohomology
exactness or monicity, lattice-choice independence, continuity of a Galois
action, rationalization, an adic or other infinite-limit comparison, or the
analytic smooth-equivariant spectral sequence. Those remain obligations
of the broader development. In particular this conditional cohomology
adapter does not complete the unitary Shimura construction task.

The Lean and paired English prose are by Worker 57 using published
interfaces. The environment is Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
