# Galois-equivariant normalized finite shifts of CM coefficients

Author: Worker 57.

This module constructs the original normalized finite-shift inclusions and
reductions as morphisms of Galois-action inverse systems. It treats bounded-below
derived global sections, ordinary cohomology in every natural degree, and actual
global sections. It identifies their underlying maps with the cohomological
images of the original geometric coefficient maps and proves both scalar
composites in each case.

## Arithmetic, geometry and coefficients

The arithmetic input is the same as in the
[original geometric Galois cohomology construction](HarrisTaylorCMGeometricGaloisCohomology.md).
All arithmetic carriers have universe zero. It consists of
`D : CentralSimpleUnitaryData E F A n`, where E is a totally real number
field, F is a totally complex CM number field quadratic over E, and A has
the compatible E-, F- and rational algebra structures. The signature charts
are

```text
C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀),
```

with L an imaginary quadratic number field, an L-algebra structure on F,
and `τ₀ : L →+* ℂ`. The named premises remain pullback-tensor comparison,
composition, unit coherence, associativity, left-unitor comparison and
symmetry; Picard-zero pullback, the Mumford-square assertion and universal
base change; dual abelian base-change naturality, polarization base change
and relative finite Weil transition; the rational profinite-integer/adele
comparison h; and `htor : TorsionFiniteEtaleStatement.{0}`.

The geometric premises are exactly

```text
q : CMRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor,
existence : RelativeDualSchemeExistenceStatement.{0},
geometry : RelativeDualSchemeGeometryStatement.{0},
hRigid : CMGeometricCoarseRigidity D C preservation composition
      unitCoherence associativity comparison symmetry stability square
      universality compatibility h htor U.obj,
```

where `U : SmallCMLevel D`. The representability assertion concerns the
specified original moduli presheaf on componentwise admissible CM bases,
with its connected-component, locally Noetherian and geometric-point
restrictions. It is retained as an assertion, rather than proved here.
The geometric scheme is the existing fiber product

```text
Xbar = (cmGeometricSchemeTower ... q).obj U
     = X_U ×_(Spec F) Spec (AlgebraicClosure F).
```

The coefficients retain `[Module.Finite ℚ A]`, a number field K, a finite
K-module W, an algebraic representation
`ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W`, a
rational finite place p, and `m : ℕ` with `hm : m ≠ 0`. Put

```text
R = HarrisCoefficientIntegers K p,
S = cmHarrisGeometricCoefficientSystem ... q U ρ p m hm
      existence geometry hRigid,
G = AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F.
```

R is the full product of coefficient valuation rings above p. S is the
original stable-lattice torsion coefficient system pulled back to Xbar.
Its original coefficient-kernel covers, inverse-unop residual action and
specified reductions are unchanged. Every natural exponent, degree and
shift, including zero, is allowed. The scalar need not be prime and may
be one; no residual-group-order invertibility assumption is added.

Write

```text
RD = EtaleDerivedSectionsPlus.derivedSections Xbar R,
H_d = EtaleDerivedSections.cohomology Xbar R d,
Γ = EtaleDerivedSections.sections Xbar R.
```

The derived and homology-transport constructions use

```text
[HasDerivedCategory.{wS} (ModuleSheaf Xbar R)]
[HasDerivedCategory.{wR} (ModuleCat.{0} R)].
```

The universes wS and wR are independent. These are the same localization
premises as in the original Galois cohomology module; no new geometric or
exactness premise is introduced.

## Coefficient comparison and the shifted action systems

For `k : ℕ`, use the already constructed natural maps

```text
I_k = cmHarrisGeometricCoefficientShiftInclusion ... k : S ⟶ S[k],
P_k = cmHarrisGeometricCoefficientShiftReduction ... k : S[k] ⟶ S.
```

At `r : ℕᵒᵖ`, `S[k].obj r = S.obj (op (r.unop + k))`. The inclusion
is the original normalized inclusion, including the identity normalization
for shift zero. The reduction is the original arrow from exponent
`r.unop + k` to `r.unop`.

Let `g_σ = (cmGeometricGaloisMap ... q σ).app U` and
`Ψ_σ = cmHarrisGeometricCoefficientGaloisIso ... σ`. The raw map g_σ uses
`Spec σ` on the algebraic-closure factor and fixes the original-level
projection. The theorem
`cmHarrisGeometricCoefficientGaloisIso_shiftInclusion` proves

```text
(inverseImage g_σ R).map (I_k.app r) ≫
    Ψ_σ.hom.app (op (r.unop + k)) =
  Ψ_σ.hom.app r ≫ I_k.app r.
```

Its proof specializes naturality of the original canonical geometric
inverse-image comparison to the original normalized inclusion before
geometric pullback. Thus the comparison is compatible with the actual
coefficient map, with no additional equivariance hypothesis.

Write A, B_d and C₀ for the published systems
`cmHarrisGeometricGaloisDerivedAction`,
`cmHarrisGeometricGaloisCohomologyAction d`, and
`cmHarrisGeometricGaloisSectionsAction`. They take values in
`Action (DerivedCategory.Plus (ModuleCat R)) G` or
`Action (ModuleCat R) G`, respectively. Their underlying objects at r are
`RD.obj (S.obj r)`, `H_d.obj (S.obj r)` and `Γ.obj (S.obj r)`.
Their Galois operators are the original pullback-with-coefficients maps
along g_σ using `Ψ_σ.hom.app r`.

The private index functor `cmGaloisShiftIndex k` is the opposite of the
monotone map `r ↦ r + k`. Composition with it defines the three public
systems

```text
cmHarrisGeometricGaloisDerivedShiftedAction k = A[k],
cmHarrisGeometricGaloisCohomologyShiftedAction d k = B_d[k],
cmHarrisGeometricGaloisSectionsShiftedAction k = C₀[k].
```

Each is the original action system evaluated at the shifted exponent,
including its original shifted reduction maps. The public inclusion and
reduction interfaces below use these named shifted systems.

## Equivariant inclusions, reductions and their exact underlying maps

The six constructions are natural transformations in the corresponding
action-valued functor categories:

```text
cmHarrisGeometricGaloisDerivedShiftInclusion k : A ⟶ A[k],
cmHarrisGeometricGaloisDerivedShiftReduction k : A[k] ⟶ A,
cmHarrisGeometricGaloisCohomologyShiftInclusion d k : B_d ⟶ B_d[k],
cmHarrisGeometricGaloisCohomologyShiftReduction d k : B_d[k] ⟶ B_d,
cmHarrisGeometricGaloisSectionsShiftInclusion k : C₀ ⟶ C₀[k],
cmHarrisGeometricGaloisSectionsShiftReduction k : C₀[k] ⟶ C₀.
```

Consequently every component is Galois-equivariant and every map is
compatible with all original exponent reductions. For the derived
inclusion, its component is `RD.map (I_k.app r)`. The private commutation
lemma uses the published formulas for the original Galois operators,
precomposition and postcomposition of derived pullback with coefficients,
and the coefficient-comparison equation above. Its private naturality
lemma applies RD to naturality of I_k. A named private component combines
these proofs into an action morphism, which forms the natural
transformation.

Each reverse map is the original action functor applied to
`(homOfLE (Nat.le_add_right r.unop k)).op` at r. Its naturality follows
from functoriality and uniqueness of arrows in the exponent category.
The published original reduction-identification theorems therefore give
its exact underlying map.

The ordinary inclusion is the derived inclusion transported through
`cmHarrisGeometricGaloisDerivedHomologyIso d`. The section inclusion uses
`cmHarrisGeometricGaloisDerivedZeroIso`. Both comparisons are already
Galois-equivariant and natural in the exponent, so their conjugated maps
are morphisms of the original action systems.

For each of the three prefixes `Derived`, `Cohomology` and `Sections`,
the theorems with suffixes `ShiftInclusion_app_hom` and
`ShiftReduction_app_hom` identify the underlying components with

```text
RD.map (I_k.app r),   RD.map (P_k.app r),
H_d.map (I_k.app r),  H_d.map (P_k.app r),
Γ.map (I_k.app r),    Γ.map (P_k.app r),
```

respectively. For the transported inclusions these equalities use
naturality of the canonical homology comparison at `I_k.app r`, followed
by cancellation of its inverse and forward components. The small private
lemma `cmGaloisNatIso_conjugate` implements precisely this categorical
calculation. Thus the maps are identified with cohomology or actual
sections of the original inclusions, rather than only specified up to
an unspecified isomorphism.

## Both scalar composites

For any object X in the relevant preadditive category,
`powSMul m k X = (m^k : ℕ) • 𝟙 X`. This notation also applies to the
action-valued inverse systems. The six theorems with suffixes
`ShiftInclusion_reduction` and `ShiftReduction_inclusion` prove

```text
I_D,k ≫ P_D,k = powSMul m k A,
P_D,k ≫ I_D,k = powSMul m k A[k],
I_H,d,k ≫ P_H,d,k = powSMul m k B_d,
P_H,d,k ≫ I_H,d,k = powSMul m k B_d[k],
I_Γ,k ≫ P_Γ,k = powSMul m k C₀,
P_Γ,k ≫ I_Γ,k = powSMul m k C₀[k].
```

Here the I and P symbols denote the corresponding newly constructed
equivariant maps. These are equalities of natural transformations in the
action categories, with categorical composition written in execution
order.

Each proof reduces first to an exponent and then to the underlying
morphism using natural-transformation extensionality and `Action.Hom.ext`.
The underlying-map identifications turn the composite into the image of
`I_k.app r ≫ P_k.app r`, or of the reverse composite. The published
geometric coefficient scalar identity evaluates it, and `map_powSMul`
transports the result through the additive functor. Additivity of RD is
inherited from the actual derived-complex construction; additivity of
H_d is the published right-derived additivity instance; Γ has its
existing additive structure. No exactness or monicity of higher
cohomology is used or concluded.

## Source, internal derivation and retained obligations

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99,
specifies the original small levels, moduli F-schemes and level maps.
III.2, printed pp.94–96, PDF pp.102–104, constructs stable-lattice
torsion sheaves with inverse function-equivariance, compatible coefficient
and cover maps, and geometric cohomology over F's algebraic closure.
Registered source: `harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA-256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The source's imaginary quadratic E is this module's L, and its totally
real F⁺ is this module's E.

The finite-shift equivariance, action-valued natural transformations,
underlying-map identifications and scalar calculations are internal
deductions from the published
[geometric finite shifts](HarrisTaylorCMGeometricCohomology.md),
[Galois coefficient comparisons](HarrisTaylorCMGeometricGaloisCoefficients.md)
and [original Galois cohomology actions](HarrisTaylorCMGeometricGaloisCohomology.md).
They are not separate displayed assertions attributed to those source
pages. No generic sheaf or cohomology infrastructure is reimplemented.

Representability, dual existence and geometry, coarse rigidity and all
other named premises above remain assumptions. This module constructs
finite-stage algebraic Galois equivariance and its scalar relations.
Continuity for the profinite Galois topology, level or adic limits,
rationalization, Hecke coefficient maps and the remaining geometric
existence and canonical-model proofs remain separate obligations. The
host actual unitary Shimura construction task remains incomplete.

The new Lean and paired English prose are by Worker 57 using Lean 4.34.0
and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
