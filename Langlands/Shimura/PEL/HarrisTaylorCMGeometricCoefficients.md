# Geometric CM levels and original pulled-back coefficients

Author: Worker 57.

This module constructs the base change of the original represented CM scheme
tower from F to its algebraic closure, together with the natural projections
and the original integral coefficient system pulled back to these schemes.
Exact inverse image transports the whole original divisible system, including
its specified inclusions, reductions, short exact rows, torsion condition and
complementary-power exactness.

## Arithmetic and representability inputs

All arithmetic carriers have universe zero. The input
`D : CentralSimpleUnitaryData E F A n` retains a totally real number field E,
a totally complex CM number field F quadratic over E, and the compatible
E-, F- and rational algebra structures on A. The signature data retain an
imaginary quadratic number field L, its algebra map to F, an embedding
`τ₀ : L →+* ℂ`, and

```text
C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀).
```

The named premises are pullback-tensor comparison, composition, unit
coherence, associativity, left-unitor comparison and symmetry; Picard-zero
pullback, the Mumford-square assertion and universal base change; dual
abelian base-change naturality, polarization base change and relative finite
Weil transition; `h : Global.RationalProfiniteIntegerAdeleComparison`;
and `htor : TorsionFiniteEtaleStatement.{0}`. The exact representability
premise is

```text
q : CMRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor.
```

This proposition requires representing evidence at every
`U : SmallCMLevel D` for the original moduli presheaf on
`ComponentwiseAdmissibleCMBaseCategory`. Each witness includes an actual
admissible F-scheme, smoothness, an actual projective-space closed immersion
and a natural representation isomorphism. Its componentwise admissibility
retains the original connected-component, locally Noetherian and
geometric-point restrictions.
`chosenCMLevelRepresentation` chooses these witnesses from q.
The existing `representedCMOverTower` recovers the actual level maps by
fully faithful lifted Yoneda from the original moduli transitions, so their
identity and composition laws are already proved.
Write

```text
T_F = representedCMOverTower ... (chosenCMLevelRepresentation ... q),
X_U = (cmSchemeTower ... q).obj U,
Ω = AlgebraicClosure F.
```

The underlying schemes and maps of `T_F` are exactly `cmSchemeTower ... q`.
The named premises, including q, remain assumptions throughout this module.

## Actual geometric scheme tower

`cmGeometricFieldMap` is the actual morphism

```text
b : Spec Ω ⟶ Spec F
```

obtained by applying the contravariant spectrum functor to the algebra map
`F → Ω`. This declaration needs only F and its field structure.
`cmGeometricOverTower` is the functor

```text
T_Ω = T_F ⋙ Over.pullback b :
  SmallCMLevel D ⥤ Over (Spec Ω).
```

Its level at U is the scheme fiber product `X_U ×_(Spec F) Spec Ω`,
with structure morphism the second projection. Its maps are the genuine
base-changed original level maps. `cmGeometricSchemeTower` forgets the
over-category structure. Functor identities and composition follow from
the imported pullback functor.

`cmGeometricProjection` is the natural transformation from this geometric
scheme tower to `cmSchemeTower ... q`, whose component `π_U` is the first
fiber-product projection. For every original transporter arrow `k : U ⟶ V`,
its naturality says

```text
T_Ω.map k ≫ π_V = π_U ≫ T_F.map k
```

after forgetting to schemes. The proof reduces the left side to a pullback
lift followed by its first projection and then unfolds the underlying
original scheme tower.
`cmGeometricSchemeTower_isPullback` proves that the square with sides
`π_U`, the structure maps of the two levels, and b is a pullback.
It applies the universal property of the actual categorical pullback.
`cmGeometricOverTower_smooth` obtains smoothness of the second projection
by base change from the smoothness in the chosen original representation.
This module proves that smoothness assertion; it does not establish a
base-change theorem for the particular `IsHProjective` predicate.

## Original coefficients on the geometric level

The coefficient part additionally assumes finite rational dimension of A,
a number field K, a finite K-module W and

```text
ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W,
p : Global.FinitePlace ℚ,
m : ℕ, hm : m ≠ 0.
```

For the chosen small level U, it also retains

```text
existence : RelativeDualSchemeExistenceStatement.{0},
geometry : RelativeDualSchemeGeometryStatement.{0},
hRigid : CMGeometricCoarseRigidity D C preservation composition
           unitCoherence associativity comparison symmetry stability square
           universality compatibility h htor U.obj.
```

Let `R = HarrisCoefficientIntegers K p`, the full product of the coefficient
valuation rings above p. Write `J_Ω` for the small-etale topology of the
actual geometric scheme at U and

```text
S = cmHarrisCoefficientSystem ... q U ρ p m hm existence geometry hRigid,
B = cmHarrisCoefficientDivisibleSystem ...
      q U ρ p m hm existence geometry hRigid,
P_U = EtaleInverseImage.inverseImage π_U R.
```

S is the existing original inverse system of integral module sheaves on
`X_U.smallEtaleTopology`. It uses the full stable lattice for
`CompactOpenLevel.inverseOpposite U.obj`, the original quotients by the
powers of m, the inverse-unop residual action and the constructed
coefficient-kernel covers. Each reduction is the specified original
reduction with its existing cover comparison. B has exactly S as its tower
and the original cokernel-defined normalized inclusions.

P_U is the published inverse image along the actual scheme projection
π_U. Its construction uses the affine etale subsite, geometric base change,
left Kan extension, sheafification and the affine/small-etale sheaf
equivalence. The imported exactness result proves finite-limit
preservation for arbitrary scheme morphisms; its adjunction gives
finite-colimit preservation, and the imported additive structure supplies
additivity. These properties require no etaleness of π_U.

`cmHarrisGeometricCoefficientSystem` is exactly the composite

```text
S_Ω = S ⋙ P_U :
  ℕᵒᵖ ⥤ Sheaf J_Ω (ModuleCat.{0} R).
```

Thus at exponent r it is `P_U.obj (S.obj (op r))`.
`cmHarrisGeometricCoefficientSystem_map` is the definitional equality

```text
S_Ω.map f = P_U.map (S.map f)
```

for every inverse-index arrow f. It retains all original reductions.
`cmHarrisGeometricCoefficientDivisibleSystem` is `B.map P_U`, using the
existing generic `DivisibleSystem.map`.
Its tower and inclusion lemmas identify its tower with S_Ω and its
inclusion at r < s with `P_U.map (B.inclusion hrs)`, respectively.
Neither the sheaves nor their maps are new supplied output data.

## Exactness and scalar relations

The generic transport constructs every field of the geometric divisible
system. Additivity carries multiplication by a natural scalar power and
zero to the corresponding morphisms on the pulled-back object.
Functoriality preserves each zero composite.
Exactness transports the original short exact, torsion and
complementary-power rows. In particular, if

```text
A_r = S_Ω.obj (op r),
j_(s,r) = S_Ω.map (homOfLE hrs).op       for hrs : r ≤ s,
i_(r,s) = (B.map P_U).inclusion hrs     for hrs : r < s,
```

the constructed structure supplies the short exact row

```text
0 ⟶ A_r --i_(r,s)--> A_s --j_(s,s-r)--> A_(s-r) ⟶ 0,
```

and identifies the first map with the kernel of multiplication by `m^r`
on A_s. Its complementary-power exactness is

```text
A_(a+b) --(m^a)•id--> A_(a+b) --(m^b)•id--> A_(a+b)
```

for all nonnegative a and b.
`cmHarrisGeometricCoefficientSystem_powSMul_eq_zero` specializes the
constructed annihilation field to state `(m^r) • id_(A_r) = 0`.
All exponents include zero, and m = 1 is permitted. No primality or
invertibility of a residual group order is needed. The categorical
complementary-power condition does not assert module freeness over an
arbitrary coefficient ring.

## Original sources, provenance and remaining scope

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99,
specifies the original small-level moduli, right frame composition and
level maps. III.2, printed pp.94–96, PDF pp.102–104, constructs
stable-lattice torsion sheaves with inverse function-equivariance and
compatible coefficient/cover maps. Its cohomology on p.96 uses
`X_U ×_F F^ac` and a direct limit over levels. This module constructs that
scheme base change of the represented tower and the inverse images of its
original integral sheaves, conditional on the displayed premises. Registered
source: `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), Section 2, printed p.304, one-based PDF p.6, defines divisible
systems, their torsion condition and short exact row (2.1).
Section 3, printed pp.306–308, PDF pp.8–10, supplies the algebraic
representation, full local scalar algebra, stable lattice,
inverse function-equivariance (3.7) and normal congruence quotient
factorization. Registered source:
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

The fiber-product functor, projection naturality and exact transport of
the original coefficient system are internal deductions from the published
[scheme tower](HarrisTaylorCMSchemeLevels.md),
[original divisible system](HarrisTaylorCMCoefficientDivisible.md),
[inverse image](../../Geometry/EtaleInverseImage.md) and
[its exactness](../../Geometry/EtaleInverseImageExact.md).
They are not separately quoted results from the cited passages.
This construction retains the existing representation choices through q;
it does not prove the source representability or rigidity premises,
projectivity of the geometric levels, a comparison with a new torsor
presentation, algebraic-closure coefficient comparison formulas,
Galois actions, level limits, analytic uniformization or analytic cohomology.
Those remain separate constructions or proof obligations.
Generic inverse-image and divisible-system infrastructure is imported,
with no reused unreviewed draft.
The new Lean and English prose are by Worker 57 in Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
