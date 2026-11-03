# Finite shifts and ordinary cohomology of the geometric CM coefficient tower

Author: Worker 57.

This internal construction uses the actual original CM coefficient system pulled
back to the scheme fiber product over the algebraic closure of F. It transports
the original normalized finite-shift inclusions and reductions to this geometric
system, proves their scalar-composite identities and sheaf monicity, and constructs
ordinary small-etale derived sections and cohomology of the resulting sheaves.
Cohomology retains finite-stage annihilation and the two scalar identities in
every nonnegative degree.

## Arithmetic, geometric and coefficient inputs

All arithmetic carriers have universe zero. The input
`D : CentralSimpleUnitaryData E F A n` retains a totally real number field E,
a totally complex CM number field F quadratic over E, compatible E-, F- and
rational algebra structures on A, and finite rational dimension of A. The
signature input retains an imaginary quadratic number field L, an L-algebra
structure on F, an embedding `τ₀ : L →+* ℂ` and

```text
C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀).
```

The named premises are the pullback-tensor comparison, composition, unit
coherence, associativity, left-unitor comparison and symmetry assertions;
Picard-zero pullback, the Mumford-square assertion, universal base change,
duality naturality, polarization base change and relative finite Weil
transition assertions; `h : Global.RationalProfiniteIntegerAdeleComparison`;
and `htor : TorsionFiniteEtaleStatement.{0}`. With `U : SmallCMLevel D`,
the geometric premises are exactly

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

Representability is the assertion for the original moduli presheaf on
`ComponentwiseAdmissibleCMBaseCategory`, retaining its connected-component,
locally Noetherian and geometric-point restrictions. None of these named
premises is proved here. The original scheme level and all its maps are the
ones chosen and constructed from this precise representation assertion.

The coefficient inputs are a number field K, a finite K-module W, an
algebraic representation `ρ` of `D.rationalInvolution.baseChange K` on W,
a rational finite place p, and a natural scalar m with `hm : m ≠ 0`.
Set

```text
R = HarrisCoefficientIntegers K p,
X_U = (cmSchemeTower ... q).obj U,
Ω = AlgebraicClosure F,
Xbar = (cmGeometricSchemeTower ... q).obj U,
π = (cmGeometricProjection ... q).app U,
P = EtaleInverseImage.inverseImage π R,
T = cmHarrisCoefficientSystem ... q U ρ p m hm
      existence geometry hRigid,
G = cmHarrisGeometricCoefficientSystem ... q U ρ p m hm
      existence geometry hRigid = T ⋙ P,
B_r = G.obj (op r).
```

The [geometric prerequisite](HarrisTaylorCMGeometricCoefficients.md)
constructs Xbar as `X_U ×_(Spec F) Spec Ω` and π as its first projection.
It constructs P by the existing arbitrary-morphism small-etale inverse
image, whose additivity and exactness are proved. No etaleness of π is
assumed. G is exactly the original system followed by P; its transitions
are P applied to the specified original reductions.

R is the full product of the coefficient valuation rings above p. The
[original system](HarrisTaylorCMCoefficientSystem.md) retains the stable
lattice for `CompactOpenLevel.inverseOpposite U.obj`, its quotients by the
powers of m, the inverse-unop residual action and the original
coefficient-kernel covers. Their reductions include the original inverse
cover-comparison maps. These objects are carried through P without a new
choice of coefficient lattice or torsor presentation.

## Geometric finite shifts and sheaf monicity

The [original finite-shift construction](HarrisTaylorCMCoefficientDivisibleCoherence.md)
supplies the inverse diagram T[k] with component `T.obj (op (r+k))` and
natural transformations

```text
I_k : T ⟶ T[k],
P_k : T[k] ⟶ T.
```

Their components are the original normalized inclusion `i_(r,r+k)` and
the specified original reduction `j_(r+k,r)`. The normalization also covers
k = 0 by using the identity inclusion. Define

```text
cmHarrisGeometricCoefficientShiftedSystem k = T[k] ⋙ P,
cmHarrisGeometricCoefficientShiftInclusion k = I_k ▷ P,
cmHarrisGeometricCoefficientShiftReduction k = P_k ▷ P.
```

Right whiskering, denoted `▷`, applies P to each natural-transformation
component. Write G[k], Ibar_k and Pbar_k for these three constructions.
`cmHarrisGeometricCoefficientShiftedSystem_obj` identifies the component
at any opposite index r definitionally with `G.obj (op (r.unop+k))`.
The two `_app` lemmas state definitionally that the components of Ibar_k
and Pbar_k are P applied to the original inclusion and reduction. Their
naturality follows from right whiskering the original natural maps.

`cmHarrisGeometricCoefficientShiftInclusion_app_mono` proves that every
component of Ibar_k is monic. The proof unfolds it to P applied to the
original `cmHarrisCoefficientInclusionLE`, which is monic for every weak
inequality; finite-limit preservation by P preserves that monomorphism.
`cmHarrisGeometricCoefficientShiftInclusion_mono` then proves monicity of
the whole natural transformation using componentwise monicity.

For an object A in any preadditive category, `powSMul m a A` means
`(m^a : ℕ) • 𝟙 A`. The two geometric sheaf identities are

```text
Ibar_k ≫ Pbar_k = powSMul m k G,
Pbar_k ≫ Ibar_k = powSMul m k G[k].
```

These are respectively
`cmHarrisGeometricCoefficientShiftInclusion_reduction` and
`cmHarrisGeometricCoefficientShiftReduction_inclusion`. For each proof,
natural-transformation extensionality reduces to a component. Functoriality
of P combines the two images, the corresponding original finite-shift
identity identifies their composite, and `map_powSMul` transports the
scalar endomorphism through the additive P. Thus every map is the inverse
image of its original normalized map and each scalar identity is derived.

## Ordinary derived sections and cohomology

Use the [small-etale construction](../../Geometry/EtaleDerivedSections.md)
on Xbar with coefficients R. Put

```text
Jbar = Scheme.smallEtaleTopology Xbar,
Γ = EtaleDerivedSections.sections Xbar R,
RH = EtaleDerivedSections.homotopyFunctor Xbar R,
H_d = EtaleDerivedSections.cohomology Xbar R d.
```

These are the actual global-section functor and its right-derived functors
on `Sheaf Jbar (ModuleCat.{0} R)`. Enough injectives and the injective
resolutions come from the existing construction and Mathlib. No derived
object, cohomology module or desired comparison is supplied as an input.
The new diagrams are composition:

```text
cmHarrisGeometricCoefficientDerivedSystem = G ⋙ RH,
cmHarrisGeometricCoefficientCohomologySystem d = G ⋙ H_d.
```

The first takes values in
`HomotopyCategory (ModuleCat.{0} R) (ComplexShape.up ℕ)`; the second takes
values in `ModuleCat.{0} R`. The cohomology component at exponent r is
H_d(B_r). Its `_map` theorem states definitionally that every reduction
arrow is the image under H_d of the corresponding actual geometric sheaf
reduction. The identity and composition laws follow from functor
composition.

`cmHarrisGeometricCoefficientCohomologyZeroIso` constructs the natural
isomorphism

```text
G ⋙ H_0 ≅ G ⋙ Γ
```

by left whiskering the existing natural degree-zero comparison by G.
Consequently it respects every coefficient reduction. It uses the
left-exactness of sections and does not assume that sections are exact.
For an individual index r,
`cmHarrisGeometricCoefficientDerivedSystemObjIso` identifies the derived
component with the homotopy-category image of
`EtaleDerivedSections.complex Xbar R (G.obj r)`, which is Γ applied to the
chosen injective resolution. For every d,
`cmHarrisGeometricCoefficientCohomologySystemObjIso` identifies H_d(G.obj r)
with degree-d homology of that complex. These reuse the published
resolution comparisons for individual objects; no strict functoriality
of chosen cochain resolutions is asserted.

## Cohomological scalar relations and finite shifts

The local instance `cmGeometricCohomology_additive` applies the published
general instance
`Langlands.AlgebraicGeometry.Modules.CechResolution.rightDerived_additive`
to Γ. It proves additivity of H_d without an acyclicity, affineness or
higher-exactness premise. The theorem
`cmHarrisGeometricCoefficientCohomologySystem_powSMul_eq_zero` gives

```text
powSMul m r (H_d(B_r)) = 0.
```

The proof rewrites this endomorphism as H_d applied to `powSMul m r B_r`,
uses the annihilation of the actual geometric coefficient sheaf proved
in the geometric prerequisite, and maps zero to zero by additivity.

The cohomological finite shifts and maps are

```text
cmHarrisGeometricCoefficientCohomologyShiftedSystem d k = G[k] ⋙ H_d,
cmHarrisGeometricCoefficientCohomologyShiftInclusion d k = Ibar_k ▷ H_d,
cmHarrisGeometricCoefficientCohomologyShiftReduction d k = Pbar_k ▷ H_d.
```

They are natural in every original coefficient-reduction arrow after its
geometric pullback. Their components are exactly H_d applied to the
geometric normalized inclusion and reduction. The two final theorems
prove, with the displayed composition order,

```text
(Ibar_k ▷ H_d) ≫ (Pbar_k ▷ H_d) = powSMul m k (G ⋙ H_d),
(Pbar_k ▷ H_d) ≫ (Ibar_k ▷ H_d) = powSMul m k (G[k] ⋙ H_d).
```

As in the sheaf proofs, extensionality reduces to one exponent,
functoriality combines the images, the geometric sheaf identity evaluates
the composite, and additivity transports the scalar endomorphism.
The sheaf monicity above is not asserted for these higher-cohomology
maps. No exactness of H_d is used. All indices r, degrees d and shifts k
range over every natural number, including zero. Every nonzero natural
m is allowed, including one; primality and residual-group-order
invertibility are not additional hypotheses.

## Original sources, internal provenance and remaining scope

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), III.1, printed pp.90–91, one-based PDF pp.98–99, specifies the
original small-level moduli, right frame composition and finite-etale
level maps. III.2, printed pp.94–96, PDF pp.102–104, constructs the
stable-lattice torsion sheaves using inverse function-equivariance and
compatible coefficient/cover maps. Its geometric cohomology on p.96 uses
`X_U ×_F F^ac` and then a direct limit over levels. Here Xbar is precisely
the scheme fiber product over that algebraic closure, and the new
construction gives ordinary fixed-level cohomology of the inverse images
of the original integral torsion sheaves. The level direct limit and its
rational coefficient comparison remain separate. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), Section 2, printed p.304, one-based PDF p.6, defines divisible
systems and short exact row (2.1) in the analytic smooth-equivariant
setting. Section 3, printed pp.306–308, PDF pp.8–10, supplies the algebraic
representation, full local coefficient algebra, stable lattice,
inverse function-equivariance (3.7) and normal congruence quotient.
Section 4, printed p.309, PDF p.11, provides the scheme-etale coefficient
and cohomology target of Proposition 4.4. Registered source:
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

These sources specify the original geometry and coefficient conventions.
The right-whiskered geometric finite-shift maps, monicity, scalar
identities, functor compositions, annihilation and degree-zero and
resolution comparisons are internal deductions from the existing actual
geometric inverse image, original coefficient maps and ordinary
small-etale functors. No extra theorem is attributed to the cited source
passages. Harris's Lemma 2.8 on printed p.306 concerns a specified inverse
system of complexes with additional properties and is not applied here.

The explicit representability, dual geometry and coarse-rigidity premises
remain assumptions. This unit does not prove those existence or rigidity
assertions, a comparison with a new torsor presentation, projectivity of
geometric levels, lattice independence, Galois or Hecke actions on these
cohomology diagrams, level limits, adic limits, rationalization, higher
cohomology exactness or monicity, analytic uniformization or the analytic
smooth-equivariant spectral sequence. The broader actual unitary Shimura
construction task remains open.

The Lean and paired English prose are by Worker 57 using existing
interfaces. The environment is Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
