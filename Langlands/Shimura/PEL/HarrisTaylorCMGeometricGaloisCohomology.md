# Galois actions on original geometric CM torsion cohomology

Author: Worker 57.

This module equips the original geometric CM coefficient inverse system with
Galois actions on derived global sections, ordinary cohomology and actual
global sections. Every reduction is an equivariant morphism. The underlying
objects, Galois operators and reductions are identified with the existing
geometric constructions. Canonical homology and degree-zero recovery are
isomorphisms of action-valued inverse systems.

## Arithmetic and geometric input

The arithmetic carriers have universe zero. The input
`D : CentralSimpleUnitaryData E F A n` retains a totally real number field E,
a totally complex CM number field F quadratic over E, and the compatible
E-, F- and rational algebra structures on A. An imaginary quadratic number
field L with an algebra map to F, an embedding `τ₀ : L →+* ℂ` and

```text
C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀)
```

give the original signature input.

The named premises remain pullback-tensor comparison, composition, unit
coherence, associativity, left-unitor comparison and symmetry; Picard-zero
pullback, the Mumford-square assertion and universal base change; dual
abelian base-change naturality, polarization base change and relative finite
Weil transition; `h : Global.RationalProfiniteIntegerAdeleComparison`; and
`htor : TorsionFiniteEtaleStatement.{0}`. The representability premise is
exactly

```text
q : CMRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor.
```

It concerns the actual admissible smooth projective F-schemes representing
the specified original moduli presheaves on componentwise admissible CM
bases. The geometric-point and admissibility restrictions of this
proposition remain in force. Fix `U : SmallCMLevel D`, and write

```text
X = (cmSchemeTower ... q).obj U,
X̄ = (cmGeometricSchemeTower ... q).obj U,
π = (cmGeometricProjection ... q).app U : X̄ ⟶ X,
G = AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
g_σ = (cmGeometricGaloisMap ... q σ).app U.
```

Thus X̄ is the existing fiber product
`X ×_(Spec F) Spec (AlgebraicClosure F)`. The raw map g_σ fixes π and
uses `Spec σ` on the second factor. With `(σ * τ)(x) = σ(τ(x))`,
the imported raw-map laws are

```text
g_1 = id_X̄,
g_σ ≫ g_τ = g_(σ * τ),
g_σ ≫ π = π.
```

The geometric left action defined using inverse comorphisms in
[HarrisTaylorCMGeometricGalois](HarrisTaylorCMGeometricGalois.md) uses
g_(σ⁻¹). The operators below use pullback along the displayed raw g_σ.

The coefficient input additionally retains `[Module.Finite ℚ A]`, a
number field K, a finite K-module W and

```text
ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W,
p : Global.FinitePlace ℚ,
m : ℕ, hm : m ≠ 0,
existence : RelativeDualSchemeExistenceStatement.{0},
geometry : RelativeDualSchemeGeometryStatement.{0},
hRigid : CMGeometricCoarseRigidity D C preservation composition
           unitCoherence associativity comparison symmetry stability square
           universality compatibility h htor U.obj.
```

Put `R = HarrisCoefficientIntegers K p`, the full product of coefficient
valuation rings above p, and abbreviate

```text
S̄ = cmHarrisGeometricCoefficientSystem ... q U ρ p m hm
       existence geometry hRigid,
Ψ_σ = cmHarrisGeometricCoefficientGaloisIso ... σ
    : S̄ ⋙ EtaleInverseImage.inverseImage g_σ R ≅ S̄.
```

S̄ is the original stable-lattice torsion coefficient system pulled back
along π. Its finite-stage sheaves retain the inverse-unop residual action,
the constructed coefficient-kernel covers, and the original reductions.
Every natural exponent, including zero, occurs. The only scalar
restriction is `m ≠ 0`; m need not be prime and may be 1. This formal
generality is inherited from the coefficient construction.

The two localization-size instances are

```text
[HasDerivedCategory.{wS} (ModuleSheaf X̄ R)]
[HasDerivedCategory.{wR} (ModuleCat.{0} R)].
```

The universes wS and wR are independent. The private local instance
`cmHarrisGeometricGaloisDerivedInstances` derives the indexed family
required by the generic action construction from the first instance:
every vertex scheme is definitionally X̄. No extra family of geometric
or localization premises is supplied. The inverse-image and
cohomological pullback constructions apply to arbitrary scheme
morphisms; no new étaleness assumption on π or g_σ is added.

## The three action-valued systems

Let `Dcoeff = cmHarrisGeometricGaloisCoefficientDiagram ...`. This is
the original coefficient diagram on `ℕᵒᵖ × SingleObj G`, with fixed
scheme X̄, coefficient at `(r,*)` equal to `S̄.obj r`, and transition

```text
Dcoeff.map (f,σ) = Ψ_σ.hom.app r ≫ S̄.map f
```

for `f : r ⟶ s` in `ℕᵒᵖ`. Its already proved identity and composition
fields are used unchanged.

The definitions specialize the generic geometric action constructions:

```text
cmHarrisGeometricGaloisDerivedAction = Dcoeff.derivedAction
  : ℕᵒᵖ ⥤ Action (DerivedCategory.Plus (ModuleCat R)) G,

cmHarrisGeometricGaloisCohomologyAction d = Dcoeff.cohomologyAction d
  : ℕᵒᵖ ⥤ Action (ModuleCat R) G,

cmHarrisGeometricGaloisSectionsAction = Dcoeff.sectionsAction
  : ℕᵒᵖ ⥤ Action (ModuleCat R) G.
```

Here `d : ℕ` is an ordinary cohomological degree. These are inverse
systems in the coefficient exponent at one fixed small CM level U.
Write them as A, B_d and C₀, respectively. At each `r : ℕᵒᵖ` their
underlying objects are exactly

```text
(A.obj r).V =
  (EtaleDerivedSectionsPlus.derivedSections X̄ R).obj (S̄.obj r),

(B_d.obj r).V =
  (EtaleDerivedSections.cohomology X̄ R d).obj (S̄.obj r),

(C₀.obj r).V =
  (EtaleDerivedSections.sections X̄ R).obj (S̄.obj r).
```

The three `*_obj_V` theorems prove these equalities by reflexivity.
Thus the underlying objects are the original bounded-below derived
global sections, right-derived ordinary global sections and actual
global sections.

The imported action construction curries the product-index cohomological
functor and uses Mathlib's equivalence with actions. In `SingleObj G`,
`σ ≫ τ = τ * σ`; accordingly each constructed action satisfies

```text
ρ_action (σ * τ) = ρ_action τ ≫ ρ_action σ.
```

This is the usual left-action law with categorical composition written
in execution order. The unit and multiplication laws follow from the
functor laws; no action-law hypotheses are added. Commuting arrows in
the product category give equivariance of every exponent reduction,
as recorded by its type as a morphism in `Action`.

## Actual Galois operators and original reductions

The three `*_obj_ρ` theorems identify the operators with

```text
(A.obj r).ρ σ =
  sheafDerivedPullbackWithCoefficients g_σ R (Ψ_σ.hom.app r),

(B_d.obj r).ρ σ =
  cohomologyPullbackWithCoefficients g_σ R d (Ψ_σ.hom.app r),

(C₀.obj r).ρ σ =
  sectionsPullbackWithCoefficients g_σ R (Ψ_σ.hom.app r).
```

The proofs specialize the corresponding generic operator formulas.
They substitute the actual scheme-map identification and the proved
pure-Galois coefficient-map formula. The maps use the original
finite-stage Ψ comparison, with its geometric inverse-image source.

For every `f : r ⟶ s` in `ℕᵒᵖ`, the three `*_map_hom` theorems prove

```text
(A.map f).hom =
  (EtaleDerivedSectionsPlus.derivedSections X̄ R).map (S̄.map f),

(B_d.map f).hom =
  (EtaleDerivedSections.cohomology X̄ R d).map (S̄.map f),

(C₀.map f).hom =
  (EtaleDerivedSections.sections X̄ R).map (S̄.map f).
```

Consequently the original cohomological reductions themselves are
Galois-equivariant.

For the derived formula, the proof expands the generic action map on
the pure-reduction arrow `(f,1)`. Its coefficient map is the actual
diagram inverse-image unit followed by `S̄.map f`. The coefficient
postcomposition formula and `diagramDerivedPullback_id` reduce this
to derived global sections of `S̄.map f`. The product identity and
opposite-map transports are normalized in this calculation.

For the ordinary formula, let

```text
H_d = DerivedCategory.Plus.homologyFunctor (ModuleCat R) d,
c_d = EtaleDerivedSectionsPlus.homologyNatIso X̄ R d.
```

By construction the underlying map is

```text
c_d.inv.app (S̄.obj r) ≫ H_d.map ((A.map f).hom) ≫
  c_d.hom.app (S̄.obj s).
```

The proof substitutes the derived reduction formula, uses naturality
of c_d at `S̄.map f`, and cancels its inverse and forward components.
The section proof follows the same calculation with
`EtaleDerivedSectionsPlus.homologyZeroIso X̄ R` and H₀.
These calculations retain the canonical comparisons rather than
assuming definitional equality of transported maps.

## Equivariant homology and degree-zero recovery

`cmHarrisGeometricGaloisDerivedHomologyIso d` constructs

```text
A ⋙ H_d.mapAction G ≅ B_d.
```

It is the specialization of `Dcoeff.derivedActionHomologyIso d`.
The theorem with suffix `_hom_app_hom` identifies its underlying
component at r with `c_d.hom.app (S̄.obj r)` by reflexivity.

`cmHarrisGeometricGaloisDerivedZeroIso` similarly constructs

```text
A ⋙ H₀.mapAction G ≅ C₀.
```

Its `_hom_app_hom` theorem identifies the underlying component with
`(EtaleDerivedSectionsPlus.homologyZeroIso X̄ R).hom.app (S̄.obj r)`.
The generic constructions prove Galois equivariance and naturality
along all exponent arrows from naturality of these canonical
comparisons.

Finally `cmHarrisGeometricGaloisCohomologyZeroIso` constructs

```text
B_0 ≅ C₀
```

by composing the inverse of the degree-zero homology comparison
with the comparison to actual sections. Its action-valued natural
isomorphism type gives both Galois equivariance and compatibility
with the original reductions.

## Source, derivation and remaining scope

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99,
specifies the original small levels, moduli F-schemes and level maps.
III.2, printed pp.94–96, PDF pp.102–104, constructs stable-lattice
torsion sheaves using inverse function-equivariance and compatible
coefficient and cover maps, and defines geometric cohomology on
`X_U ×_F F^ac`. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The source's F is this module's F, its imaginary quadratic E is
this module's L, and its totally real F⁺ is this module's E.

The action-valued packaging, exact original-map identifications and
transport calculations are internal deductions. They are not
displayed formulas attributed to those source pages. The module
specializes the existing
[geometric action-diagram construction](../../Geometry/EtaleGeometricActionDiagram.md)
to the
[original CM Galois coefficient diagram](HarrisTaylorCMGeometricGaloisDiagram.md).
The actual pullback operators and the canonical homology comparisons
come from that generic construction; the new reduction proofs
identify their transported maps with the original CM reductions.
No generic infrastructure is reimplemented.

This module constructs algebraic Galois actions at every original
finite coefficient stage and their equivariant reduction systems.
It does not prove continuity for the profinite Galois topology,
construct level or adic limits, or construct Hecke coefficient maps.
Representability, dual existence and geometry, coarse rigidity and
every other named premise above remain assumptions. Those proofs
and the other obligations of the host geometric task remain open.
The new Lean and English prose are by Worker 57, using Lean 4.34.0
and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
