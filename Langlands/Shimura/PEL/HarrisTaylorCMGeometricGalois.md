# Algebraic-closure automorphisms of the geometric CM scheme tower

Author: Worker 57.

This module constructs an action of the F-algebra automorphisms of
`AlgebraicClosure F` on the existing geometric CM scheme tower. The maps
are actual fiber-product morphisms. Their naturality, original projection
invariance, semilinear structure formula, identity, composition and
inverse laws are proved. The construction retains the exact original
representability premise.

## Arithmetic and represented-tower inputs

All arithmetic carriers have universe zero. The arithmetic input is
`D : CentralSimpleUnitaryData E F A n`, with E a totally real number
field, F a totally complex CM number field quadratic over E, and A
carrying the compatible E-, F- and rational algebra structures used by D.
The signature input uses an imaginary quadratic number field L, an
algebra map from L to F, an embedding `τ₀ : L →+* ℂ` and

```text
C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀).
```

The named premises are pullback-tensor comparison, composition, unit
coherence, associativity, left-unitor comparison and symmetry; Picard-zero
pullback, the Mumford-square assertion and universal base change; dual
abelian base-change naturality, polarization base change and relative
finite Weil transition; `h : Global.RationalProfiniteIntegerAdeleComparison`;
and `htor : TorsionFiniteEtaleStatement.{0}`. They remain explicit
arguments. The representability premise is exactly

```text
q : CMRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor.
```

This is the existing proposition requiring actual representing admissible
smooth projective F-schemes for the original componentwise moduli
presheaves at every `U : SmallCMLevel D`.
`chosenCMLevelRepresentation ... q` chooses its witnesses. The existing
`representedCMOverTower` constructs the level morphisms from the original
moduli transitions by fully faithful lifted Yoneda. Write

```text
T_F = representedCMOverTower ... (chosenCMLevelRepresentation ... q),
Ω = AlgebraicClosure F,
b = cmGeometricFieldMap : Spec Ω ⟶ Spec F,
T_Ω = cmGeometricOverTower ... q = T_F ⋙ Over.pullback b,
X̄ = cmGeometricSchemeTower ... q.
```

Here X̄ forgets the over-category structure of T_Ω. Its level at U is the
actual fiber product of `(T_F.obj U).hom` with b. Denote its first
projection by `π_U = (cmGeometricProjection ... q).app U` and its second
projection by `s_U = (T_Ω.obj U).hom`. These are precisely the existing
chosen geometric levels and their existing projections. No coefficient
representation, coefficient ring, relative-dual existence or geometry
premise, or coarse rigidity premise is added by this module.

## Spectrum maps and the raw geometric action

For any field F of universe zero, independently of the CM hypotheses,
`cmGeometricGaloisBaseMap σ` is

```text
a_σ = Spec.map σ.toRingHom : Spec Ω ⟶ Spec Ω
```

for `σ : Ω ≃ₐ[F] Ω`. The theorem
`cmGeometricGaloisBaseMap_over` proves `a_σ ≫ b = b` from the fact that
σ fixes the algebra map from F. The identity and multiplication theorems
prove

```text
a_1 = id,
a_(σ * τ) = a_σ ≫ a_τ.
```

The multiplication on field automorphisms is function composition:
`(σ * τ)(x) = σ(τ(x))`. The displayed spectrum composition therefore has
the contravariant order. The proofs use spectrum functoriality; the
over-field equality reduces to `σ.toAlgHom.comp_algebraMap`.

Under the represented-tower hypotheses,
`cmGeometricGaloisMap σ : X̄ ⟶ X̄` has component

```text
m_σ,U = pullback.lift π_U (s_U ≫ a_σ) ...
```

The compatibility needed for this lift follows from `a_σ ≫ b = b` and
the original pullback square. Its naturality for every
`k : U ⟶ V` in the original small-level category is proved by comparing
both fiber-product projections and using the existing base-changed level
map formulas. Thus the whole original level-index functor is retained.

`cmGeometricGaloisMap_app_projection` and
`cmGeometricGaloisMap_app_structure` are the actual morphism equations

```text
m_σ,U ≫ π_U = π_U,
m_σ,U ≫ s_U = s_U ≫ a_σ.
```

They are the two projection equations for the pullback lift. The second
is the precise semilinear formula. The maps are morphisms of the
underlying schemes; the formula specifies their action on the
algebraic-closure factor.

`cmGeometricGaloisMap_one` and `cmGeometricGaloisMap_mul` prove equalities
of natural transformations:

```text
m_1 = id_X̄,
m_(σ * τ) = m_σ ≫ m_τ.
```

Both proofs compare components and then both pullback projections. The
second proof also uses the proved spectrum multiplication law.
`cmGeometricGaloisIso σ : X̄ ≅ X̄` has hom m_σ and inverse m_(σ⁻¹).
The two inverse equations follow from these multiplication and identity
laws and the field-automorphism group laws.

## Bundled left action and evaluation at a level

`cmGeometricGaloisAction` is the monoid homomorphism

```text
α : (Ω ≃ₐ[F] Ω) →* Aut X̄,
α(σ) = cmGeometricGaloisIso (σ⁻¹).
```

For categorical automorphisms, Mathlib's multiplication has
`(f * g).hom = g.hom ≫ f.hom`. Inverse comorphisms therefore give the
left-action normalization

```text
α(σ).hom = m_(σ⁻¹),
α(σ * τ).hom = α(τ).hom ≫ α(σ).hom.
```

The first equality is the definitional theorem
`cmGeometricGaloisAction_hom`. To prove multiplicativity, the Lean
implementation uses isomorphism extensionality, reverses the factors in
`(σ * τ)⁻¹`, and applies the raw multiplication law. The unit law follows
from the raw identity law by the same isomorphism extensionality.
Every group-law field of this homomorphism is supplied by these proofs.

`cmGeometricGaloisLevelAction U` applies the evaluation functor's
`Functor.mapAut` to α. It is a monoid homomorphism into
`Aut (X̄.obj U)`, with hom component `m_(σ⁻¹),U`. Its unit and
multiplication laws are inherited from this actual evaluation functor
and the constructed tower action.

`cmGeometricGaloisAction_naturality` states, for every original level
arrow k,

```text
X̄.map k ≫ α(σ).hom.app V =
  α(σ).hom.app U ≫ X̄.map k.
```

It is the naturality equation of the constructed natural automorphism.
Combining the inverse-comorphism formula with the two raw projection
equations also gives projection invariance and the field-factor map
`a_(σ⁻¹)` for the left action.

## Original source, derivation and remaining scope

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99,
specifies the original small-level moduli, their represented F-schemes
and the right level maps. III.2, printed p.96, PDF p.104, forms
cohomology on `X_U ×_F F^ac`; printed p.97, PDF p.105, states the
eventual continuous action involving `Gal(F^ac/F)`.
The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The source's F is this module's F; its imaginary quadratic field E is
this module's L, and its totally real field F⁺ is this module's E.

The source motivates the arithmetic geometry and eventual Galois
action. The definitions and all identities in this module are internal
deductions from the actual
[geometric fiber-product tower](HarrisTaylorCMGeometricCoefficients.md),
the spectrum functor, the pullback universal property, and categorical
automorphism evaluation. The particular inverse-comorphism normalization
is specified explicitly here; it is not asserted to be an additional
formula printed in the cited passage.

The module constructs the scheme action conditional on q and the named
premises. It does not prove representability, coarse rigidity, coefficient
descent, coefficient equivariance, a cohomological action or its
continuity, commutation with Hecke actions on cohomology, level or adic
limits, or analytic comparisons. The full unitary-geometry task retains
those applicable construction and proof obligations.
Only published imported constructions are used; no unreviewed draft is
reused. The new Lean and English prose are by Worker 57 in Lean 4.34.0
and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
