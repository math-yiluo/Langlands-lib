# Original geometric CM coefficients as a Galois diagram

Author: Worker 57.

This module constructs a contravariant scheme diagram at a fixed original
CM level and an actual `EtaleGeometricDiagram.CoefficientDiagram` over it.
The indices combine all coefficient exponents with the algebraic-closure
Galois group. Each coefficient map is the previously constructed Galois
comparison followed by the original reduction. The identity and composition
fields are proved, with the geometric inverse-image comparisons retained.

## Input and original objects

The arithmetic carriers have universe zero. The data
`D : CentralSimpleUnitaryData E F A n` retain a totally real number field E,
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

This is the published proposition about actual admissible smooth projective
F-schemes representing the specified original moduli presheaves on
componentwise admissible CM bases. Its geometric-point and admissibility
restrictions are retained. Fix `U : SmallCMLevel D` and write

```text
X = (cmSchemeTower ... q).obj U,
X̄ = (cmGeometricSchemeTower ... q).obj U,
π = (cmGeometricProjection ... q).app U : X̄ ⟶ X,
G = AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
g_σ = (cmGeometricGaloisMap ... q σ).app U.
```

Thus X̄ is the existing actual fiber product
`X ×_(Spec F) Spec (AlgebraicClosure F)`. The map g_σ fixes π and uses
`Spec σ` on the second factor. The published laws are

```text
g_1 = id_X̄,
g_σ ≫ g_τ = g_(σ * τ),
g_σ ≫ π = π.
```

These are the raw spectrum-comorphism maps, with
`(σ * τ)(x) = σ(τ(x))`. The inverse-comorphism left action from
[HarrisTaylorCMGeometricGalois](HarrisTaylorCMGeometricGalois.md) instead
uses g_(σ⁻¹). The present diagram uses the displayed raw maps.

The coefficient construction additionally retains `[Module.Finite ℚ A]`,
a number field K, a finite K-module W and

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

Put `R = HarrisCoefficientIntegers K p`, the full product of the coefficient
valuation rings above p, and write

```text
S = cmHarrisCoefficientSystem ... q U ρ p m hm existence geometry hRigid,
P = EtaleInverseImage.inverseImage π R,
S̄ = cmHarrisGeometricCoefficientSystem ... = S ⋙ P,
B̄ = cmHarrisGeometricCoefficientDivisibleSystem ...,
I_σ = EtaleInverseImage.inverseImage g_σ R,
Ψ_σ = cmHarrisGeometricCoefficientGaloisIso ... σ : S̄ ⋙ I_σ ≅ S̄.
```

These are the original coefficient sheaves and maps. S uses the existing
stable lattice, its quotients by powers of m, the inverse-unop residual
action, the constructed coefficient-kernel covers and the original
reductions. B̄ has this same geometric tower and its specified
cokernel-defined normalized inclusions. Every nonzero natural m, including
1, and every nonnegative exponent are allowed. The inverse-image functors
are those on the actual small étale sites and apply to arbitrary scheme
morphisms. In particular, no étaleness of π is required.

## The actual scheme diagram

Let `J = ℕᵒᵖ × SingleObj G`. Write its objects as `(r,*)` and its arrows
as `(f,σ)`, where `f : r ⟶ s` in `ℕᵒᵖ`. The `SingleObj` convention is

```text
σ ≫ τ = τ * σ,
(f,σ) ≫ (h,τ) = (f ≫ h, τ * σ).
```

`cmGeometricGaloisCoefficientSchemes` defines

```text
T : J ⥤ Schemeᵒᵖ,
T.obj (r,*) = op X̄,
T.map (f,σ) = op g_σ.
```

The exponent arrow does not change the scheme map. The identity field is
the opposite of the published g_1 law. For composition, the published raw
map law gives `g_τ ≫ g_σ = g_(τ * σ)`; taking opposites gives exactly
`T.map ((f,σ) ≫ (h,τ)) = T.map (f,σ) ≫ T.map (h,τ)`.
The theorems `cmGeometricGaloisCoefficientSchemes_obj` and
`cmGeometricGaloisCoefficientSchemes_map` identify these objects and maps
by definitional equality.

## The coefficient diagram and its laws

`cmHarrisGeometricGaloisCoefficientDiagram` defines
`Dcoeff : CoefficientDiagram R T` by

```text
Dcoeff.obj (r,*) = S̄.obj r,
Dcoeff.map (f,σ) = Ψ_σ.hom.app r ≫ S̄.map f
  : I_σ.obj (S̄.obj r) ⟶ S̄.obj s.
```

The object and combined-map identification theorems have the corresponding
`_obj` and `_map` suffixes and are proved by reflexivity. The coefficient
maps are constructed from the existing Ψ and S̄; neither these maps nor
their functoriality equations are supplied as new input.

For `a : i ⟶ j`, let `I_a = diagramInverseImage R T a`. The published
diagram interface defines its comparisons by

```text
u_i = diagramInverseImageId R T i
    : I_(id_i) ≅ Id,
t_(a,b) = diagramInverseImageComp R T a b
    : I_a ⋙ I_b ≅ I_(a ≫ b).
```

Here u includes equality transport for `T.map_id` followed by
`inverseImageId`; t includes `inverseImageComp` followed by equality
transport for `T.map_comp`. The constructed diagram proves precisely

```text
Dcoeff.map (id_i) = u_i.hom.app (Dcoeff.obj i),
t_(a,b).hom.app (Dcoeff.obj i) ≫ Dcoeff.map (a ≫ b) =
  I_b.map (Dcoeff.map a) ≫ Dcoeff.map b.
```

The identity proof removes S̄'s identity transition and applies the
published finite-stage unit law for Ψ_1.

The composition proof uses a private categorical lemma
`combineCoefficientTransitions`. For a functor S, endofunctors
I₁, I₂, I₃, natural transformations `cₖ : S ⋙ Iₖ ⟶ S` and
`t : I₁ ⋙ I₂ ⟶ I₃`, it proves

```text
t.app (S.obj i) ≫ (c₃.app i ≫ S.map (a ≫ b)) =
  I₂.map (c₁.app i ≫ S.map a) ≫ (c₂.app j ≫ S.map b)
```

from the stagewise cocycle

```text
I₂.map (c₁.app i) ≫ c₂.app i =
  t.app (S.obj i) ≫ c₃.app i.
```

Its proof expands `S.map (a ≫ b)`, substitutes the cocycle and uses the
naturality of c₂ at a, together with associativity and functoriality.
The CM composition field applies this lemma to S̄, its Ψ comparisons and
the actual t_(a,b). The published finite-stage cocycle, with arguments
`b.2` and `a.2`, supplies the premise in the `SingleObj` multiplication
order. Unfolding the actual diagram comparison identifies its composition
and equality transports. All of these fields are proved from the imported
laws; the private helper introduces no public generic framework.

## Pure Galois maps, reductions and original inclusions

`cmHarrisGeometricGaloisCoefficientDiagram_galois` proves

```text
Dcoeff.map (id_r,σ) = Ψ_σ.hom.app r
```

by removing S̄'s identity map. Thus each pure Galois transition is exactly
the original finite-stage comparison.

`cmHarrisGeometricGaloisCoefficientDiagram_reduction` proves, for every
`f : r ⟶ s`,

```text
Dcoeff.map (f,1) =
  u_(r,*).hom.app (S̄.obj r) ≫ S̄.map f.
```

It substitutes the published Ψ_1 law. The inverse-image unit and its
equality transport are retained, so this formula has the actual source
`I_1.obj (S̄.obj r)`.

For natural numbers `r < s`, put `j = B̄.inclusion hrs`. The theorem
`cmHarrisGeometricGaloisCoefficientDiagram_inclusion` proves

```text
I_σ.map j ≫ Dcoeff.map (id_(op s),σ) =
  Dcoeff.map (id_(op r),σ) ≫ j.
```

The proof rewrites the two pure Galois maps and applies the published
compatibility of Ψ with the original normalized inclusion. The statement
therefore concerns the existing inclusion of the original geometric
divisible system, alongside the existing reductions.

## Source and derivation

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99,
specifies the sufficiently small levels, original moduli F-schemes and
level maps. III.2, printed pp.94–96, PDF pp.102–104, constructs the
stable-lattice torsion sheaves with inverse function-equivariance, their
compatible coefficient and cover maps, and geometric cohomology on
`X_U ×_F F^ac`. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The source's F is this module's F, its imaginary quadratic E is this
module's L, and its totally real F⁺ is this module's E.

The product-index scheme diagram and coefficient-diagram packaging are
internal deductions, not displayed constructions attributed to that
passage. They use the published
[CM coefficient Galois comparisons](HarrisTaylorCMGeometricGaloisCoefficients.md),
their unit, cocycle and naturality laws, and the generic
[geometric coefficient-diagram interface](../../Geometry/EtaleGeometricCoefficientDiagram.md).
The scheme diagram follows from the existing raw-map laws; the
coefficient diagram follows from the existing finite-stage coherence and
the original reduction functor. The implemented proof route is the private
categorical calculation described above.

This unit establishes the actual scheme and coefficient diagrams and
their specified map identifications. Cohomological actions, continuity,
level or adic limits, Hecke coefficient maps, analytic comparisons, and
proofs of representability, dual existence, geometry and coarse rigidity
remain separate obligations. Every named premise above remains an
assumption, and acceptance of this focused unit does not complete the
host task. Only published imported definitions and results are reused.
The new Lean and English prose are by Worker 57, in Lean 4.34.0 and
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
