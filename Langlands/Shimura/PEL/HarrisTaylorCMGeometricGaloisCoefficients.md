# Coherent Galois inverse images of the original geometric CM coefficients

Author: Worker 57.

This module constructs canonical inverse-image isomorphisms for the
original geometric CM coefficient system under the constructed Galois
scheme maps. Their unit and cocycle laws include the actual
inverse-image composition and equality comparisons. They commute with
every original reduction and with the original normalized inclusions.
The geometric projection is an arbitrary scheme morphism throughout.

## Arithmetic, geometric and coefficient hypotheses

All arithmetic carriers have universe zero. The input
`D : CentralSimpleUnitaryData E F A n` retains a totally real number
field E, a totally complex CM number field F quadratic over E and the
compatible E-, F- and rational algebra structures on A. An imaginary
quadratic number field L, its algebra map to F, an embedding
`τ₀ : L →+* ℂ` and

```text
C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀)
```

give the unchanged signature charts.
The named premises are pullback-tensor comparison, composition, unit
coherence, associativity, left-unitor comparison and symmetry; Picard-zero
pullback, the Mumford-square assertion and universal base change; dual
abelian base-change naturality, polarization base change and relative
finite Weil transition; `h : Global.RationalProfiniteIntegerAdeleComparison`;
and `htor : TorsionFiniteEtaleStatement.{0}`. The representability premise
is exactly

```text
q : CMRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor.
```

It requires the existing original small-level moduli presheaves on the
componentwise admissible CM base category to have actual admissible,
smooth projective representing F-schemes. The chosen scheme tower and
its maps are those recovered from q by the existing construction.
The componentwise admissibility and geometric-point restrictions in that
premise are retained. The module does not replace q by supplied
arbitrary schemes.

Fix `U : SmallCMLevel D`. Write

```text
X = (cmSchemeTower ... q).obj U,
X̄ = (cmGeometricSchemeTower ... q).obj U,
π = (cmGeometricProjection ... q).app U : X̄ ⟶ X,
g_σ = (cmGeometricGaloisMap ... q σ).app U,
Ω = AlgebraicClosure F.
```

Thus X̄ is the actual scheme fiber product `X ×_(Spec F) Spec Ω`, π is
its first projection and g_σ is the actual lift that fixes π and acts
on the second factor by `Spec σ`. In particular,

```text
e_σ : g_σ ≫ π = π,
i : g_1 = id_X̄,
μ_(σ,τ) : g_σ ≫ g_τ = g_(σ * τ).
```

The first equation is the published projection theorem.
`cmGeometricGaloisMap_app_one` and
`cmGeometricGaloisMap_app_mul` extract the latter two equalities from the
proved natural-transformation laws by evaluation at U. They require no
coefficient ring.

The first part of this module works with every commutative ring
`R : Type`, independently of the coefficient representation. Put

```text
P = EtaleInverseImage.inverseImage π R,
I_σ = EtaleInverseImage.inverseImage g_σ R.
```

P is the published inverse image on module sheaves on the actual small
étale sites. Its construction applies to arbitrary scheme morphisms.
No étaleness, finiteness or finite presentation of π is assumed.

## Canonical comparisons for all original sheaves

For a morphism `f : Z ⟶ X` and `a : V ⟶ Z`, denote the published
comparison `inverseImageComp R f a` by c(f,a). It has type

```text
f* ⋙ a* ≅ (a ≫ f)*.
```

For an equality e of base morphisms, write d(e) for
`inverseImageCongr R e`. These comparisons are determined by the actual
inverse-image adjunctions and geometric direct-image comparisons.

`cmGeometricGaloisInverseImageIso σ` is the natural isomorphism

```text
C_σ : P ⋙ I_σ ≅ P,
C_σ = c(π,g_σ) ≪≫ d(e_σ).
```

This is the canonical comparison for pulling an original sheaf back
along π and then along g_σ. Its inverse is the inverse of this displayed
composite of actual isomorphisms. Neither an inverse-image comparison nor
an equivariance witness is supplied as additional input.

`cmGeometricGaloisInverseImageIso_one` proves, for every original
`M : Sheaf X.smallEtaleTopology (ModuleCat R)`,

```text
C_1.hom.app M =
  d(i).hom.app (P.obj M) ≫
    (inverseImageId R X̄).hom.app (P.obj M).
```

The equality transport from g_1 to the scheme identity is retained.
The private implementation first substitutes that equality and then
applies the published source-identity coherence
`inverseImageComp_id_source`. The unitor component is removed using
the categorical identity law.

`cmGeometricGaloisInverseImageIso_mul` proves the cocycle equation

```text
I_σ.map (C_τ.hom.app M) ≫ C_σ.hom.app M =
  c(g_τ,g_σ).hom.app (P.obj M) ≫
    d(μ_(σ,τ)).hom.app (P.obj M) ≫
      C_(σ * τ).hom.app M.
```

The common source is the inverse image of `P.obj M` first along g_τ
and then along g_σ. The intermediate c comparison therefore has the
displayed order. The raw maps use σ as comorphism:
`(σ * τ)(x) = σ(τ(x))`, and
`g_(σ * τ) = g_σ ≫ g_τ`.
This module works with that raw normalization. The inverse-comorphism
left action on schemes in
[HarrisTaylorCMGeometricGalois](HarrisTaylorCMGeometricGalois.md) sends
σ to the map g_(σ⁻¹); substituting σ⁻¹ in C gives its corresponding
coefficient comparison.

The implemented cocycle proof expands C, moves equality transport past
the composition comparison, and applies the published
`inverseImageComp_assoc`. It moves the equality μ through the other
composition comparison and combines the resulting equality transports.
The two resulting proofs assert the same equality from
`(g_σ ≫ g_τ) ≫ π` to π and agree by proof irrelevance.
The private equality-transport lemmas are proved by substitution and the
published `inverseImageCongr_refl`; they introduce no assumed coherence.
The private fixed-projection comparison and its unit and composition
lemmas organize this proof inside the specialization. No new public
generic inverse-image or equivariant-sheaf framework is introduced.

## The unchanged original coefficient system

The concrete coefficient part additionally assumes
`[Module.Finite ℚ A]`, a number field K, a finite K-module W and

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

Let `R₀ = HarrisCoefficientIntegers K p`, the full product of the
coefficient valuation rings above p. In this part P and I_σ use R₀.
Write

```text
S = cmHarrisCoefficientSystem ... q U ρ p m hm existence geometry hRigid,
B = cmHarrisCoefficientDivisibleSystem ...,
S̄ = cmHarrisGeometricCoefficientSystem ... = S ⋙ P,
B̄ = cmHarrisGeometricCoefficientDivisibleSystem ... = B.map P.
```

S uses the existing full stable lattice, its quotients by powers of m,
the inverse-unop residual action and the constructed coefficient-kernel
covers. Its transition maps are the specified original reductions with
their existing cover comparisons. B has exactly S as its tower and its
original cokernel-defined normalized inclusions. The module retains all
these sheaves and maps. The scalar may be any nonzero natural number,
including 1; exponents include zero.

`cmHarrisGeometricCoefficientGaloisIso σ` is the natural isomorphism

```text
Ψ_σ : S̄ ⋙ I_σ ≅ S̄
```

obtained by the functor associator
`(S ⋙ P) ⋙ I_σ ≅ S ⋙ (P ⋙ I_σ)` followed by whiskering C_σ with S.
`cmHarrisGeometricCoefficientGaloisIso_hom_app` identifies its component
at `r : ℕᵒᵖ` with exactly `C_σ.hom.app (S.obj r)`. The associator
component is the identity, so the proof removes that identity and makes
no alternate choice of coefficient sheaf.

## Original reductions, inclusions and group coherence

`cmHarrisGeometricCoefficientGaloisIso_reduction` states, for every
arrow `f : r ⟶ s` of the original inverse-index category,

```text
I_σ.map (S̄.map f) ≫ Ψ_σ.hom.app s =
  Ψ_σ.hom.app r ≫ S̄.map f.
```

This is the naturality equation of the constructed isomorphism of the
entire original inverse diagram.

For `r < s`, let `j = B̄.inclusion hrs`. The theorem
`cmHarrisGeometricCoefficientGaloisIso_inclusion` proves

```text
I_σ.map j ≫ Ψ_σ.hom.app (op s) =
  Ψ_σ.hom.app (op r) ≫ j.
```

The proof applies naturality of C_σ to the original
`B.inclusion hrs`. It uses the existing identities identifying B's tower
with S and identifying j with `P.map (B.inclusion hrs)`.
Thus the equation concerns precisely the original normalized inclusion,
alongside the original reductions.

`cmHarrisGeometricCoefficientGaloisIso_one` and
`cmHarrisGeometricCoefficientGaloisIso_mul` specialize the proved unit
and cocycle equations to `M = S.obj r` for every `r : ℕᵒᵖ`.
They use the displayed i and μ comparisons and `S̄.obj r` in place of
`P.obj M`. These are the actual canonical unit and cocycle equations
for the coefficient isomorphisms, rather than group laws assumed as
data. Their proofs rewrite the component identification and apply the
all-sheaf comparison theorems.

## Source, derivation and remaining scope

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99,
specifies the original moduli F-schemes and level maps. III.2, printed
pp.94–96, PDF pp.102–104, gives the original stable-lattice torsion
sheaves, inverse function-equivariance and compatible coefficient and
cover maps, then forms cohomology on `X_U ×_F F^ac`. Printed p.97,
PDF p.105, states the eventual continuous Galois action on that
cohomology. Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The source's F is this module's F, its imaginary quadratic E is this
module's L, and its totally real F⁺ is this module's E.

The source supplies the arithmetic-geometric and original-coefficient
context. The present comparisons and all their coherence equations are
internal deductions from the published
[geometric coefficients](HarrisTaylorCMGeometricCoefficients.md),
[scheme maps](HarrisTaylorCMGeometricGalois.md),
[inverse-image comparisons](../../Geometry/EtaleImageFunctoriality.md)
and [their coherence](../../Geometry/EtaleInverseImageCoherence.md).
The displayed raw comorphism convention and particular coherence
formulas are specified here; they are not asserted to be formulas
printed in the cited passage.

This unit constructs coherent inverse-image coefficient comparisons
at each represented small level. It does not package them as an object
of a separate equivariant-sheaf category, construct coefficient maps
for Hecke correspondences, construct a cohomological action or prove
its continuity, form level or adic limits, prove analytic comparisons,
or discharge representability, coarse rigidity or the remaining
geometric existence and descent obligations of the host task.
All named premises remain assumptions. The generic inverse-image and
action infrastructure remains imported or separate.
Only published imported results are used, with no reused unreviewed
draft. The new Lean and English prose are by Worker 57 in Lean 4.34.0
and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
