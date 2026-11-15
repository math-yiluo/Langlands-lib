# Statement: affine analytification carries tensor products to fibre products

`AffineAnalytificationFibreProductStatement` states that the polynomial-locus
analytification of affine schemes sends the pushout square of algebras

```text
C ──→ A
│     │
↓     ↓
B ──→ A ⊗[C] B
```

to a pullback square in the Library's localized category of analytic spaces.
So `Spec(A ⊗[C] B)ᵃⁿ` is the fibre product of `Spec(A)ᵃⁿ` and `Spec(B)ᵃⁿ`
over `Spec(C)ᵃⁿ`. It is a `Prop`-valued definition; this unit supplies no
proof. It imports only the published `AffineAnalytificationLocalizedMap`.

## Provenance

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`:

- §2.6, printed p.51/PDF p.48, considers a scheme `𝒴` locally of finite type
  over `𝒳` and the functor from good analytic spaces `Z → X` over `k` to sets,
  `Z ↦ Hom_𝒳(Z, 𝒴)`. Proposition 2.6.1 states that this functor is
  representable by `𝒴ᵃⁿ → X`, and that "the correspondence `𝒴 ↦ 𝒴ᵃⁿ` is a
  functor which commutes with extensions of the ground field and with fibred
  products". The case used here is `X = M(k)`, the analytic space of the
  ground field.
- Proposition 1.4.1 and its proof, printed pp.29–30/PDF pp.26–27, construct
  fibre products in the category of `k`-analytic spaces by gluing the affinoid
  products `V ×_U U'`.

Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990), Theorem 3.4.1, printed p.63/PDF p.77, defines `𝒳ᵃⁿ` for a scheme `𝒳`
locally of finite type over `k` as the analytic space representing
`𝒵 ↦ Hom_k(𝒵, 𝒳)`. Step (3) of its proof, printed p.64/PDF p.78, builds the
affine case from affine space and closed subschemes. The registered source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed
p.19, proof of Proposition 5.11(3), uses the analytification of [CT]
(Conrad–Temkin), in the sense of rigid-analytic spaces, for separated algebraic
spaces locally of finite type over `k`. He describes it as "compatible with
fiber products, open and closed immersions, étale maps, the scheme case, and
extension of the ground field". The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The statement is a derived formulation. It is the affine case of Berkovich's
fibre-product compatibility, for the Library's explicit polynomial-locus model
and its localized category. Berkovich and Conrad speak of fibre products of
schemes; for affine schemes, `Spec(A) ×_{Spec(C)} Spec(B) = Spec(A ⊗[C] B)`.
That identification is standard scheme theory and is not stated in Lean here.
The Lean statement is phrased directly with the tensor product. The Library's
`LocalizedCategory` implements Berkovich's category of `k`-analytic spaces:
saturated presentations and strong maps, localized at quasi-isomorphisms
(Berkovich 1993, Definitions 1.2.7–1.2.9, printed pp.18–20/PDF pp.15–17).
Rigid-analytic spaces in Conrad's sense are not formalized here.

## Hypotheses

- `K : Type u` is a nontrivially normed, ultrametric, complete field.
- `C : Type v` is a commutative `K`-algebra.
- `A : Type w` and `B : Type x` are commutative rings with `K`-algebra and
  `C`-algebra structures such that `K → C → A` and `K → C → B` are scalar
  towers (`IsScalarTower K C A`, `IsScalarTower K C B`).
- `PC`, `PA`, `PB` and `PT` are finite polynomial presentations over `K` of
  `C`, `A`, `B` and `A ⊗[C] B`. The `K`-algebra structure on `A ⊗[C] B` is
  Mathlib's `Algebra.TensorProduct.leftAlgebra`, through `A`. Mathlib's
  scalar-tower instance for `K → C → A ⊗[C] B` lets the `C`-algebra map
  `includeRight` be restricted to a `K`-algebra map.

No other hypothesis is made. The algebras may be zero; for instance,
`A ⊗[C] B` may be zero, with empty analytification.

## The statement

For all such data, the square

```text
localizedHom K PA PT includeLeft                 : localized K PT ⟶ localized K PA
localizedHom K PB PT (includeRight.restrictScalars K) : localized K PT ⟶ localized K PB
localizedHom K PC PA (IsScalarTower.toAlgHom K C A) : localized K PA ⟶ localized K PC
localizedHom K PC PB (IsScalarTower.toAlgHom K C B) : localized K PB ⟶ localized K PC
```

is a pullback square in `LocalizedCategory` (Mathlib's `IsPullback`, with the
first two morphisms as the projections). Here `includeLeft : A →ₐ[K] A ⊗[C] B`
is `a ↦ a ⊗ 1`, and `includeRight : B →ₐ[C] A ⊗[C] B` is `b ↦ 1 ⊗ b`, viewed
as a `K`-algebra map. `localizedHom K P Q f : localized K Q ⟶ localized K P`
is the published morphism of analytifications induced by `f`.

`IsPullback` has two parts:

1. The square commutes: the two composites `localized K PT ⟶ localized K PC`
   are equal.
2. For every object `T` of `LocalizedCategory` and morphisms
   `φ : T ⟶ localized K PA`, `ψ : T ⟶ localized K PB` with equal composites
   to `localized K PC`, there is a unique morphism `T ⟶ localized K PT` whose
   composites with the two projections are `φ` and `ψ`.

The test object `T` is arbitrary. It need not be an analytification, good,
or Hausdorff.

## Truth sketch

This is not a Lean proof. Commutativity follows from the published
`AffineAnalytificationLocalizedFunctorialityStatement`, conjunct 4, because
`includeLeft ∘ (C → A) = includeRight ∘ (C → B)` as `K`-algebra maps
`C → A ⊗[C] B`.

For the universal property, Berkovich 1990, Theorem 3.4.1, gives
`Hom(T, Spec(A)ᵃⁿ) = Hom_k(T, Spec(A))` for analytic spaces `T` in the sense
of that book, which are good. For an affine scheme the right side is
`Hom_k(A, 𝒪(T))`, naturally in `A`. The universal property of `A ⊗[C] B` then identifies
`Hom(T, Spec(A ⊗[C] B)ᵃⁿ)` with compatible pairs of maps from `A` and from
`B`. Berkovich's 1993 statement represents the functor on good spaces only.
For an arbitrary test space the argument can be run chart by chart. A morphism
in the localized category is a strong map from a refinement of the atlas of
`T`, and a strong map into a polynomial-locus model is a compatible family of
maps from affinoid charts. On an affinoid chart `M(𝒜)`, maps to `Spec(A)ᵃⁿ`
correspond to `K`-algebra maps `A → 𝒜`. The same argument shows existence and
uniqueness of the factorization.

Alternatively: the fibre product `Spec(A)ᵃⁿ ×_{Spec(C)ᵃⁿ} Spec(B)ᵃⁿ` exists
by Berkovich 1993, Proposition 1.4.1. Its affinoid domains `V ×_U U'` show
that it is good when the three factors are good. Analytifications of affine
schemes are good. It and `Spec(A ⊗[C] B)ᵃⁿ` represent the same functor on
good spaces, so the comparison morphism is an isomorphism by Yoneda's lemma
on good spaces.

## Scope

The statement covers only affine schemes given by finite polynomial
presentations over the ground field `K`. It does not cover nonaffine schemes,
analytification over a base other than `M(K)`, the identification
`Spec(A) ×_{Spec(C)} Spec(B) = Spec(A ⊗[C] B)` as schemes, extension of the
ground field, étale maps, or algebraic spaces. It does not compare the
morphism with the glued fibre product of the Library's `AnalyticFibreProduct`.
Fibre products of analytic spaces are generally not fibre products of the
underlying topological spaces, and nothing here asserts that.
