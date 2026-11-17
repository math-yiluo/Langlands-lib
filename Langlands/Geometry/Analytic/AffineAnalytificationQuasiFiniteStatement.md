# Statement: the affine analytification detects quasi-finite maps

Authors: Worker 554 (proposal and Lean form), Worker 3519 (review, Markdown and
submission through parent Task 3519).

`AffineAnalytificationQuasiFiniteStatement` compares algebraic and analytic
quasi-finiteness for a map of finitely generated algebras over a complete
nonarchimedean field. Let `K` be a complete, ultrametric, nontrivially normed
field. Let `A` and `B` be commutative `K`-algebras with finite polynomial
presentations `P` and `Q`, and let `f : A →ₐ[K] B`. The statement says:

`f.toRingHom.QuasiFinite ↔ (saturatedHom K P Q f).IsQuasifinite`.

This is a statement only; its proof is a separate successor. It is a
prerequisite proposed for the proof of `AffineAnalytificationEtaleStatement`
(Task 7169). That proof needs local finiteness of the analytic map before it
can test flatness or unramifiedness on finite pieces.

## Source

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993). The
registered source is `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`. PDF page =
printed page − 3.

- Definition 3.1.1, printed p.54/PDF p.51: a morphism `φ : Y → X` of
  `k`-analytic spaces is *finite at* `y` if there are open neighborhoods `V` of
  `y` and `U` of `φ(y)` such that `φ` induces a finite morphism `V → U`; `φ` is
  *quasifinite* if it is finite at every point.
- Printed p.56/PDF p.53, before Corollary 3.1.7: a morphism of schemes is
  quasifinite if every point is isolated in its fibre ([SGA1], 1.2).
- Corollary 3.1.7, printed p.56/PDF p.53: a morphism `φ : 𝒳 → 𝒴` between
  schemes of locally finite type over `Spec(𝒜)`, where `𝒜` is a `k`-affinoid
  algebra, is quasifinite if and only if `φᵃⁿ : 𝒳ᵃⁿ → 𝒴ᵃⁿ` is quasifinite.

The statement takes `𝒜 = K`, `𝒳 = Spec B` and `𝒴 = Spec A`. For the
analytifications it uses the Library's polynomial-locus model `Space K P`
(`AffineAnalytificationGluing`), with the morphism `saturatedHom K P Q f`
(`AffineAnalytificationLocalizedMap`).

## Provenance

The statement is a direct specialization of Corollary 3.1.7. Two choices are
derived:

- *Algebraic side.* Mathlib's `RingHom.QuasiFinite` (via `Algebra.QuasiFinite`)
  asks that every fibre `P.Fiber B` be finite-dimensional over the residue field
  `P.ResidueField`. Here `B` is a finitely generated `K`-algebra, so `f` is of
  finite type. For maps of finite type, finite-dimensional fibres are the same
  as SGA1 quasi-finiteness: the fibres are finite discrete, so every point is
  isolated in its fibre.
- *Analytic side.* `StrongHom.IsQuasifinite` is the published predicate of
  `FullRecognitionFiniteMorphisms`: `g.IsFiniteAt y` for every point `y`. Here
  `IsFiniteAt y` asks for open neighborhoods `V` of `y` and `U` of its image such
  that `g.IsFiniteOver V U`. That is, over every recognized affinoid subset
  of `U`, the corresponding recognized subset of `V` is an affinoid domain
  finite over it. This is the Library's form of Definition 3.1.1.

## Hypotheses

- `K : Type u` is a `NontriviallyNormedField` with `IsUltrametricDist K` and
  `CompleteSpace K`.
- `A : Type v` and `B : Type w` are commutative `K`-algebras in independent
  universes, with `P : FinitePolynomialPresentation K A` and
  `Q : FinitePolynomialPresentation K B`.
- `f : A →ₐ[K] B` is arbitrary.

Zero algebras are allowed. If `B = 0`, the source analytification is empty and
both sides hold.

## Why the claim is expected to hold

This is a truth check, not the proof. Berkovich's proof runs as follows. For a
point `y` of `𝒴ᵃⁿ` with completed residue field `ℋ(y)`, the fibre of `φᵃⁿ`
over `y` is the analytification of the algebraic fibre after base change to
`ℋ(y)`. That fibre is finite exactly when the algebraic fibre is. Analytic
quasifiniteness then follows because `φᵃⁿ` is closed (Proposition 2.6.1) and
fibres are finite. Conversely, every point of `𝒳` is the center of some
analytic point (Berkovich 1990, Theorem 3.4.1(i)). A finite analytic fibre
forces the algebraic fibre through it to be finite.

## Scope

Only the affine case over the base `K` is stated, with the Library's specified
presentations. The statement is independent of the three equivalences of
`AffineAnalytificationEtaleStatement`. It says nothing about finite morphisms
globally, about closedness, or about ground field extension.
