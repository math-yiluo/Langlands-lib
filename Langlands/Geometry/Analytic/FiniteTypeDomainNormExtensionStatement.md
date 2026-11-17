# Statement: the norm of a complete ultrametric field extends to every finitely generated domain

`FiniteTypeDomainNormExtensionStatement` says the following. Let `K` be a
complete nonarchimedean nontrivially normed field, and let `D` be a finitely
generated commutative `K`-algebra that is a domain. Then some multiplicative
seminorm `ν` on `D` extends the norm of `K` and vanishes only at `0`. Such a
`ν` is a multiplicative norm on `D`: in the terms of Temkin's notes, a real
valuation of `D` extending the valuation of `K`.

In Berkovich's language, the claim says that the analytification of
`Spec D` has a point lying over the generic point of `Spec D`. It is the
algebraic input for surjectivity of the center map
(`AnalytificationCenterStatement`, parts (1) and (4)). For a prime `𝔭` of a
finitely generated `K`-algebra `A`, apply the statement to `D = A/𝔭` and
compose with `A → A/𝔭`. The result is a multiplicative seminorm on `A` that
extends the norm of `K` and has kernel exactly `𝔭`.

This is a statement only; its proof is a separate successor.

## Sources

Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990). The registered source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
PDF page = printed page + 14.

- Theorem 3.4.1(i), printed p.63/PDF p.77: for a scheme `X` locally of
  finite type over `k`, the map `π : X^an → X` is surjective.
- Remark 3.4.2, printed p.64/PDF p.78: if `X = Spec(A)`, where `A` is a
  finitely generated ring over `k`, then `X^an` coincides with the set of all
  multiplicative seminorms on `A` whose restriction to `k` is the norm on `k`.
  Under this identification, `π` sends a seminorm to its kernel, a prime
  ideal of `A`.

Take `X = Spec D`. Theorem 3.4.1(i) gives a point over the generic point
`(0)`. By Remark 3.4.2 that point is a multiplicative seminorm on `D` that
extends the norm of `k` and has kernel `(0)`. This is the claimed `ν`.

Temkin, *Valued Fields* (course notes). The registered source is
`temkin-valued-fields-2018-course-notes`, SHA256
`60cbfd7681abcb39ee111aff005434bd6b11054089cf48a78068c97e3d53abe3`.

- §1.2.1, PDF p.1: a *real semivaluation* is a multiplicative seminorm; it is
  a *real valuation* if its kernel is `0`.
- Lemma 1.2.7, PDF p.2: a real valuation on a domain extends to its fraction
  field.
- §1.2.12 and Exercise 1.2.13, PDF p.3: for a non-archimedean real valued
  field `k` and `r > 0`, the generalized Gauss function
  `|∑ aᵢ tⁱ|_r = maxᵢ rⁱ |aᵢ|` is a real valuation on `k[t]`.
- §1.3.6, PDF p.5: an *analytic field* is a complete real valued field.
- Theorem 1.7.7, PDF pp.15–16: the valuation of an analytic field extends
  (uniquely) to every algebraic extension.

These give the classical direct argument sketched below.

Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed
p.19, in the final paragraph of the proof of Proposition 5.11(3), uses the
functorial analytification and its points. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. This
statement is a prerequisite for the Library's center-map statement, which
compares the analytification's points with the points of the scheme.

## Provenance

The formulation is derived. Berkovich states surjectivity of `π` for the
analytic space and identifies the affine analytification with a set of
seminorms. The algebraic consequence stated here, for a finitely generated
domain and its generic point, is the special case of these two statements
that the Library's center-map proof needs. It is stated without reference to
any analytification.

## Hypotheses

- `K : Type u` is a `NontriviallyNormedField` with `IsUltrametricDist K` and
  `CompleteSpace K`. This matches Berkovich's complete non-Archimedean field
  `k` with nontrivial valuation (§3.4, "the case of nontrivial valuation").
- `D : Type v` is a commutative ring with `IsDomain D`, a `K`-algebra
  structure, and `Algebra.FiniteType K D`.

The universes of `K` and `D` are independent.

## The claim

`∃ ν : MulRingSeminorm D, ExtendsNorm K ν ∧ ∀ a : D, ν a = 0 → a = 0`.

- `MulRingSeminorm D` is Mathlib's multiplicative ring seminorm: `ν 0 = 0`,
  `ν 1 = 1`, `ν (a * b) = ν a * ν b`, `ν (-a) = ν a` and
  `ν (a + b) ≤ ν a + ν b`.
- `ExtendsNorm K ν` comes from `AffineAnalytificationSeminorm`. It means
  `ν (algebraMap K D c) = ‖c‖` for every `c : K`.
- The last conjunct says the kernel of `ν` is `0`.

The statement does not require `ν` to be ultrametric. Every multiplicative
seminorm extending the norm of an ultrametric field is ultrametric (Temkin,
Theorem 1.2.3, PDF p.2), so an ultrametric `ν` is no stronger.

## Why the claim is expected to hold

This is a truth check, not the proof.

By Noether normalization, `D` is a finite extension of a polynomial
subalgebra `K[t₁, …, tₙ]`. The Gauss norm on `K[t₁, …, tₙ]` is multiplicative
(Gauss's lemma; Temkin §1.2.12, applied one variable at a time). It extends
to `F = K(t₁, …, tₙ)` by Lemma 1.2.7, and then to the completion `F̂`.
`L = Frac D` is a finite extension of `F`, so `L ⊗_F F̂` is a nonzero finite
`F̂`-algebra. Its quotient `L'` by a maximal ideal is a finite field extension
of `F̂`. By Temkin's Theorem 1.7.7 the absolute value of `F̂` extends to `L'`.
The composite `D → L → L'` is injective, because `L → L'` is a homomorphism
of fields. So the pulled-back absolute value is multiplicative with kernel
`0`. It restricts to the Gauss norm on `K[t]`, hence to `‖·‖` on `K`.

Berkovich's argument gives the same result. In the Library's affine model,
the statement also follows from surjectivity of the affine center map,
`AnalytificationCenterStatement`(1), for a finite polynomial presentation
of `D`. Take a point `x` whose center is the zero ideal. Then
`pointSeminorm K P x` extends the norm (the proved
`pointSeminorm_extendsNorm`), and its kernel is the center (`center_asIdeal`),
which is `0`. This statement is meant as an input to the proof of that
surjectivity, so its own proof should not go through it.

## Scope

The statement concerns one finitely generated domain at a time. It does not
claim uniqueness, which fails in general. It does not describe the set of
such norms, does not assert any topological property, and does not mention
the analytification. The trivially valued and Archimedean cases are not
covered.
