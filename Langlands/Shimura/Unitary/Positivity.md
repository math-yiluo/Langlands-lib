# Positive involutions and Kottwitz's homomorphism for the Harris datum

Author: Worker 57. This module defines positivity of an involution of a real
algebra and builds Kottwitz's archimedean homomorphism `h₀` for the corrected
Harris datum. It proves that the involution twisted by `h₀(i)` is positive.
This is the positivity hypothesis of Kottwitz (1992), p.654.

## The source conditions

Kottwitz (1992), printed p.654, works with a division algebra `D` whose
center is a CM field `F` with totally real subfield `F₀`, and with an
involution `x ↦ x*` of the second kind. He then writes:

> Let h₀ be an ℝ-algebra homomorphism h₀: ℂ → D ⊗_ℚ ℝ such that
> h₀(z)* = h₀(z̄) for all z ∈ ℂ. Then the map x ↦ h₀(i)⁻¹ x* h₀(i) is an
> involution of D ⊗_ℚ ℝ. We assume further that this involution is positive.
> The inverse of the restriction of h₀ to ℂ^× gives us a homomorphism
> h: R_{ℂ/ℝ}𝔾_m → G_ℝ.

Positivity is defined in Milne, *Introduction to Shimura varieties* (in
Arthur–Ellwood–Kottwitz 2005), Section 8. For a semisimple `ℝ`-algebra `C`
with involution `∗`, Proposition 8.10 lists three equivalent conditions, of
which (c) is

> Tr_{C/ℝ}(c∗c) > 0 for all nonzero c ∈ C.

Definition 8.11 reads: "An involution satisfying the equivalent conditions of
(8.10) is said to be positive." Here `Tr_{C/ℝ}` is the trace of the regular
representation: Milne's proof of (b) ⇒ (c) computes `Tr_ℝ(c∗c|V)` for a
module `V` and ends "On applying this remark with V = C, we obtain (c)."

## Declarations

- `AlgebraInvolution.IsPositive σ` is Milne's condition (c). For every nonzero
  `x`, the real trace of left multiplication by `σ x * x` on `A` is positive.
  Lean's `LinearMap.trace` is the trace of the regular representation when
  `A` is free of finite rank over `ℝ`, and Mathlib defines it to be `0`
  otherwise. So the predicate holds for no nonzero algebra that is not finite
  dimensional. Semisimplicity is not assumed; the predicate is used here only
  for the semisimple algebra `∏ M_n(ℂ)`.
- `ComplexHom.conj h` precomposes a homomorphism `h` with complex
  conjugation, and proves the compatibility `σ(h(z)) = h(z̄)` again.
- `ComplexHom.twist h` is the involution `x ↦ h(-i) σ(x) h(i)`. Since
  `h(-i) h(i) = h(1) = 1`, `h(-i)` is the inverse of `h(i)`, so this is
  Kottwitz's map `x ↦ h₀(i)⁻¹ x* h₀(i)`. The structure proves that it is
  real linear, unital, reverses products and squares to the identity. The
  last property uses the compatibility `σ(h(z)) = h(z̄)`.
- `twist_conj`: conjugating `h` does not change the twisted involution,
  because `h(-i) = -h(i)`.
- `matrix_repr_apply` and `trace_mulLeft_matrix`: in the real basis of
  matrix units times `1` and `i`, the real trace of left multiplication by
  `y` on complex `n × n` matrices is `2n · Re(tr y)`.
- `trace_mulLeft_pi`: the real trace of left multiplication on a finite
  product of finite free real algebras is the sum of the traces on the
  factors.
- `trace_mulLeft_conjTranspose_mul_self_pos`: for a nonzero complex matrix
  `x`, the real trace of left multiplication by `x^* x` is positive. The
  proof uses Mathlib's results that `x^* x` is positive semidefinite and
  that `tr(x^* x) = 0` only for `x = 0`.
- `piConjTranspose n I` is conjugate transposition on every factor of
  `I → M_n(ℂ)`, and `piConjTranspose_isPositive` proves it positive for a
  finite index type `I`.
- `correctedComplexHom_twist`: at a factor of signature `(r, n-r)`, the
  twist of the involution `signatureAdjoint n r` (that is, `x ↦ J x^* J` with
  `J = diag(1,…,1,-1,…,-1)`) by the published corrected homomorphism
  `correctedComplexHom n r` is conjugate transposition. Indeed
  `h(-i) J` is the scalar `i` and `J h(i)` is the scalar `-i`.
  `harrisArchimedeanHom_twist` states the same on all archimedean factors.
- `kottwitzHom n I τ₁` is `(harrisArchimedeanHom n I τ₁).conj`, Kottwitz's
  `h₀` for the corrected Harris datum (see below). It carries the
  compatibility `h₀(z)* = h₀(z̄)` as a field of `ComplexHom`.
- `kottwitzHom_twist_isPositive` is the positivity certificate: the twisted
  involution of `kottwitzHom` equals `piConjTranspose`, hence is positive.

## Choice of h₀

The published `harrisArchimedeanHom n I τ₁` is the corrected homomorphism of
Harris (1998), Erratum, printed pp.180-182:
`z ↦ ((z̄ I_{n-1}, z), z̄ I_n, …, z̄ I_n)`, with the first block at the
distinguished real place `τ₁`. Harris (1997), printed p.89, uses instead
`h_Φ(z) = ((z I_{n-1}, z̄), z I_n, …, z I_n)`; the Erratum replaces it by its
complex conjugate. Thus `kottwitzHom = harrisArchimedeanHom ∘ conj` is
Harris's original `h_Φ` as an algebra homomorphism.

This is the correct `h₀` for the corrected datum, because Kottwitz uses the
inverse of `h₀`. For `z ∈ ℂ^×`, `h₀(z)⁻¹ = h₀(z⁻¹) = h₀(z̄) / |z|²`, which is
`harrisArchimedeanHom(z) · |z|⁻²`. So Kottwitz's `h` is Harris's corrected
homomorphism times the central real scalar `|z|⁻²`. Multiplying by a central
scalar does not change the centralizer in `G(ℝ)`. This comparison is
explanation only and is not formalized; the module contains no Deligne torus
or cocharacter.
`ComplexHom.twist_conj` shows that the positivity certificate is the same
for both homomorphisms.

## Scope

The module works in the standard archimedean model `I → M_n(ℂ)` with the
involution `harrisArchimedeanInvolution`. It does not construct
`D ⊗_ℚ ℝ ≅ ∏_τ M_n(ℂ)` for a global algebra or transport `h₀` to it.
Milne's equivalences (a)–(c), the uniqueness of `h` up to conjugacy, and
positivity of an involution of a global `ℚ`-algebra are not formalized.

## Sources

- Kottwitz (1992), Section 1, printed p.654 (PDF p.2): `h₀`, its
  compatibility with the involution, positivity of the twisted involution,
  and `h` as the inverse of `h₀` on `ℂ^×`.
- Milne, *Introduction to Shimura varieties*, in Arthur–Ellwood–Kottwitz
  (2005), Proposition 8.10 and Definition 8.11, printed pp.325-326
  (PDF pp.337-338): positive involutions via the regular trace.
- Harris (1997), Section 2, printed p.89 (PDF p.15): `h_Φ`; Harris (1998),
  Erratum, printed pp.180-182: its replacement by the complex conjugate.

These passages were read in the original. The trace computation and the
packaging of `h₀` as `conj` of the published corrected homomorphism are
derived.

Source IDs and SHA-256 fingerprints:

- `kottwitz-1992-lambda-adic-simple-shimura`:
  `749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.
- `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`:
  `88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.
- `harris-1997-drinfeld-cohomology`:
  `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`.
- `harris-1998-local-langlands`:
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.

Formal dependencies: `Langlands.Shimura.Unitary.Domain` (`ComplexHom`,
`correctedComplexHom`, `harrisArchimedeanInvolution`,
`harrisArchimedeanHom`, `AlgebraInvolution.pi`), `Unitary.Signature`
(`signatureMatrix`, `signatureAdjoint`), `Unitary.Involution` (`ofStar`), and
Mathlib `5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0, in
particular `LinearMap.trace_eq_matrix_trace`, `Module.Basis.matrix`,
`Matrix.posSemidef_conjTranspose_mul_self` and
`Matrix.trace_conjTranspose_mul_self_eq_zero_iff`.
