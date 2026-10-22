# Subfields of the complex numbers are fixed fields

Author: Worker 57. This file states a proposition. It does not prove it.

`ComplexFixedFieldStatement` says that every intermediate field `L` of
`ℂ / ℚ` is the fixed field of its own fixing group. In Lean the fixing group
is `IntermediateField.fixingSubgroup L`, the subgroup of `ℂ ≃ₐ[ℚ] ℂ` of
automorphisms fixing `L` pointwise. The fixed field is
`IntermediateField.fixedField`. Every ring automorphism of `ℂ` fixes `ℚ`, so
`ℂ ≃ₐ[ℚ] ℂ` is Kottwitz's group `Aut(ℂ/ℚ)`. The quantifier covers all
subfields of `ℂ`, including transcendental ones and those of infinite degree.
The proposition does not assume that `L` is finite-dimensional, that `ℂ` is
algebraic over `L`, or that any extension is Galois.

The inclusion `L ≤ fixedField (fixingSubgroup L)` holds by definition, so the
content is the reverse inclusion. For any `x ∈ ℂ` outside `L` there must be an
automorphism of `ℂ` that fixes `L` and moves `x`. Mathlib's
`IsGalois.fixedField_fixingSubgroup` and
`InfiniteGalois.fixedField_fixingSubgroup` do not apply here, because `ℂ` is
not algebraic over `ℚ`.

## Why it is needed

Kottwitz (1992), printed page 655, defines the reflex field as "the fixed
field of the stabilizer in Aut(ℂ/ℚ) of the function i ↦ n(i)". Harris (1997),
printed page 89, states that the reflex field `E(GG, X_{n-1})` "is just
`t₁(K)`". Here `t₁` is the place of the CM type above `σ₁`. A companion module,
`Langlands.Shimura.Unitary.Reflex`, was submitted with the positivity and
reflex-field definitions. Its theorem
`HarrisSignatureCharts.reflexField_eq_distinguishedImage` concludes
`C.reflexField = C.distinguishedImage`, where `C.distinguishedImage` is the
image `Φ τ₁ (K)` of the CM field. It needs two hypotheses. The first is that
`n ≥ 3` or there is a second real place. The second, `hgal`, is the equality
`fixedField (fixingSubgroup C.distinguishedImage) = C.distinguishedImage`.
That module's theorems show that the stabilizer contains the fixing group of
`Φ τ₁ (K)`, and under the first hypothesis is contained in it. The present
proposition, applied to `L = C.distinguishedImage`, is exactly `hgal`. A proof
would therefore turn the conditional identification into Harris's statement,
whenever the first hypothesis holds. The present Lean file does not import
that module and does not formalize this deduction.

## Provenance

The proposition is a derived general obligation. It is not a displayed
statement in Kottwitz or Harris; both use it implicitly when identifying the
reflex field with an explicit subfield of `ℂ`. It is the characteristic-zero
case of the classical fact about an algebraically closed field `Ω` and a
subfield `L`: the field fixed by `Aut(Ω/L)` is the perfect closure of `L`. In
characteristic zero that closure is `L`. The statement here is specialized to
`Ω = ℂ`, the field used by Kottwitz. Its generality goes beyond the number
fields needed for Harris, but the expected proof is the same.

Sources: Kottwitz, *On the λ-adic representations associated to some simple
Shimura varieties*, Invent. Math. 108 (1992), printed page 655
(`kottwitz-1992-lambda-adic-simple-shimura`, SHA-256
`749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`); Harris,
*Supercuspidal representations in the cohomology of Drinfel'd upper half
spaces; elaboration of Carayol's program*, Invent. Math. 129 (1997), printed
page 89 (`harris-1997-drinfeld-cohomology`, SHA-256
`aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`). Formal
dependencies: Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`,
Lean 4.34.0, modules `Mathlib.Basic.Complex.Basic` and
`Mathlib.FieldTheory.Galois.Basic`.

## Expected proof

A proof must establish the whole declaration for every intermediate field.
Let `x ∉ L`. If `x` is algebraic over `L`, its minimal polynomial is separable
of degree at least two, so it has a second root `y ≠ x` in `ℂ`. Then
`x ↦ y` gives an `L`-isomorphism `L(x) → L(y)`. If `x` is transcendental over
`L`, then `x ↦ x + 1` gives an `L`-automorphism of `L(x)`; put `y = x + 1`, so
that `L(y) = L(x)`. Choose a transcendence basis `B` of `ℂ` over `L(x)`. It is
also a transcendence basis over `L(y)`: in the first case both fields are
algebraic over `L`, and in the second they are equal. Fixing `B` extends the
isomorphism `L(x) → L(y)` to an isomorphism `L(x)(B) → L(y)(B)` of rational
function fields. `ℂ` is an algebraic closure of both, so this isomorphism
extends to an automorphism of `ℂ` (`IsAlgClosure.equivOfEquiv`). The resulting
automorphism fixes `L` and sends `x` to `y ≠ x`. This sketch is not formalized
here.
