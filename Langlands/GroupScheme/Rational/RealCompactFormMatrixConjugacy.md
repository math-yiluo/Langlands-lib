# Matrix conjugation for compact real forms

`Langlands.GroupScheme.RealCompactFormUniqueness.exists_closed_representation_with_real_conjugator`
takes connected reductive real groups `G` and `H` with compact real points and
an isomorphism from the complexification of `H` to that of `G`. It constructs
a closed matrix representation of `G` over ℝ and a complex invertible matrix
`c` normalizing the image of `G(ℂ)`. Conjugating the transported `H(ℝ)` by `c`
gives matrices whose entries are fixed by every ℝ-algebra automorphism of ℂ.

The closed representation comes from `affineLinearEmbeddingStatement`.
Its complex matrix image `A` is defined by polynomial equations in entries and
inverse entries. The two subgroups of `A` obtained from the real points are
compact by continuity of scalar extension, the isomorphism on complex points,
and matrix evaluation for the canonical rational-point topologies. Each is
polynomially dense in `A`. To prove this, pull a polynomial back along the
representation to a regular function and use density of the extended real
points to show its basic open is empty. Smoothness makes the complex group
reduced, so the regular function vanishes. The argument applies to `H` through
the representation pulled back along the supplied isomorphism.

The invariant-form theorem gives positive definite Hermitian forms `J₁` and
`J₂` preserved by the respective compact subgroups. Polynomial density gives
stability of `A` under both form adjoints. `exists_mean` gives a positive form
`X` with `X J₁⁻¹ X = J₂` and a form adjoint preserving `A`.
The matrix `c = J₁⁻¹ X` normalizes `A` and satisfies `c⋆ J₁ c = J₂`, so its
conjugation carries preservation of `J₂` to preservation of `J₁`.
For any element `g` of `A` preserving `J₁`, the adjoint coordinate polynomials
evaluate to the conjugated entries of `g⁻¹`. Their differences from the
inverse-entry coordinates vanish on the dense real subgroup from `G(ℝ)`.
They therefore vanish at `g`, forcing the entries of `g⁻¹` and hence of `g`
to lie in ℝ.

This is a derived matrix step for `RealCompactFormUniquenessStatement`.
Borel's *Lie Groups and Linear Algebraic Groups, I. Complex and Real
Groups*, retained source `borel-lie-groups-linear-algebraic-groups-2000`,
Sections 5.6–5.7, printed and one-based PDF page 40, gives inner conjugacy
and discusses algebraicity of compact real forms. The Lean construction
uses the ambient matrix normalizer. This supplies the conjugator for the
group-scheme restriction and descent in the proof of uniqueness.
