# Polynomial presentations of local algebras modulo the square of the maximal ideal

This module formalizes the presentation step in the proof of Stacks Project Lemma
98.10.1 (Tag 07XB, `artin.pdf` printed p. 15). Stacks chooses a surjection
`Λ[x₁, …, x_s] → k` and lifts it to `R`. It then adds variables mapping to
generators of `m_R`, so that `Λ[x₁, …, x_s] → R/m_R^2` is surjective. The provenance
is source.

`exists_mvPolynomial_surjective_mod_sq` takes a commutative ring `R : Type u`, a
field `K` that is a finite-type `R`-algebra, a Noetherian local `R`-algebra
`A : Type u`, and a surjective `R`-algebra map `ε : A →ₐ[R] K`. It gives a finite
type `ι : Type u` and `σA : MvPolynomial ι R →ₐ[R] A` such that every `a : A` has
some `s` with `a - σA s ∈ (maximalIdeal A) ^ 2`.

The index type is `ULift (Fin n ⊕ Fin k)`. The first `n` variables map to lifts
along `ε` of the images of the variables of a surjection
`MvPolynomial (Fin n) R → K`. The last `k` variables map to generators of the
maximal ideal, which is finitely generated because `A` is Noetherian. The residue
map of `σA` is then surjective. Given `a`, choose `s₀` with `ε (σA s₀) = ε a`. Write
`a - σA s₀ = ∑ c l * g l` with the generators `g l`. Choose `sc l` with
`ε (σA (sc l)) = ε (c l)`. Then
`a - σA (s₀ + ∑ sc l * X l) = ∑ (c l - σA (sc l)) * g l` lies in
`(maximalIdeal A) ^ 2`.
