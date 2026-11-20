# Noetherian models of smooth affine sections and ideals

Let `B` be a smooth commutative `R`-algebra with an augmentation
`ε : B →ₐ[R] R` and a finitely generated ideal `J`. The construction
`Algebra.SectionJet.noetherianModel` supplies a Noetherian ring `A` mapping
to `R`, a smooth `A`-algebra `B₁` with augmentation `ε₁`, and an ideal
`J₁` of `B₁`. The comparison `R ⊗[A] B₁ ≃ₐ[R] B` intertwines the two
augmentations, and `J₁` extends to `J` along `B₁ → B`.

The proof starts with Mathlib's smooth model `B₀` over a finitely generated
`ℤ`-subalgebra `R₀` of `R`. Evaluate the finite algebra generators of `B₀`
at the section and express the finite ideal generators of `J` as sums
of pure tensors in `R ⊗[R₀] B₀`. Adjoining their coefficients and the
evaluation values to `R₀` gives `A`. The augmented algebra over `A` is
`A ⊗[R₀] B₀`, and the chosen tensors with coefficients in `A` generate
its ideal. The tensor comparison verifies the evaluation and recovers
the chosen generators of `J`.

This internal construction supplies the smooth affine model with a
section and ideal needed to apply finite-jet vanishing over a Noetherian
base. It adds the section and ideal to Mathlib's smooth algebra descent.
