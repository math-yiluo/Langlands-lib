# Finite-jet detection over arbitrary coefficient rings

Let `B` be a smooth commutative `R`-algebra, let
`ε : B →ₐ[R] R` be an augmentation and let `J` be a finitely generated
ideal. The theorem `Algebra.SectionJet.exists_order_of_finite_ideal_vanishing_near_section`
gives a single order `n` for all `R`-algebras `S`. If the image of `J` is
zero in `S ⊗[R] (B / (ker ε)^(n + 1))`, there is `f` in `S ⊗[R] B`
which evaluates to `1` at the base-changed section and annihilates the
image of `J`. Thus the ideal vanishes on a principal open containing the
section.

The proof takes a smooth Noetherian model carrying the augmentation and
the ideal. Over a test algebra `S`, `NoetherianModel.scalarExtensionEquiv`
identifies its scalar extension with `S ⊗[R] B`. The isomorphism preserves
the augmentations and the extended ideals. Hence it identifies powers
of the augmentation kernels and preserves the test that the ideal
vanishes on a jet. Applying the Noetherian finite-order theorem to the
model gives the order and a principal open, whose defining element
maps to the one required over `S`.

This is an internal application of smooth algebra descent, the model
comparison, and the Noetherian finite-jet vanishing lemma.
