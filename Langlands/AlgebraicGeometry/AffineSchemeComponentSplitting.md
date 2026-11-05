# Finite separable component splitting for arbitrary affine structure maps

This internal derived module transfers the proved tensor-spectrum splitting construction to any locally finite-type morphism `f : X → Spec K` with `X` affine. It retains an arbitrary field `K` and common universe `u`. All component predicates refer to actual maximal irreducible components with their vanishing-ideal reduced closed scheme structures.

`tensorSpecBaseChangeIso` uses the tensor-product pushout of commutative rings and the spectrum pullback theorem to construct an actual isomorphism from `Spec(L ⊗[K] A)` to the categorical scalar extension of `Spec A`. Its coherence lemma identifies the structural morphism to `Spec L`.

`exists_finite_separable_components_of_SpecMap` gives the finite splitting extension for an arbitrary locally finite-type spectrum map induced by a ring homomorphism `K → A`. Equip `A` with the algebra structure of that homomorphism. The affine finite-type criterion gives `Algebra.FiniteType K A`. The imported tensor-spectrum existence theorem constructs a finite intermediate field `E` of the separable closure with the required component property on its tensor spectrum. The preceding isomorphism and the published component transport theorem give the same property for the categorical scalar extension.

For `exists_finite_separable_components_of_isAffine`, use the canonical affine isomorphism `X ≅ Spec Γ(X, ⊤)`. The composite of its inverse with `f` is a spectrum map and remains locally of finite type. Apply the preceding theorem and transport its pullback through the affine source isomorphism. The resulting field `E` is finite dimensional over `K` and is an intermediate field of `SeparableClosure K`; its separability over `K` follows from that inclusion.

`affineSchemeComponentSplittingField` chooses this intermediate field from the proved existence result. Its specification theorems give finiteness and geometric irreducibility of every actual component of the categorical scalar extension of `f`. The construction assumes neither a splitting extension nor geometric irreducibility of descended components.

This affine comparison does not assemble a finite affine cover or prove the unrestricted splitting proposition. Those are downstream steps.
