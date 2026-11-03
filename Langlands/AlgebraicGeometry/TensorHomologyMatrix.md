# Degree-zero tensor homology in finite matrix coordinates

Let `R : CommRingCat.{u}` and let `K` be an integer cochain complex of
`R`-modules. Assume the actual incoming differential `K.d (-1) 0` is zero,
and choose finite free coordinate isomorphisms
`e₀ : K.X 0 ≃ₗ[R] (Fin n → R)` and
`e₁ : K.X 1 ≃ₗ[R] (Fin m → R)`. Write `a` for
`FiniteLinearEquations.TensorKernel.matrix (K.d 0 1).hom e₀ e₁`.

`TensorSections.homologyZeroSolutionsPresheafIso K h e₀ e₁` is a natural
isomorphism from `TensorSections.homologyPresheaf K 0` to
`FiniteLinearEquations.solutionsPresheaf a` on the full scheme slice over
`Spec R`. At every test scheme `T`, it identifies the explicitly lifted
`H⁰(Γ(T,𝒪_T) ⊗[R] K)` with the explicitly lifted solutions of `a` in
`Γ(T,𝒪_T)`. The coefficient algebra and all restriction maps come from the
actual structure morphism of `T`. Nonaffine test schemes and every morphism
in the slice are included.

The implemented construction first uses the two kernel universal properties
to identify the cycles of a module complex with the concrete linear kernel
of `K.d 0 1`. Since the incoming differential is zero, Mathlib's
`ShortComplex.asIsoHomologyπ` makes the class map from cycles to homology
an isomorphism. `homologyZeroLinearKernelIso` composes its inverse with the
concrete-kernel identification. Its naturality is proved after precomposing
with the epimorphism from cycles to homology and then using naturality of
that class map and of the cycle inclusion.

Tensoring preserves the zero incoming differential.
`tensorHomologyZeroKernelEquiv` therefore identifies ordinary tensor
homology with the actual kernel of `id_A ⊗ K.d 0 1` for every coefficient
module `A : ModuleCat R`. Its proved naturality uses the actual map
`q ⊗ id` for every `R`-linear coefficient map `q`. Composing with
`TensorKernel.kernelEquiv` gives `tensorHomologySolutionsEquiv` for
commutative coefficient algebras; its naturality follows from the two
proved naturality identities. Applying these equivalences to global
sections and preserving `ULift.{u+1}` gives the displayed presheaf
isomorphism. `homologyZero_hasModel` packages this same explicit matrix as
`FiniteLinearEquations.HasModel (TensorSections.homologyPresheaf K 0)`.

This is an internal construction from Mathlib's module-kernel and homology
APIs and the `TensorSectionsHomology`, `TensorLinearKernel`, and
`FiniteLinearModels` constructions. No flatness of the coefficient module
or algebra, no noetherian hypothesis, no boundedness of `K`, and no
positive-rank hypothesis is used. The zero incoming differential and both
finite free coordinate systems are inputs; their local existence and a
comparison with ordinary geometric module Hom remain separate obligations.
In particular, this construction does not prove
`NoetherianHomFiniteLinearModelsStatement` or its unproved perfect-complex
comparison.
