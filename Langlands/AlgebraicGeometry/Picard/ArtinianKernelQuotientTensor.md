# Actual affine tensor comparison for an elementary kernel quotient

This is an internal construction from `ElementaryKernelSubspaceQuotient`,
`ArtinianKernelQuotient`, and `ArtinianPicardKernelTensor`. It proves compatibility
of their actual maps; it introduces no new external mathematical assertion.

Let `k` be a commutative ring, `K` a field with its specified `k`-algebra
structure, and `f : X → Spec k` an actual scheme morphism. All objects use
an arbitrary common universe `u`. Let `q : A → B` be an elementary
surjection of augmented Artinian tests. Its unchanged kernel `I = Kernel q`
has the previously descended `K`-action, and `W` is any `K`-subspace of `I`.
Write `Q` for the actual quotient test constructed from `W`, `π : A → Q`
for the projection, `r : Q → B` for the reduction, and `φ` for the underlying
ring map of `π`. Put `h : X_Q → X_A` for the actual induced scheme morphism.
Zero and whole-kernel subspaces are allowed. There is no chosen section of
the augmentation `A → K` or a `K`-algebra structure on `A`.

For an open `U` in `X_A`, write `V = h⁻¹(U)`. The lemma
`quotient_testSectionHom` states that the actual structure map on sections
carries an element coming from `a ∈ A` to the element coming from `φ(a) ∈ Q`.
The private proof first establishes this statement for an arbitrary commutative
square of schemes over spectra, using the naturality of `Γ(Spec R) ≅ R`.
It then applies the actual quotient projection square.

`FibreSections f C U` abbreviates `K ⊗_C Γ(X_C,U)`, using the specified
augmentation of the test `C`. `quotientFibreRingHom` is the tensor ring map
induced by `φ`, the identity of `K`, and the actual section map `h.app U`.
The augmentation triangle and `quotient_testSectionHom` provide its two
compatibility equations. `quotientFibreMap` equips the same ring map with its
`K`-algebra-map structure. Its pure-tensor formula is

`c ⊗ s ↦ c ⊗ h.app U s`.

`quotientTensorMap` tensors this map with the actual `K`-linear map
`kernelLinearMap q W : I → Kernel r` induced by the ordinary quotient.
It is a `K`-linear map

`FibreSections f A U ⊗_K I → FibreSections f Q V ⊗_K Kernel r`.

The corresponding pure-tensor lemma states that
`(c ⊗ s) ⊗ x` maps to `(c ⊗ h.app U s) ⊗ kernelLinearMap q W x`.
These definitions and formulas require no flatness or properness of `f`.
The lemma `quotient_kernel_section` records the compatible actual section-ring
formula for the coefficient `c • x`; it uses linearity of `kernelLinearMap`
for the existing residue-field actions.

Assume now that `f` is flat. For an affine open `U`, and an explicit proof
that `V` is affine, `affineKernelEquiv_quotient` identifies the following two
maps on every tensor `t`:

- apply `affineKernelEquiv` for `q` to obtain an actual ideal section, then
  apply the actual ideal quotient map `idealMap f q W`;
- apply `quotientTensorMap`, then apply `affineKernelEquiv` for `r` on `V`.

The proof of affineness of `V` is an explicit parameter. Such a proof is
available because `π` is surjective, so `h` is a closed immersion and hence
affine. The theorem does not require properness. The equivalences and ideal
maps in this statement are the preexisting actual constructions; none is
defined by conjugating an arbitrary coordinate map.

The implemented proof first proves the equality on pure tensors. Its
underlying section value follows from the pure formula for
`affineKernelEquiv`, the actual scalar naturality above, and `K`-linearity
of the actual kernel quotient. For arbitrary tensors, private additive maps
compare the underlying structure-ring values. A generic two-stage tensor
induction proves equality of these additive maps from their pure values.
Finally, `idealMap_app` and subtype extensionality give the equality of ideal
sections. Naming the value maps avoids reducing the transported ideal map
inside tensor induction. `affineKernelEquiv_quotient_tmul` also records the
pure-tensor equality directly.

This unit proves the affine tensor compatibility for the actual quotient.
Compatibility after identifying fibre tensor rings with actual sections on
`X_K`, global cohomology tensor naturality, obstruction-class naturality,
the complete local hull, algebraization, and the requested smooth Picard atlas
remain separate obligations.
