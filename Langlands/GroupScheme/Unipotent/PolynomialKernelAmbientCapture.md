# Pointed affine-line capture by ambient polynomial-kernel factors

Authors: Worker 864, with Worker 1561 contributing the ambient capture
interface and Worker 1371 contributing the generic pointed-map capture adapter.

This internal construction concerns a separated additive polynomial row
`f : Fin n → k[X]` over an arbitrary field in universe `u`. All group schemes,
pullbacks, kernels and maps from the affine line are actual schemes. There is
no smoothness assumption on the polynomial kernels. The conclusion applies
also to finite and imperfect fields.

The imported `baseChangeTensorIso b V W` compares the pullback of `V ⊗ W` along an arbitrary
scheme map `b : S' ⟶ S` with the product of the pulled-back group schemes.
It is the inverse of the monoidal product comparison for scheme pullback.
The projection identities `baseChangeTensorIso_inv_fst` and
`baseChangeTensorIso_inv_snd` identify the two changed projections.
`baseChangeTensorIso_section` identifies the first-factor inclusion
`lift id 0` with the pullback of the original first-factor inclusion. Here
zero is the zero group homomorphism; its underlying scheme map takes every
point to the identity.

Suppose an actual ambient isomorphism `e : V_n ≅ V_r ⊗ V_m` satisfies
`e.hom ≫ snd ≫ polynomialRow g hg = polynomialRow f hf`.
The previously constructed `polynomialKernelAmbientKernelIso` restricts this
isomorphism to `kernel(row f) ≅ V_r ⊗ kernel(row g)`.
For any map `b : S' ⟶ Spec k`,
`polynomialKernelAmbientBaseChangeIso` combines the canonical kernel
base-change comparison, the pullback of this kernel isomorphism, and the
product comparison. Its source is the full kernel of the pulled-back row;
its target is the product of the pulled-back `V_r` and pulled-back residual
kernel. `polynomialKernelAmbientBaseChangeIso_section_ι` proves that its
first-factor inclusion, followed by the actual kernel inclusion, equals the
pullback of `polynomialKernelAmbientSection e`. This identity follows from
the inclusion identity for kernel base change, the product-section identity,
and the original compatible kernel-section identity.

`mem_range_baseChange_polynomialKernelAmbientSection` applies to any scheme
map `c : Spec K ⟶ Spec k` between fields, provided the actual pullback of the
residual kernel has only constant affine-line maps over `K`. A map from the
affine line over `K` into the pulled-back ambient vector group which takes
zero to the identity and is annihilated by the changed row factors through
the pulled-back ambient section. Indeed, annihilation means membership in
the full kernel range. The product isomorphism and constancy of its second
factor capture all pointed maps in that kernel, by
`CapturesPointedAffineLineMaps.of_productIso`. Transport along the monic
kernel inclusion and the preceding section identity give the asserted
ambient factorization. Membership in `SubgroupFunctor.range` here means a
global factorization as a relative-scheme morphism; the factoring morphism
need not be a group homomorphism.

Finally, `exists_polynomialKernelAmbientCapture` supplies this data for every
nonzero row over `k`: an integer `r < n`, an actual closed subgroup inclusion
`s : V_r ⟶ V_n`, a retraction `q : V_n ⟶ V_r` with `s ≫ q = id`, and
`s ≫ row f = 0`. Every pointed affine-line map over the separable closure
annihilated by the actual changed row factors through the actual changed
`s`. The proof takes the existing ambient-factor decomposition with its
strict rank bound and separable-closure constancy of the residual kernel,
then applies the preceding capture theorem.

The provenance is internal: these are categorical consequences of the
existing compatible ambient factor, scheme-theoretic kernel base change,
monoidal scheme pullback and generic pointed affine-line capture. This unit
supplies the single-row capture step for an induction on closed subgroups of
vector groups. It does not carry out that general induction or prove the
full arbitrary-unipotent-group woundness criterion.
