# Constructing regular module actions from universal affine coefficients

Let `R` be a commutative ring, `H` an affine group scheme over `Spec R`, and
`M` an arbitrary `R`-module. This internal construction turns universal linear
coefficient data into an actual natural module representation of `H`.
Neither `H` nor `M` is assumed flat, smooth, finite or projective.

A linear map `c : M → coordinateAlgebra H ⊗[R] M` determines
`universalCoefficientAction`: specialize its coefficients at a supplied actual
point `h ∈ H(A)`, then extend the resulting `R`-linear map `M → A ⊗[R] M`
to an `A`-linear endomorphism of `A ⊗[R] M`. Its pure-tensor formula is
`a ⊗ m ↦ a • (pointSpecialization(h) ⊗ id)(c(m))`.
`modulePointMap_smul` proves semilinearity for the full test-algebra scalar
action, and tensor induction gives naturality of these endomorphisms under
every morphism of affine test algebras.

`UniversalModuleAction` bundles this linear map together with two explicit
conditions. For every `m ∈ M`, the endomorphism at the identity point over
`R` fixes `1 ⊗ m`. At the pair of independent generic points of `H`, the
endomorphism for their product equals the successive endomorphisms on
`1 ⊗ m`. These are supplied hypotheses of the structure, not assertions
about an arbitrary linear map.

`action_one` specializes the base identity condition to every algebra and
extends it by linearity. `action_mul` specializes the generic-pair condition
to any pair and likewise extends it by linearity. They prove the identity
and multiplication laws as equalities of actual linear endomorphisms on all
affine tests. `endAction` packages the resulting monoid homomorphism.
The inverse source point gives an inverse endomorphism, so `linearAction`
constructs linear automorphisms. Finally `moduleRepresentation` packages this
pointwise action and the previously proved naturality in the existing
`ModuleRepresentation` interface.

The provenance is internal: this is affine universal-point specialization,
scalar extension of a linear map, and the elementary inverse law for a group
action. It does not construct these universal data from a square-zero kernel,
prove cohomology vanishing, or prove infinitesimal homomorphism lifting.
