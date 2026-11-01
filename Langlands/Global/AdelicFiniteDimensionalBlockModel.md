# Actual finite-dimensional models for adelic block induction

This is an internal construction from the published actual block tensor action,
actual adelic parabolic section spaces, and pinned Mathlib finite-dimensional
linear algebra. It constructs a normed coefficient model for every family of
finite-dimensional complex block representations and the actual continuous
section maps induced by algebraic families of block intertwiners.

## Inputs and coefficient space

Let `F` be any number field, `n` any natural number and `B : BlockShape n`
an ordered positive block shape. Let `V i` be complex modules and let
`σ i` be representations of the actual group `AdelicGL F (B.size i)`.
The field and the coefficient families have independent universes. No topology
on any `V i` and no continuity of `σ i` is required.

`Index B V` is the finite type
`∀ i : Fin B.length, Fin (Module.finrank ℂ (V i))`, in `Type 0`.
`Model B V` is the actual complex function space `Index B V → ℂ`,
with its usual finite-product sup norm and complex normed-space structure.
`model_finrank` computes its dimension as the product of the factor finranks.
This dimension formula concerns the defined coordinate space and does not
require finite-dimensionality of the original factors.

For finite-dimensional factors, `tensorEquiv` is the complex linear equivalence
from the actual algebraic `PiTensorProduct ℂ V` to `Model B V`. It is
`equivFun` for `Basis.piTensorProduct` of `Module.finBasis ℂ (V i)`.
Thus a genuine tensor basis constructs the model; an arbitrary coefficient
space with a postulated tensor equivalence is not an input. The choices of
factor bases are noncanonical. `tensorEquiv_tprod` proves that the coordinate
at `p` of a pure tensor `⊗ᵢ v i` is the product of the coordinates of `v i`
at `p i`.

## Actual representation and section carrier

`coefficientAction` transports the published actual representation
`B.blockTensor σ` of the full adelic block Levi through `tensorEquiv`.
`coefficientEquiv` is an equivalence of these genuine representations. The
action on a model vector `v` is
`tensorEquiv (blockTensor σ m (tensorEquiv.symm v))`.
`coefficientAction_tprod` proves the factorwise coordinate formula: apply
`σ i (m i)` in each factor, then multiply the resulting basis coordinates.

`CompactOpenSections` is the published compact-open carrier of actual
half-twisted parabolic sections with this constructed coefficient
representation. Its sections have the existing parabolic covariance, one
common open finite stabilizer and real-smooth infinite slices in the actual
mixed archimedean matrix coordinates. Its topology is the one induced by its
faithful realization in continuous functions on the full adelic group.
`rightAction` is the actual full adelic right translation on this carrier.
The finite-dimensional coefficient model does not assert that the section
space is finite-dimensional.

## Algebraic block maps give continuous section maps

Let `W i` and `X i` be further finite-dimensional complex coefficient families,
with independent universes, carrying block representations `τ i` and `υ i`.
A family `T i : (σ i).IntertwiningMap (τ i)` needs only its algebraic
intertwining property. `coefficientMap` transports the genuine tensor map
`FiniteTensor.externalMap T` between the constructed models. Its value on a
model vector is
`tensorEquiv W (externalMap T (tensorEquiv V).symm v)`.
`coefficientMap_tprod` gives the product-coordinate formula after applying
each actual `T i`.

`continuous_coefficientMap` proves continuity by finite-dimensionality of the
constructed normed source. It imposes no topological premise on `T i` or
the original factors. `coefficientMap_id` and `coefficientMap_comp` prove the
identity and composition laws using the corresponding actual tensor-map laws
and cancellation of the coordinate equivalences.

`mapCLM` applies the published continuous coefficient-postcomposition
construction to this actual continuous intertwiner. It is a continuous complex
linear map of the compact-open section spaces. `mapCLM_apply` identifies its
value at every full adelic group element with transported tensor
postcomposition of the old value. `mapCLM_id` and `mapCLM_comp` inherit the
identity and composition laws, and `mapCLM_rightAction` proves equivariance
for the full adelic right actions.

## Whole-block central characters

Suppose each factor has an actual Hecke character `c i`, together with the
scalar-action identity
`σ i (AdelicGL.scalar F (B.size i) z) v = (c i).onIdeles z • v`
for every idele `z` and factor vector `v`. These identities are explicit
hypotheses. `coefficientAction_scalar` proves that common scalar ideles act on
the constructed model through
`AdelicBlockFactorInduction.centralCharacter F B c`, the unweighted product
of the whole-block central characters.
`rightAction_scalar` proves the same product central law on the actual
compact-open sections. The proof first uses the published algebraic tensor
central identity, then linearity and inverse cancellation; the published
generic induced scalar law transfers it to sections.

## Provenance and scope

This pair derives its constructions from
`Langlands.Global.AdelicBlockFactorInduction`,
`Langlands.Global.AdelicParabolicInductionTopology` and the generic actual
representation transport in
`Langlands.Representation.Smooth.SmallRealizationProof`.
The coordinate equivalence and formula use pinned Mathlib
`LinearAlgebra/PiTensorProduct/Basis` and `Module.finBasis`; automatic
continuity uses
`Topology/Algebra/Module/FiniteDimension`.
These are internal constructions with no new original-literature
identification.

Every rank and block shape is retained, including the empty shape in rank zero
and zero-dimensional factor modules. The latter can give an empty coordinate
index. Empty products use the ordinary Mathlib conventions. There is no claim
of a canonical norm on arbitrary algebraic tensors, a completed tensor product,
nonzero sections, a Haar-modulus identification, a unitary completion or
automorphic occurrence. These remain separate construction or theorem
obligations where needed.
