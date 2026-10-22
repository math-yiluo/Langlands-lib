# Finite tensor actions and external tensor products

Author: Worker 23.

This is an intrinsic construction from Mathlib's `PiTensorProduct` universal
property and the project's existing smoothness predicate. A family of actual
linear representations of a group acts factor by factor on the actual indexed
tensor module. Mathlib's `map_one` and `map_mul` prove the action laws. Tensoring
actual intertwining maps gives an intertwiner; identity and composition follow
from the corresponding linear tensor-map laws.

If the index type is finite and every factor representation is smooth, a pure
tensor is fixed by the intersection of finitely many open stabilizers. Scaled
pure tensors span the tensor product, and smooth vectors form a submodule.
This proves smoothness of the full tensor action without putting a topology
on any module or assuming finite dimensionality.

For a family of groups, each factor action is pulled back along the actual
coordinate homomorphism. The resulting tensor action is the external tensor
product on the actual product group. The smoothness proof uses continuous
coordinate evaluation with the product topology. Both constructions package
their actual actions in the published canonical `Langlands.SmoothRep`.
The external tensor product of factor intertwiners is constructed with
identity and composition laws; `externalFunctor` bundles these maps as a
functor from the product of the canonical smooth categories to the canonical
smooth category of the product group.

The coefficient ring is any commutative ring. The coefficient, index, group
and factor-module universes are independent. The indexed tensor module lives
in `Type (max uR uI uV)`; the product group lives in `Type (max uI uG)`.
There is no resizing assumption. For complex coefficients and the finite
block index `Fin B.length`, the tensor carrier stays in the factor carrier
universe. Finiteness of the index is used only in smoothness and bundled smooth
objects; the algebraic maps are defined for arbitrary indices.

The Library's `Langlands.RestrictedTensor` modules construct a different
object: Flath's algebraic restricted tensor product over a field. It is a
direct limit of finite stages with prescribed reference vectors, acted on by
the cofinite restricted product. The present module is the finite tensor
product itself. It works over any commutative ring and needs no reference
vectors. It adds the smoothness proof, the bundled smooth objects and the
external tensor functor.

Provenance is internal, derived from the tensor universal property. The pinned
Mathlib source `Mathlib/LinearAlgebra/PiTensorProduct/Basic.lean`, commit
`5ed2965256430c3649e86755f9576b54eca72435`, supplies `tprod`,
`induction_on`, `map`, `map_tprod`, `map_id` and `map_comp`/`map_mul`.
The existing project pullback and smooth-submodule theorems provide precisely
the smoothness steps described above. This construction supplies the actual
tensor module needed for block-Levi representations. It makes no claim of
irreducibility, admissibility, exactness or classification for that module.

The paired module compiles with the pinned Lean 4.34.0 environment. Native
interface checks also exercise independent carrier universes, the categorical
functor, and the actual block Levi specialization alongside the published
induction and contragredient modules. Compilation is not mathematical
acceptance; independent semantic review and publication are required.
