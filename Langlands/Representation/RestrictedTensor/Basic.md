# Algebraic restricted tensor products and finite-stage embeddings

`Langlands.RestrictedTensor.Product K V E r` is the algebraic restricted tensor
product of the vector spaces `V i` over the field `K`, with prescribed nonzero
reference vectors outside the finite exceptional set `E`. It is an actual
Mathlib algebraic `DirectLimit` of finite `PiTensorProduct` spaces. The space and
its universal maps are constructed, rather than supplied as fields of a record.

The coefficient field, index type, and local carriers lie in independent
universes `uK`, `uI`, and `uV`. The resulting carrier lies in
`Type (max uK uI uV)`. The universal map allows a target in an independent
universe `uW`. No finite-dimensionality, topology, admissibility, or nontriviality
of the exceptional local factors is assumed.

## Source and precise correspondence

D. Flath, *Decomposition of representations into tensor products*, in
*Automorphic Forms, Representations and L-Functions*, Proc. Sympos. Pure Math.
33, part 1 (1979), pp. 179–183, defines the construction in §2, printed p. 180,
last two paragraphs. The finite sets `S` contain the exceptional set, and the
map from `S` to a finite superset adjoins the prescribed vectors at new indices.
The direct limit is spanned by elementary tensors. These are respectively
`Index E`, `transition`, `Product`, and `span_pure` in this implementation.

Registered original: `flath-1979-tensor-products`.
Retained file:
`C:/Central-Library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`.
SHA-256:
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
Printed pp. 180–181 are one-based PDF pp. 176–177. The complete five-page
article was read. The finite-stage splitting and contraction below are
implementation proofs of the construction's intrinsic embedding properties;
they are not separately attributed theorems of Flath.

Flath §2, p. 181, numbered (1) and Example 2 motivate the subsequent induced-map
and group-action contributions. This file does not yet implement those
contributions. The factorization and uniqueness theorems, the archimedean
`(g,K)` discussion in §3, and the Hilbert completion in §4 are distinct
mathematics and are not consequences claimed here.

## Construction and exported API

`Stage K V S` is `PiTensorProduct K (fun i : S => V i)`, with its standard
module structure. For a total family `e`, `extend e v` keeps the coordinates
of `v` on `S` and uses `e` elsewhere. `transitionMultilinear` proves this
extension is multilinear in the original coordinates, and `transition` is
its linear extension by `PiTensorProduct.lift`.

`transition_tprod` states the defining formula. `transition_self` and
`transition_comp` prove the identity and composition laws by equality on
elementary tensors. The proof of multilinearity uses a coordinate-update
identity, including arbitrary decidable-equality instances introduced by
Mathlib's multilinear-map definition.

`splitStage h` is a linear equivalence

```text
Stage K V T ≃ₗ[K]
  Stage K V S ⊗[K] (⨂[K] (i : {i : T // i.1 ∉ S}), V i.1)
```

for `h : S ⊆ T`. It is built from the explicit index equivalence `splitIndex`,
Mathlib's dependent tensor reindexing, and `PiTensorProduct.tmulEquivDep`.
`splitStage_tprod` gives its elementary formula. Its inverse is a genuine
linear equivalence, so the finite-stage separation and reassembly laws are
available from the `LinearEquiv` API. This is finite-stage splitting;
[Separation](Separation.md) constructs separation and reassembly for the full
restricted tensor product.

`retractStage h φ` contracts the complementary factors against linear
functionals. `retractStage_tprod` is the product-of-evaluations formula.
If each functional takes the new reference vector to one,
`retractStage_transition` proves the contraction is a left inverse.
For a nonzero vector in a vector space over a field,
Mathlib `Module.Projective.exists_dual_eq_one` supplies such a functional.
Consequently `transition_injective` requires nonzero reference vectors only
on `T \ S`. The field assumption is essential to this argument's generality;
no unsupported claim about injectivity over arbitrary rings is made.

`Index E` is the subtype of finite supersets of `E`. It is inhabited by `E`
and directed by union. `systemMap` has a proved `DirectedSystem` instance.
`Space K V E e` is its algebraic direct limit. The underlying generalized
construction allows an arbitrary total reference family; its injectivity
theorems explicitly require nonzero vectors outside `E`.

The canonical maps are `of K V E e S`. `of_transition` is compatibility with
transition maps. `of_eq_iff` characterizes equality of two representatives
by equality of their images in some common finite stage. `exists_of` says
every element has a finite-stage representative.

`lift` constructs a linear map from every compatible family of finite-stage
linear maps. `lift_of` is its evaluation rule; `hom_ext` proves uniqueness.
These use Mathlib `DirectLimit.Module.of`, `lift`, and the actual quotient
relation, with no choice of a purported tensor space.

`pure E e S v` is the elementary tensor represented by `v` at stage `S`.
`pure_extend` proves independence of enlarging this finite stage.
`induction` reduces a predicate to elementary tensors, addition, and scalar
multiplication. `span_pure` proves their linear span is the entire space.
`of_injective` proves all finite stages embed when `e i ≠ 0` outside `E`.

Finally `ReferenceVectors V E` takes `vector i hi : V i` and its nonzero
proof only for `hi : i ∉ E`. `ReferenceVectors.family` fills exceptional
coordinates with zero. These coordinates are never adjoined by the system,
since every stage contains `E`. `Product K V E r` specializes `Space` to
this total family. `reference_of_injective` supplies its finite-stage
embeddings with no additional hypotheses.

## Dependencies, verification, and remaining scope

There are no project mathematical dependencies. The exact environment is
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1: Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

The audited Mathlib APIs are `PiTensorProduct.Basic`, `Algebra.Colimit.DirectLimit`,
`LinearAlgebra.Dual.Lemmas`, and `TensorProduct.Map`. In particular
`PiTensorProduct.Finite` only supplies finite-generation instances and is
not used to impose restrictions on the local carriers. All construction
obligations stated in this file have Lean proofs.

This contribution is the core algebraic construction. Almost-everywhere
reference-preserving induced maps, changes of the exceptional set,
the genuine restricted-product representation, intertwiner compatibility, and
smoothness belong to separate modules in the same task. Coherent separation
in the full restricted tensor product is implemented in
[Separation](Separation.md). Compilation and
development inspection do not themselves establish independent acceptance
or current Library publication.
