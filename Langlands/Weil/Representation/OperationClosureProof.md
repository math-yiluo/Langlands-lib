# Closure of finite-dimensional complex representation properties

Worker 62 authored this proof pair.

The closing theorem `Langlands.Weil.representationOperationClosure` proves the
entire published proposition `Langlands.Weil.RepresentationOperationClosure`
from `Langlands.Weil.Representation.Operations`. It retains the independent
group and carrier universes, the topological-group hypotheses, the arbitrary
subgroup `I`, and the two finite-dimensional complex representations. The
topologies on all endomorphism spaces are exactly the target's
`moduleTopology` topologies for the usual topology on the complex numbers.

## Dual representations

The component lemmas live in `Langlands.Weil.OperationClosure`.
`annihilator` sends an invariant subspace to its annihilator in the
contragredient representation: applying the dual action evaluates a functional
on the original action at the inverse group element. Invariance of the original
subspace therefore proves invariance of its annihilator.
`coannihilator` reverses this construction. Its invariance follows by applying
the dual action at the inverse group element and simplifying the double inverse.

`annihilatorOrderIso` combines these constructions into an order isomorphism
from the invariant-subspace lattice to the order dual of the contragredient's
invariant-subspace lattice. The inverse laws use Mathlib's double-annihilator
and double-coannihilator results. Finite dimensionality supplies the reflexivity
needed on the dual side. `irreducible_dual_iff` transports `IsSimpleOrder`;
`semisimple_dual_iff` transports the complemented-lattice property. These are
Mathlib's definitions of the two representation properties.

`recoverTranspose` is the linear map that transposes an endomorphism of the
dual and conjugates the resulting bidual endomorphism through
`Module.evalEquiv`. `recoverTranspose_transpose` proves that this recovers the
original endomorphism. Consequently transpose is injective, and
`dual_eq_one_iff` identifies the kernels of a representation and its dual.
The inverse in the contragredient formula causes no change to the kernel
because a subgroup is closed under inversion.

For finite images, the dual's image is contained in the transpose of the
original finite image. Conversely the original image is contained in the
image of the dual's finite image under `recoverTranspose`, using inversion
on the group. This gives `finite_range_dual_iff`.

For continuity, transpose and `recoverTranspose` are linear maps between
spaces with their complex module topologies, hence continuous.
Composing with the continuous inverse on the group proves both directions
of `continuous_dual_iff`.

## Products, tensor products, and twists

`continuous_prod` composes the continuous pair of action maps with
`LinearMap.prodMapAlgHom`, regarded as a linear map.
`continuous_tensor` uses `TensorProduct.mapBilinear` and Mathlib's continuity
theorem for a bilinear map with a finite module on its left. It then composes
with the pair of action maps. The helper gives that pairing explicitly to
the elaborator. `continuous_twist` composes the unit-valued character with
the continuous map taking its complex value, then uses continuous scalar
multiplication on the endomorphism space.

`finite_range₂` bounds the range of a pointwise binary operation by the
binary image of the two finite ranges. It gives `finite_range_prod_tensor`
and `finite_range_twist`. These arguments apply to the whole group and,
by restriction, to `I`.

`isOpen_ker_of_common_kernel` proves openness of a homomorphism kernel
containing the intersection of two open kernels, using
`Subgroup.isOpen_mono`. The pointwise lemmas `prod_eq_one`, `tensor_eq_one`,
and `twist_eq_one` supply the required containments. The dual kernel equality
gives the open-kernel equivalence directly. The same pointwise identities
prove the unramifiedness clauses. When a character is trivial on `I`,
its scalar action on every element of `I` is the identity, giving the stated
twist equivalence there.

For irreducibility and semisimplicity under twists, the proof imports the
published `Langlands.twistSubrepresentationOrderIso`. This is the
order isomorphism that keeps the underlying invariant submodule and changes
only the stability proof. Transporting simplicity and complements gives
`irreducible_twist_iff` and `semisimple_twist_iff`.

The closing theorem assembles every clause in the order of the published
target, including its character-first hypotheses in the twist kernel and
finite-image clauses. No nonzero-rank assumption is used. The subgroup need
not be open, normal, or compact, and the group need not be finite.
Continuity of the character is used only for continuity of the twist;
the algebraic twist clauses impose no continuity hypothesis.

## Provenance and verification boundary

This is an internal proof of an existing published statement. Its mathematical
source scope remains the paired Markdown of
`Langlands.Weil.Representation.Operations`; the proof route is the explicit
linear-algebra and topology argument above.
The other project import is
`Langlands.Representation.Twist.SubquotientDefinitions`, which itself uses
the published scalar-twist definitions. These sources and their paired
Markdown were read and matched byte-for-byte with the current Library at
commit `30ceb5a0d89d8094c1663fc19f35416519b9a125`.

The principal Mathlib interfaces used are dual annihilators and bidual
evaluation in `Mathlib.LinearAlgebra.Dual`, the product and tensor maps,
the representation invariant-subspace lattice, module-topology continuity,
finite set images, and openness of a subgroup containing an open subgroup.
The pinned environment uses Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

The proof contains no project axiom or placeholder. Compilation through the project Lean service is a
development check. Independent Lake validation, exact-target inspection,
semantic review, and publication are recorded separately by the project.
