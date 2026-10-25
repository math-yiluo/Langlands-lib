# Cancelling trivial multiplicity spaces

This internal algebraic construction supports uniqueness of supplied restricted
tensor representations. It works over any field and for monoid representations,
with independent universes for the field, monoid, both local factors, and both
multiplicity spaces. There are no topological or finite-dimensional assumptions.

`slice ρ a` maps `x` to `x ⊗ a` and intertwines `ρ` with its tensor product with
the trivial action on the multiplicity space. `coefficient σ b j` takes the
`j`th coefficient in a basis of the second tensor factor. Its equivariance is
proved on pure tensors, where scalar linearity proves the identity.

`exists_coefficient_ne_zero` uses the injective basis-coordinate equivalence
from Mathlib to detect any nonzero tensor. `tmul_ne_zero` detects a tensor of
nonzero vectors by a nonzero basis coefficient of the second vector.

`nonempty_equiv_of_tensor_trivial` assumes both local representations irreducible,
the source multiplicity space nontrivial, and an equivariant equivalence between
their tensors with trivial multiplicity actions. Choose nonzero vectors in the
source local factor and multiplicity space. Their tensor and its image under
the equivalence are nonzero. Some target basis coefficient detects that image.
Composing the source slice, the equivalence, and this coefficient gives a
nonzero intertwiner between the local factors. Mathlib's
`Representation.IsIrreducible.bijective_or_eq_zero` makes it bijective, and
`IntertwiningMap.ofBijective` supplies the genuine representation equivalence.
The target multiplicity space need not separately be assumed nontrivial.

This is derived internal infrastructure, implementing the elementary algebraic
content of the isotypic-restriction argument used for factor uniqueness. It does
not prove restricted-product existence or invoke a version of Schur's lemma
requiring algebraic closure or finite dimension. The construction reuses
Mathlib's basis-coordinate tensor equivalence and irreducible-intertwiner lemmas.
