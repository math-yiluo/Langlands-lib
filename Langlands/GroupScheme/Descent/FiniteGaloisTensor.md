# The actual finite Galois tensor decomposition

This internal construction uses Mathlib's linear independence of distinct
multiplicative characters and finite Galois automorphism count. It has arbitrary
field universe `u` and no characteristic, perfectness or infinitude restriction.

The canonical `L`-algebra map `galoisTensorHom` sends `a ⊗ b` to the tuple
`σ ↦ a * σ(b)`. For a finite extension, linear independence of automorphisms
as functions and `span_flip_eq_top_iff_linearIndependent` show that the evaluation
tuples `σ ↦ σ(b)` span the whole product. These tuples are images of `1 ⊗ b`,
so the canonical map is surjective. When the extension is Galois, the two
`L`-vector spaces have the same dimension: the tensor product has dimension
`[L : k]` and the product has dimension the number of automorphisms. Mathlib's
finite Galois automorphism count identifies these numbers. Hence the map is
bijective and defines the actual algebra equivalence `galoisTensorEquiv`.

`galoisIndexEquiv` enumerates the automorphisms by `Fin [L : k]`.
`finiteGaloisTensorEquiv` reindexes the same equivalence by that small type,
as required by `TensorComponents`. Its pure tensor formula is proved exactly.
`finiteGaloisComponent` applies the existing tensor-to-spectrum construction
to this proved algebra equivalence. The induced map from the finite coproduct
of copies of `Spec L` to the actual double overlap is an isomorphism.
The first projection on component `i` is the identity, and the second is exactly
`Spec (galoisIndexEquiv k L i)`. Thus the algebra equivalence and its formula
are constructed here, rather than supplied as hypotheses. Source transport and
closed subgroup effective descent remain separate constructions.
