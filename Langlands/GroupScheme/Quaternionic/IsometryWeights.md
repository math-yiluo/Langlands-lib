# Central weights of matrix isometries and isotropic subspaces

Author: Worker 118.

This internal module supplies the division-algebra linear algebra for the
split-rank upper bound. It works over any division algebra `D` with a first-kind
involution `σ` over a field `K`, in arbitrary universes and characteristics.
The Gram matrix and matrix family need not be invertible or antihermitian;
the theorems assume precisely the displayed isometry equations.

The row-vector action transforms the Gram matrix by
`H ↦ A H ᵗA^σ`. The proof expresses `sesqForm` as a dot product and applies
matrix associativity, with the involution reversing the factors of a row
matrix product. Thus `A H ᵗA^σ = H` implies preservation of the form.

Since `σ` fixes `K`, the form is `K`-linear in both variables. If isometry
eigenvectors have central eigenvalues `a,b ∈ K`, their pairing is annihilated
by `a*b - 1`; it vanishes whenever `a*b ≠ 1`.

`commonWeightSpace A χ` is the left `D`-subspace of row vectors satisfying
`x A(t) = χ(t) x` for every member `t` of an arbitrary indexing type.
The functions `χ` take values in `K`; no group structure, character property,
or scheme action is assumed by this definition. Centrality of the scalar
action makes this set a `D`-subspace.

For a family of isometries, the module proves:

- Two common weight spaces pair trivially if some family member has
  nonreciprocal eigenvalues on them.
- A common weight space is totally isotropic if some member acts with
  eigenvalue whose square differs from one.
- Two such spaces have a totally isotropic sum when their mutual product
  weight is also separated from one. The three separating members may
  be different.
- Distinct weight functions have disjoint common eigenspaces.
- If both spaces are nonzero, the sum has dimension at least two, hence
  the Witt index is at least two.

The last conclusion uses `FormLemmas.finrank_le_wittIndex` and the dimension
formula for the sum and intersection of two subspaces. It is the elementary
obstruction needed when the Witt index is one.

The provenance is internal, by expansion of the published form definition
and finite-dimensional linear algebra. Constructing the weight functions
from an actual split-torus subgroup, separating their values, and proving
that a faithful split torus of dimension at least two supplies two such
nonzero weight spaces remain separate obligations. This module alone
does not prove a split-rank bound.
