# First-column elimination for the diagonal Hermitian matrix model

This internal continuation of `HermitianRootOpposites` proves an explicit
first-column elimination step over an arbitrary field. It uses actual root
coordinates and matrix identities. It does not assert full generation.

`topIndex`, `middleIndex` and `bottomIndex` name the three kinds of block
indices. For any form-preserving matrix `M`, `preservesForm_entry` expresses
the form pairing of columns `i,j`:

    bar(M_bottom,i)*M_top,j
      - Σ k, w_k*bar(M_middle(k),i)*M_middle(k),j
      + bar(M_top,i)*M_bottom,j = gram(H)_i,j.

This entry identity holds over every commutative ring. In the field case,
write the first column as `(a,b,d)`, with `d≠0`.
`firstColumnParameter` is the actual parameter with vector
`x_k=bar(b_k/d)` and scalar `z=a/d`. The top-top form identity says that the
first column is isotropic. Dividing it by `bar(d)*d` proves
`z+bar(z)=Σ k,w_k*x_k*bar(x_k)`, so these coordinates lie in `Parameters H`.
The implemented proof factors the common denominator out of the finite sum
and then clears denominators in that scalar identity.

The first column of `M` equals `d` times the last column of the recovered
upper root matrix `U(x,z)`. Replacing each first-column entry by that
expression shows that `U(x,z)⁻¹*M` has first column `(0,0,d)`, by the
already proved inverse-matrix identity. Multiplying by `swapMatrix` moves
this to `(d,0,0)`. The elimination theorem specifies every first-column
entry. Its general-linear version states the same formula using the actual
root embedding and `swapElement`.

Neither nondegeneracy nor anisotropy of the middle form is needed. The
input can be any form-preserving matrix with nonzero bottom-top entry;
only the final version assumes matrix invertibility. No determinant-one,
characteristic or nonidentity-involution hypothesis is used. Coefficient
and finite middle-index universes remain independent.

The result is derived directly from the existing coordinate model. Further
reduction of a matrix with top-axis first column requires handling its
middle Levi block and remains a separate generation obligation.
