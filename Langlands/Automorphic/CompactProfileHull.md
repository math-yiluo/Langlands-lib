# Common right-stable bounds for compact profiles

For a subgroup `H` of a group `G`, the profile of `f` at `x` is the function
`h ↦ f (x * h)` on `H`. Fix a finite-dimensional space `E` of functions on
`H` and take the span of the profiles of all functions having every profile
in `E`. This span is finite-dimensional and stable under left translation,
since left translation of a profile moves its base point `x`.

`rightCompactProfileHull` spans the right translates of that profile span.
A right translate of `v` in the profile span is the matrix coefficient
`h ↦ ℓ_k(L_h v)`, where `L_h v` is left pullback by `h` and `ℓ_k` is
evaluation at `k`. All these coefficients lie in the image of the tensor
product of the profile span with its dual. Finiteness of the image gives a
common finite-dimensional hull. The original profiles belong to it by
translation by the identity. Associativity makes it stable under right
translation.

This is the algebraic coefficient argument behind the fixed compact-type
convention of Borel–Jacquet, *Automorphic forms and automorphic
representations* (1979), §1.5 (1)–(2), printed p. 190, PDF p. 185 of
`borel-jacquet-1979-automorphic`, SHA-256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
The argument works for all subgroups and requires no topology on `G`.
