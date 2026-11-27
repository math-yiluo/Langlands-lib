# Determinants on a quotient and on an orthogonal subspace

Module `Langlands.BaseChange.TwistedLocalDescent.PairingDeterminant`. Two linear-algebra facts
about determinants of operators on finite-dimensional vector spaces over a field `F`.

## Adjoint operators

`det_mapQ_eq_det_restrict_of_pairing`: let `β : V → V → F` be bilinear, `T, T'` operators on `V`
with `β (T x) y = β x (T' y)`, `W` a `T`-stable subspace and `W'` a `T'`-stable subspace such that
`β` vanishes on `W × W'`, an element of `W'` orthogonal to all of `V` is zero, and an element of
`V` orthogonal to all of `W'` lies in `W`. Then the determinant of the operator induced by `T` on
`V ⧸ W` equals the determinant of `T'` on `W'`.

Proof: `β` induces injective maps `Φ : W' → (V ⧸ W)^*` and `Ψ : V ⧸ W → W'^*`; comparing
dimensions, `Φ` is an isomorphism, and it intertwines `T'` on `W'` with the dual of the induced
operator on `V ⧸ W`. Conjugate determinants agree and a dual map has the same determinant
(`LinearMap.det_dualMap`).

## Three nested subspaces

`det_mapQ_eq_det_restrict_mul_det_mapQ`: for subspaces `D ≤ P` with `P = D ⊔ L` and
`D ∩ L = 0`, all stable under `T`, the determinant of `T` on `V ⧸ D` is the determinant of `T` on
`L` times the determinant of `T` on `V ⧸ P`. The image of `P` in `V ⧸ D` is `T`-stable;
`LinearMap.det_eq_det_mul_det` splits the determinant along it, the image is identified with `L`
(an isomorphism commuting with `T`), and the quotient of `V ⧸ D` by it with `V ⧸ P`.
