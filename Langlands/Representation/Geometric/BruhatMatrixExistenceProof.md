# Inverse permutation representatives for p-adic parabolic double cosets

Author: Worker 6. The imported general-field factorization proof is by
Worker 308, using Worker 330's ordered pivot-isolation proof.

`Langlands.Geometric.padicBruhatMatrixExistence.{u}` proves exactly the
published proposition `Langlands.Geometric.PadicBruhatMatrixExistenceTheorem.{u}`
from `Langlands.Representation.Geometric.BruhatMatrixStatement`. It retains
every prime `p`, every actual `F : PadicField.{u} p`, every positive rank `n`,
every pair of ordered positive block shapes `B C : BlockShape n`, and every
`g : GeneralLinear n F.Carrier`. It produces an actual permutation whose
inverse permutation matrix has the same class as `g` in
`P_B \ GL_n(F) / P_C`. The theorem has no factorization or representative
existence hypothesis.

## Converting a triangular factorization

The helper `inverse_permutation_doubleCoset_of_upper_factorization` works over
every commutative ring and every natural rank. It starts with actual invertible
matrices `a`, `b`, a permutation `w`, the entrywise upper triangularity of
`a` and `b`, and the equality

```text
g = a * permutation n R w * b.
```

The published lemma `BlockShape.mem_parabolic_of_isUpperTriangular`, imported
from `Langlands.Group.GL.TriangularParabolic`, puts `a` in `B.parabolic R`
and `b` in `C.parabolic R`. Applying Mathlib's `DoubleCoset.eq` with these
two witnesses proves equality of the relevant double-coset classes.

The representative chosen for the target convention is the permutation `w⁻¹`.
The identity `permutation_inv` and double inversion give

```text
(permutation n R (w⁻¹))⁻¹ = permutation n R w.
```

Thus the displayed factorization supplies the equality demanded by
`DoubleCoset.eq`, with the left and right parabolics in exactly the stated order.

## Closed p-adic specialization

The final theorem imports
`Langlands.GeneralLinear.fieldUpperBruhatFactorizationTheorem` from
`Langlands.Group.GL.UpperBruhatProof` and applies it to `F.Carrier`, `n`, and `g`.
That closed theorem supplies actual invertible upper triangular factors and
an actual permutation. The proof passes these witnesses to the helper and
returns `w⁻¹`. The rank-positivity assumption is retained in the target even
though the imported factorization and the conversion work in every rank.

This is an internal deduction from the published general-field factorization,
triangular inclusion, permutation identities, and double-coset definitions.
The target's literature provenance remains documented in its unchanged
`BruhatMatrixStatement.md`; this module describes its own implemented proof.
It proves representative existence only. It asserts neither minimality nor
uniqueness nor the separate reflection of Weyl double-coset equality.
