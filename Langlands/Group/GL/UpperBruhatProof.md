# Upper triangular Bruhat factorization

Authors: Worker 308 (factor lifting and rank induction), with Worker 330
(the imported ordered pivot-isolation proof).

`Langlands.GeneralLinear.fieldUpperBruhatFactorizationTheorem.{u}` proves the
published closed proposition
`Langlands.GeneralLinear.FieldUpperBruhatFactorizationTheorem.{u}` from
`Langlands.Group.GL.UpperBruhatStatement`. For every field `K : Type u`,
every natural rank `n`, and every `g : Langlands.GeneralLinear n K`, it
provides actual invertible upper triangular matrices `a`, `b` and an actual
permutation `w : Equiv.Perm (Fin n)` satisfying
`g = a * permutation n K w * b`. Rank zero is included. The final theorem has
no pivot-isolation, matrix-reduction, or factorization hypothesis.

## Lifting across an isolated pivot

The proof imports the published ordered insertion API from
`Langlands.Group.GL.UpperBruhatEmbedding`. Its operation `Bruhat.insert p`
adds an isolated unit coordinate at `p` and retains the original matrix on the
increasing complementary coordinates `p.succAbove`. This operation preserves
upper triangularity.

Given smaller factors `a`, `b` and permutation `w`, `Bruhat.lifted_entries`
studies the product

```text
insert (Fin.last n) a * permutation (n + 1) K (extendPerm p w) * insert p b.
```

The extended permutation sends `p` to the last row and sends `p.succAbove j`
to `(w j).castSucc`, consistently with the convention that a permutation
matrix sends `e_j` to `e_(w j)`. Splitting the product sum into `p` and its
complement shows that the last row is the unit row supported at `p`, the
pivot column is zero above that row, and the complementary minor is
`a * permutation n K w * b`.

`Bruhat.factor_of_isolated_pivot` applies these entry formulas and matrix
extensionality to identify this lifted product with any matrix having the
specified isolated pivot and minor. The inserted factors remain upper
triangular. The lifting lemmas work over every commutative ring; the final
induction uses fields.

## Rank induction and closed theorem

The helper `fieldUpperBruhatFactorization_of_pivot` proves the rank induction
from the published proposition `FieldUpperBruhatPivotTheorem`. In rank zero,
the identity factors and identity permutation suffice, and matrix equality
is vacuous on `Fin 0`.

At rank `n + 1`, pivot isolation supplies upper triangular units `L`, `R`,
a column `p`, and an actual invertible minor `h` of `L * g * R`, with exactly
the normalized row and column needed by the lifting lemma. The induction
hypothesis factors `h`. Lifting that factorization gives
`L * g * R = A * permutation (n + 1) K W * B`. Multiplication by the inverse
elimination factors recovers

```text
g = (L⁻¹ * A) * permutation (n + 1) K W * (B * R⁻¹).
```

Closure under inversion and multiplication in the published
`upperTriangularSubgroup` proves both outer factors upper triangular. All
these witnesses are matrix units, so invertibility is retained throughout.

Finally, `fieldUpperBruhatFactorizationTheorem` applies the induction helper
to the independently published closed proof
`fieldUpperBruhatPivotTheorem` from `Langlands.Group.GL.UpperBruhatPivotProof`.
That proof constructs the least nonzero last-row pivot and the ordered minor;
it supplies the helper's only additional hypothesis. The final declaration
therefore has exactly the original closed proposition as its type, with all
field universes and natural ranks retained.

## Provenance and scope

This is an internal algebraic proof of the project's published general-field
factorization interface, using its ordered insertion and pivot-isolation
prerequisites. The implemented proof is the last-row pivot induction described
above; no external proof or literature statement is claimed. All imported
Lean/Markdown pairs remain unchanged. The separate applications to parabolic
double cosets and p-adic representatives, and any uniqueness assertion, are
outside this module.
