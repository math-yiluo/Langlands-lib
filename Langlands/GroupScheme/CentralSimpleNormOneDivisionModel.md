# Division-algebra matrix models of actual norm-one groups

Author: Worker 165.

This internal derived unit uses Mathlib's Wedderburn--Artin theorem and the
published norm-one transport construction. It introduces no external
classification assertion. All fields and algebras lie in an arbitrary
common universe `u`. There is no restriction on the field characteristic.

In the namespace `Langlands.GroupScheme.CentralSimpleUnits`,
`DivisionMatrixPresentation K A` stores a positive matrix size, a
finite-dimensional central division `K`-algebra in `Type u`, and an actual
algebra equivalence from `A` to that matrix algebra. These are the only
fields; there is no rank, norm compatibility or group-classification field.
`divisionMatrixPresentation K A` constructs such a presentation under the
central-simple-algebra hypotheses.
`DivisionMatrixPresentation.normOneIso K A p` is the actual group-scheme
isomorphism induced by a presentation `p`.

`exists_matrix_division_model K A` applies to a field `K` and a
finite-dimensional central simple `K`-algebra `A`. Its conclusion provides a
positive natural number `m` (as `NeZero m`), a division ring `D : Type u`,
its `K`-algebra structure, finite dimensionality and centrality, an actual
algebra isomorphism `A ≃ₐ[K] Matrix (Fin m) (Fin m) D`, and an isomorphism
of the actual norm-one group schemes over `Spec K`.

The finite-dimensional algebra is Artinian.
`IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite` therefore gives
its matrix presentation over a finite-dimensional division algebra.
`Langlands.CentralSimple.isCentral_of_algEquiv_matrix` proves centrality
of that division algebra from centrality of `A` and the nonzero matrix
size. The group-scheme isomorphism is `normOneAlgEquivIso` applied to the
algebra isomorphism. Its construction preserves the actual reduced norm
on every commutative coefficient algebra and represents the natural
multiplicative equivalences of points on every test scheme. Thus the
result is an isomorphism of group schemes, with no supplied norm
compatibility or rational-point-only identification.

The remaining two theorems are explicitly conditional reductions.
`exists_binary_model_of_splitRank_one K A hrank hA` takes
`hrank : MatrixNormOneSplitRankStatement.{u}` and
`hA : splitRank (normOne K A) = 1`. Transport of split rank across the
constructed isomorphism and `hrank` give `(m - 1 : ℕ∞) = 1`. Injectivity
of the natural-number inclusion and positivity of `m` force `m = 2`.
The result is `normOne K A ≅ BinaryRoot.groupScheme K D` for some
finite-dimensional central division `K`-algebra `D`.

`exists_binary_model_of_normOne_presentation` also takes an actual
isomorphism `e : G ≅ normOne K A` and `splitRank G = 1`. It transports
the rank equality and composes the resulting group-scheme isomorphisms
to obtain `G ≅ BinaryRoot.groupScheme K D`, with the same division-algebra
properties. It imposes no affine, simply connected, almost-simple or
local-field hypothesis beyond the supplied norm-one presentation.

This unit does not prove the matrix-rank statement. It also does not
construct a central-simple-algebra presentation of an arbitrary inner
form of type A. Those inputs, the admissible-index enumeration, and the
other classical model identifications remain separate obligations of
the local rank-one classification.
