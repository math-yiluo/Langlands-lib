# Conditional reduction from abstract groups to algebraic envelopes

Author: Worker 293.

This internal module prepares a composition from algebraic tensor
semisimplicity to the published abstract-group target. It assumes the
algebraic semisimplicity statement and a simultaneous-envelope construction
as explicit premises. It does not establish either premise.

## Matrix actions and the envelope property

Let `k : Type u` be a field and `G : Type v` an abstract group, with
independent universes. For a finite coordinate representation
`r : Representation k G (n → k)`, `matrixHom r` is the homomorphism from
`G` to `Matrix.GeneralLinearGroup n k` obtained from `r.asGroupHom` and
the inverse of `Matrix.GeneralLinearGroup.toLin`. Its underlying matrix
at `g` is `LinearMap.toMatrix' (r g)`, as proved by `matrixHom_val`.
Empty coordinate types are allowed.

The proposition `HasFiniteCoordinateEnvelopes k G` requires the following
data for every two natural numbers `n`, `m` and homomorphisms
`r : G →* GL (Fin n) k`, `s : G →* GL (Fin m) k`:

- a reduced affine group scheme `H` over `k`, locally of finite type;
- matrix representations `p`, `q` of `H` on `Fin n`, `Fin m`;
- a homomorphism `α : G →* RationalPoint k H.X` whose family is dense in
  the published `HasDenseRationalPointFamily` sense;
- equalities `p.rationalMatrix (α g) = r g` and
  `q.rationalMatrix (α g) = s g` for every `g`.

This is an explicit existence property; defining it does not construct
such an envelope or assert that the property holds. It imposes no
characteristic assumption.

The theorem `rationalAction_comp_eq_of_matrix` proves that, if the rational
matrices of `p` along `α` are `matrixHom r`, then
`p.rationalAction.comp α = r`. It applies injectivity of the ordinary
matrix equivalence, `rationalAction_toMatrix` and `matrixHom_val`.
Neither density nor geometric hypotheses are needed for this equality.

## Conditional tensor and abstract-group reductions

Assume characteristic zero and an explicit proof
`h : CharZeroSemisimpleRepresentationIdentityComponentStatement.{u}`.
For a supplied reduced affine group scheme `H` locally of finite type,
two matrix representations `p`, `q`, and a dense family `α` as above,
`coordinate_tensor_semisimple_of_dense_envelope` proves that the product
coordinate tensor of their restricted rational actions is semisimple
whenever both restricted actions are semisimple.

The proof transfers the two hypotheses to `IsSemisimpleOnTests` by the
dense-family comparison. The tensor conjunct of `h k H` yields
`IsSemisimpleOnTests (p.tensor q)`; this predicate is definitionally the
local predicate in the sibling statement. The dense-family comparison
transfers this conclusion back, and `rationalAction_tensor_comp`
identifies the resulting action with the product coordinate tensor.

Finally, `abstractGroupTensorSemisimple_of_envelopes` assumes `h` and
`HasFiniteCoordinateEnvelopes k G` for every characteristic-zero field
in universe `u` and every group in universe `v`. Its conclusion is exactly
`CharZeroAbstractGroupTensorSemisimpleStatement.{u, v, w₁, w₂}`.
The proof uses the published finite-coordinate reduction to handle the
two arbitrary finite-dimensional carriers. It applies the supplied
envelope property to `matrixHom` of their coordinate actions, identifies
the restricted rational actions with those coordinate actions, and
applies the preceding conditional tensor theorem.
The field, group and two original vector-space universes are independent.

## Provenance and scope

These constructions and proofs are internal compositions of Mathlib's
invertible linear maps and matrix equivalence, the semisimplicity
transport and dense rational comparison modules, and the two unchanged
published statement definitions. No additional external-literature
correspondence is claimed. The algebraic semisimplicity statement is
passed as a premise, without importing a proof of it. This module alone
does not prove the unconditional abstract-group target.
