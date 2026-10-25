# Canonical opposite-to-upper block product reversal

Author: Worker 357.

`Langlands.glOppositeProductReversal.{uF,uV}` proves the unchanged published
`Langlands.GLOppositeProductReversalStatement.{uF,uV}`. This is an internal
transport proof from the actual block, tensor, character and smooth-induction
constructions. It imports the statement and all its dependencies unchanged.
No external theorem or literature identification of the explicit modulus with
a Haar modulus enters the proof.

## Scope and canonical maps

The theorem retains every quantifier of the target: an arbitrary prime, an
actual `PadicField` and supplied `TopologicalData`, arbitrary natural rank and
block shape, and dependent complex block modules in a universe independent of
the field. The inputs are arbitrary smooth block representations. Their
smoothness hypothesis is retained, although the transport of the already
smooth induced function spaces does not need to use it. There are no
irreducibility, admissibility, dimension, nonzero-vector, positivity-of-rank,
or classification hypotheses.

Write `P = B.oppositeParabolic F.Carrier`,
`Q = B.reverse.parabolic F.Carrier`, `w = B.reverseMatrix F.Carrier`, and
`R = PiTensorProduct.reindex ℂ V Fin.revPerm`. The constructed equivalence
between the normalized opposite induction and the reversed upper product has
exactly the formulas

```text
(E f)(x)      = R (f (w * x)),
(E.symm h)(x) = R.symm (h (w⁻¹ * x)).
```

Both formulas are proved by `rfl` after composing the published constructors.
Thus they constrain the actual maps on all tensor values, and the inverse uses
the inverse of this very `R`. No assertion that `w` is involutive is used.
`Fin.revPerm.symm` is definitionally `Fin.revPerm`, giving precisely the typed
reindex map in the target. Rank zero, the empty tensor, reducible inputs and
zero modules are all included by the same construction.

## Specialized geometric and character calculations

In `Langlands.GeneralLinear.BlockShape`, `reverseToOpposite` constructs the
multiplicative equivalence `Q ≃* P` by restricting `MulAut.conj w`. Its forward
map is `q ↦ w*q*w⁻¹`, and its inverse is the inverse conjugation. Membership is
provided by the published `reverseMatrix_conj_mem_oppositeParabolic_iff`;
the inverse and multiplicativity laws are inherited from the group
conjugation equivalence.

`oppositeLeviProjection_reverseToOpposite` proves

```text
(B.oppositeLeviProjection F.Carrier (B.reverseToOpposite F.Carrier q)) i.rev
  = (B.reverse.leviProjection F.Carrier q) i.
```

It uses extensionality of matrix units and then matrix entries, applying
`reverseMatrix_conjugate_entry` on each diagonal block. This compares the
actual published projections, including their invertible matrix structures.

In `Langlands.PadicField.TopologicalData`, `leviModulus_reverse` proves

```text
T.leviModulus B.reverse (fun i => m i.rev) = (T.leviModulus B m)⁻¹.
```

The proof expands the explicit determinant product, replaces its filtered
products by conditional factors, reindexes both finite indices with
`Fin.revPerm`, and uses reversal of the strict order. Swapping the two finite
products exchanges numerator and denominator in each surviving factor.
`Finset.prod_inv_distrib` then identifies their product with the inverse
original modulus. No nonempty indexing assumption enters this argument.

`leviHalfModulus_reverse` unfolds the canonical positive half as the
composition of the units map of `NNReal.sqrtHom` and the units map into the
complex numbers. The full-modulus identity and `map_inv` for these actual
homomorphisms prove the half-modulus identity. The proof therefore compares
the canonical positive halves themselves, rather than choosing a square root
from an equality of squares.

`oppositeHalfModulus_reverseToOpposite` combines this with the projection
identity to equate the opposite normalizing character at `w*q*w⁻¹` with the
upper normalizing character at `q`.

## Assembly from published transport constructions

Inside the closing theorem, `ρ` is the original normalized inducing action on
`P`; `α = ρ.comp e.toMonoidHom` is its pullback to `Q`, where
`e = B.reverseToOpposite F.Carrier`; and `τ` is the reversed upper normalized
inducing action. The projection identity first identifies the original Levi
tuple with the inverse of `FiniteTensor.reindexGroup` applied to the reversed
Levi tuple. `FiniteTensor.reindexEquiv_apply_action` then supplies the exact
tensor equivariance of `R` on every vector. Combining that identity with
linearity of `R` and equality of the normalizing characters constructs
`D : α.Equiv τ` with underlying linear equivalence `R`.

The published `Induction.conjugateSmoothInducedEquiv w e` gives
`C : (smoothInduced Q α).Equiv (smoothInduced P ρ)`. Its forward formula is
left translation by `w⁻¹`, and its inverse is left translation by `w`.
The desired equivalence is

```text
C.symm.trans (Induction.smoothInducedEquiv Q D).
```

The generic conjugation construction proves covariance in both directions
using `e`, its inverse and the inducing-action identity. It carries each
entire function's single open right stabilizer `K` to the same `K`, since
`w*(x*k) = (w*x)*k` and the corresponding identity holds for `w⁻¹`.
The coefficient-change construction uses `smoothInducedMap` in both
directions; postcomposition by `R` or `R.symm` preserves the same uniform
stabilizer. Neither construction uses topology on the tensor carrier.

The published equivalences also provide linearity, both inverse identities,
and intertwining for the unchanged ambient right-translation action. Their
inverse identities reduce pointwise to group cancellation and the inverse
laws of the linear equivalence. Composition retains these properties and
both evaluation formulas reduce definitionally to those in the target.

The reused generic constructions are in `Induction.ConjugateParabolic`,
`Induction.Equivalences` and `Tensor.FiniteRegrouping`. This proof adds only the
specialized block-conjugation and determinant-character calculations and
their assembly; it does not reimplement those generic transports.
