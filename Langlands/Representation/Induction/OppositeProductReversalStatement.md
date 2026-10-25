# Opposite induction and reversed upper block products

Author: Worker 163. Worker 69 specified the canonical comparison and its
evaluation formulas in the task.

`Langlands.GLOppositeProductReversalStatement.{uF,uV}` is an internal
Prop-valued statement about the published normalized induction constructions.
It asserts existence of an actual complex-linear representation equivalence,
with both function maps constrained below. This pair states the target; it
does not prove that the equivalence exists.

## Exact scope and representations

The statement universally quantifies over a prime `p`,
`F : PadicField.{uF} p`, a supplied `T : F.TopologicalData`, every natural
rank `n`, and an actual `B : GeneralLinear.BlockShape n`. For a dependent
family `V : Fin B.length → Type uV` with complex module structures, its inputs
are representations

```
σ i : Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)
```

and the hypothesis `∀ i, IsSmooth (σ i)`. The field topology is `T.topology`.
The conclusion existentially quantifies over

```
E : Representation.Equiv
  (T.normalizedOppositeParabolicInduced B (B.blockTensor σ))
  (T.normalizedProductInduced B.reverse (fun i => σ i.rev)).
```

The target factor at `i` acts on `V i.rev`, has rank `B.size i.rev`, and uses
the original module structures at `i.rev`. These structures are installed
explicitly in the Lean statement. Both representations act on the same
ambient `GeneralLinear n F.Carrier` by right translation. There is no
ambient group pullback in the conclusion.

The field universe `uF` and block-carrier universe `uV` are independent.
The original and reversed tensor carriers are in `Type uV`; both induced
function carriers are in `Type (max uF uV)`. There is no positive-rank or
nonempty-family hypothesis. Rank zero and the empty tensor family are
included. The empty tensor is the existing `PiTensorProduct`, whose empty
case is equivalent to the coefficient field; it is not replaced by a zero
module. Reducible and zero smooth representations are allowed.

There are no irreducibility, admissibility, unitarity, temperedness,
finite-dimensionality, modulus-equality, classification, or supplied-equivalence
premises. Smoothness of the factors is the only representation-theoretic
hypothesis.

## Canonical forward and inverse formulas

The two local definitions in the proposition are the existing objects

```
w = B.reverseMatrix F.Carrier
R = PiTensorProduct.reindex ℂ V Fin.revPerm.
```

The type annotation on `R` explicitly identifies its codomain with
`PiTensorProduct ℂ (fun i : Fin B.reverse.length => V i.rev)`.
Mathlib's general `reindex` has codomain indexed by `V (e.symm i)`.
Here `B.reverse.length` reduces to `B.length` and
`Fin.revPerm.symm` reduces to `Fin.revPerm`
(`Fin.revPerm_symm` is proved by `rfl`). Thus no propositional type
transport or additional chosen linear equivalence is needed. On pure tensors,
`PiTensorProduct.reindex_tprod` gives

```
R (⨂ i, v i) = ⨂ i, v i.rev.
```

For the same existentially quantified `E`, the conclusion requires both
identities, for every induced vector and every ambient group element `x`:

```
(E f)(x)      = R (f (w * x)),
(E.symm h)(x) = R.symm (h (w⁻¹ * x)).
```

Lean expresses each evaluation using `Induction.eval`, with the subgroup and
inducing action inferred from the actual induced carrier. The inverse is
the inverse of this very `R`, not a separately chosen reindexing map.
Consequently the conclusion constrains the actual map on every vector,
including tensors that have not been presented as pure tensors.

`w` reverses whole blocks and preserves the coordinate within each block:
`B.reversePermutation (B.reverse.index i a) = B.index i.rev a`.
It need not be involutive and is not in general the full antidiagonal
permutation matrix. The inverse formula uses `w⁻¹`, as required.

## Internal provenance and remaining proof obligations

This statement is derived from the published definitions, not attributed as
an exact formula from the original literature. `Group.GL.ReverseBlocks`
constructs `B.reverse` and `w`, and proves that conjugation by `w` sends the
reversed upper parabolic to the original opposite parabolic.
`Group.GL.OppositeBlocks` supplies the actual opposite Levi projection.
`Induction.OppositeParabolic` and `Induction.BlockFactors` supply the two
representations; `Induction.Definitions` supplies their covariant functions,
uniform open right stabilizers, and right-translation actions.
`Group.GL.BlockModulus` defines the explicit determinant modulus and its
canonical positive half. Mathlib supplies the tensor reindexing equivalence.
The companion Markdown files of those constructions document their source
conventions; this pair makes no additional external-source claim.

The intended proof must establish the following consequences of those
definitions. They are proof obligations, not extra premises of this target.

1. For `q` in `B.reverse.parabolic F.Carrier`, put `qbar = w*q*w⁻¹` in
   `B.oppositeParabolic F.Carrier`. The actual projections must satisfy
   `(B.oppositeLeviProjection F.Carrier qbar) i.rev =
   (B.reverse.leviProjection F.Carrier q) i`.
   The published conjugation entry formula gives the corresponding diagonal
   entries; the proof must identify the resulting matrix units.
2. `R` must intertwine the original block tensor action with the reversed
   action on the reversed Levi tuple. The published `blockTensor_tprod`
   and Mathlib's `map_reindex` describe the required tensor identity.
3. If `m' i = m i.rev`, the explicit upper moduli must satisfy
   `T.leviModulus B.reverse m' = (T.leviModulus B m)⁻¹`.
   Reversing the ordered block pairs exchanges numerator and denominator
   in the defining product of determinant norms. This must yield
   `T.leviHalfModulus B.reverse m' = (T.leviHalfModulus B m)⁻¹`
   using the canonical positive square root, not merely equality of squares.
   The source opposite normalizing character is precisely the inverse
   original upper half, so it matches the target upper half.
4. These identities must prove covariance for both function formulas.
   Each entire function must have one uniform open right stabilizer.
   A stabilizer `K` for `f` also stabilizes `x ↦ R(f(w*x))`,
   because `w*(x*k) = (w*x)*k`; the inverse has the same property.
   Pointwise local constancy alone is not the required smoothness evidence.
5. Linearity, the inverse identities, and ambient equivariance must be
   assembled into `Representation.Equiv`. The inverse identities use
   `w*(w⁻¹*x) = x`, `w⁻¹*(w*x) = x`, and the inverse laws of `R`.
   Right equivariance uses `w*(x*g) = (w*x)*g` and the analogous inverse
   identity, with the unchanged ambient action.

These obligations require no identification of the explicit determinant
modulus with a Haar modulus. They compare the constructors as actually
defined. Generic conjugate-induction transport and generic finite-tensor
regrouping are separate reusable developments; this pair introduces neither.
It also makes no smooth-contragredient or inverse-transpose assertion.
