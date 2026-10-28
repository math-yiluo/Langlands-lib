# Proof of the opposite-parabolic mirabolic product identity

Author: Worker 593.

The theorem `Langlands.GeneralLinear.mirabolicOppositeProduct.{u}` proves the
published proposition
`Langlands.GeneralLinear.MirabolicOppositeProductStatement.{u}` without any
additional parameters or assumptions. It works for every field `K : Type u`,
every `a b : ℕ` with `ha : 0 < a`, and every actual matrix
`g : GeneralLinear (a+b+1) K`. With the published binary shape of ordered
sizes `a,b+1`, the conclusion is

```text
(∃ r : shape.oppositeParabolic K, ∃ m : mirabolic (a+b) K,
   g = r.val * m.val)
  ↔
∃ j : Fin (b+1), (g⁻¹) (Fin.last (a+b)) (Fin.natAdd a j) ≠ 0.
```

Here inversion and multiplication are operations in the actual matrix unit
group. The factors belong to the existing opposite parabolic and mirabolic
subgroups, with their existing membership certificates.

## Implemented proof

The private helper `exists_nonzero_row` proves that each row of an invertible
matrix has a nonzero entry. If a row were zero, the corresponding diagonal
entry of the product with its inverse would be zero, contradicting the
identity matrix.

For the forward direction, write `g=r*m`. Then `g⁻¹=m⁻¹*r⁻¹`.
The inverse `m⁻¹` is again mirabolic. The helper `mirabolic_mul_last` expands
matrix multiplication and uses its last-row equation to show that the last
row of `g⁻¹` is the last row of `r⁻¹`. Apply the published
`BlockShape.oppositeLeviProjection` to `r⁻¹`, taking its second block.
This is an actual invertible matrix of size `b+1`; the nonzero-row helper
supplies a nonzero entry in its final row. The binary coordinate formula
`BlockShape.binary_index_one` and
`MirabolicOppositeIntersection.tail_last` identify it with the required
ambient tail entry of `g⁻¹`.

For the converse, put `w(j)=(g⁻¹)(Fin.last (a+b),j)` and choose the supplied
nonzero coordinate `p=Fin.natAdd a k`. Let `l=Fin.last (a+b)`. The helper
`exists_prescribed_row` constructs

```text
A = identity with row p replaced by w,
Q(i,j) = A(swap(l,p)(i),j).
```

The identity rows span `w` with coefficients `w(i)`. Hence
`Matrix.det_updateRow_sum` gives `det A = w(p) ≠ 0`. Row permutation changes
the determinant only by its sign (`Matrix.det_permute`), so `det Q ≠ 0`,
whether or not `l=p`. `Matrix.GeneralLinearGroup.mkOfDetNeZero` makes `Q`
an actual unit `q`. The helper proves that row `l` is exactly `w` and that
every row other than `l,p` is its original identity row.

Both `l` and `p` are tail coordinates. Every head row is therefore an
unchanged identity row, and its entries in all tail columns vanish.
The private `mem_opposite_iff` specializes the published opposite-parabolic
membership theorem to these binary coordinates, proving `q` belongs to that
subgroup. Since its last row is `w`, matrix multiplication identifies the
last row of `q*g` with that of `g⁻¹*g=1`. Thus `q*g` is mirabolic.
The proof supplies the actual factors `r=q⁻¹` and `m=q*g`, with subgroup
membership proved, and finishes with the group identity
`g=q⁻¹*(q*g)`.

All helpers are local to this proof module. No existing Lean or Markdown
pair is changed.

## Boundary cases and provenance

The tail has size `b+1`, so the final tail coordinate exists even when `b=0`.
In that case the chosen pivot is the final coordinate and the row swap is
the identity; the same determinant argument applies. There is no assumption
on a preselected pivot: the pivot is obtained from the existential condition
being proved sufficient. The theorem retains the statement's arbitrary
coefficient universe and field hypotheses and its required `a>0`.

This is derived internal matrix algebra for the published
`MirabolicOppositeProductStatement`, using the existing `Mirabolic`,
`MirabolicOppositeIntersection`, and `OppositeBlocks` interfaces and
Mathlib determinant identities. It is not attributed to a literature theorem.
It asserts no continuity or measurability of a selection of factors, measure
or conullity statement, or representation-theoretic comparison.

## Complete unapplied declaration and axiom checks

The following complete assignment of the unapplied theorem constant was
compiled in the pinned environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, with no errors or warnings:

```lean
import Langlands.Group.GL.MirabolicOppositeProductProof

universe u

example :
    ∀ (K : Type u) [Field K] (a b : ℕ) (ha : 0 < a)
      (g : Langlands.GeneralLinear (a + b + 1) K),
      (∃ (r : (Langlands.GeneralLinear.MirabolicOppositeIntersection.shape a b ha).oppositeParabolic K)
         (m : Langlands.GeneralLinear.mirabolic (a + b) K),
        g = r.val * m.val) ↔
      ∃ j : Fin (b + 1), (g⁻¹) (Fin.last (a + b)) (Fin.natAdd a j) ≠ 0 :=
  @Langlands.GeneralLinear.mirabolicOppositeProduct

set_option pp.universes true in
#check @Langlands.GeneralLinear.mirabolicOppositeProduct

#print axioms Langlands.GeneralLinear.mirabolicOppositeProduct
```

The inspection outputs are:

```text
Langlands.GeneralLinear.mirabolicOppositeProduct.{u_1} :
  Langlands.GeneralLinear.MirabolicOppositeProductStatement.{u_1}

'Langlands.GeneralLinear.mirabolicOppositeProduct' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

The Lean service also built the proof module with Lake and inspected the
unapplied declaration, reporting kind `theorem`, level parameters `["u"]`,
and exactly these three axioms. These are development checks; independent
semantic review and formal exact-target validation remain separate acceptance
requirements.
