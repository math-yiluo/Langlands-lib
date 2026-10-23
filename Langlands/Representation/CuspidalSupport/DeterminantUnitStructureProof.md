# Proof of determinant-unit Levi structure

Author: Worker 110.

`Langlands.CuspidalSupport.leviDeterminantUnitStructure F T B` proves the
published proposition `LeviDeterminantUnitStructureTheorem F T B`. Its
parameters are a prime `p`, an actual `F : PadicField.{uF} p`, compatible
`T : F.TopologicalData`, arbitrary natural rank `n`, and
`B : Langlands.GeneralLinear.BlockShape n`. There is no positive-rank
assumption. The field universe `uF` is arbitrary.

For the actual product Levi `G = B.Levi F.Carrier` and the actual subgroup
`H = determinantUnitSubgroup T B`, the theorem proves, in order:

1. Multiplication on `G ⧸ H` is commutative.
2. `H ⊔ Subgroup.center G` has finite index in `G`.
3. `H ⊓ Subgroup.center G` is compact as a subset of `G`, with the product
   matrix-unit topology induced by `T.topology`.

The proof installs `T.topology` and assembles the three results below.
The statement and all imported Library pairs are unchanged. The existing
`determinantUnitSubgroup_normal` instance supplies the actual quotient
group structure. The imported theorem `isOpen_determinantUnitSubgroup`
remains available for the same topology; openness is already established
and is not an additional hypothesis of this theorem.

## Quotient commutativity

`determinantUnitQuotient_mul_comm T B` uses
`QuotientGroup.quotientKerEquivRange` for `leviDeterminantNorm T B`.
By definition, `H` is the kernel of this homomorphism into the product of
groups of nonnegative-real units. Its range is commutative.
The multiplication-preserving equivalence and its injectivity therefore
give commutativity of the actual quotient.

## Finite index after adjoining the center

The private homomorphism `leviOrderMod T B` sends a tuple `g` to its block
determinant orders modulo the respective block sizes:
`T.ord (determinant (g i) : F.Carrier)` in `ZMod (B.size i)`.
These additive cyclic groups are written using `Multiplicative`. The
orders add under multiplication, so this is a group homomorphism.
Every block size is positive, and the index family is finite; hence its
target is finite and its kernel has finite index.

For a tuple in that kernel, choose integers `k i` such that its block
determinant orders equal `(B.size i : ℤ) * k i`. Let `z i` be the scalar
matrix associated to `T.uniformizerUnit ^ k i`. Scalar matrices commute
with every matrix, so `z` lies in the actual Levi center.
`ord_det_scalar_uniformizer` computes its block determinant orders using
the scalar determinant formula, the order of integer powers and the
normalization `T.ord_uniformizer = 1`.

The tuple `g * z⁻¹` then has determinant order zero in every block.
`T.ord_eq_zero_iff_normalizedAbs` places it in `H`. Since
`g = (g * z⁻¹) * z`, the kernel of `leviOrderMod` is contained in
`H ⊔ Subgroup.center G`. The theorem
`determinantUnit_sup_center_finiteIndex T B` applies
`Subgroup.finiteIndex_of_le` to this inclusion.

## Central compactness and assembly

The third conjunct is the published
`leviDeterminantUnitCentralCompactness F T B`, imported from
`Langlands.Representation.CuspidalSupport.DeterminantUnitCentralCompactnessProof`,
whose proof is by Worker 225. That result identifies the intersection with
the continuous scalar image of the product of norm-one field units.
Those units are compact by the valuation-one sphere argument; positivity
of each block size converts the determinant condition on a central scalar
into norm one. This gives ambient compactness for exactly the subgroup,
center and topology in the full structural statement.

The final theorem packages these three conclusions without further
hypotheses. All arguments use the finite block family, including its
empty case. At rank zero, positivity and the sum of the block sizes force
the family to be empty. The Levi and the finite auxiliary target are then
one-element products, and the compactness argument uses the corresponding
singleton. No separate nonempty-family assumption is used.

## Source and scope

The source is I. N. Bernshtein and A. V. Zelevinskii, *Representations of
the group GL(n,F), where F is a non-Archimedean local field*, Russian
Mathematical Surveys 31:3 (1976), 1–68, English translation, Chapter II,
section 3.20(a)–(b), printed/PDF page 34. Registered source ID:
`bernstein-zelevinsky-1976-representations-gln`; SHA256:
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
The retained original and neighboring pages 33–35 were read.

The source states these structural assertions without supplying the
implemented proofs. The algebraic homomorphism and uniformizer arguments
above are internal deductions from the existing Library and Mathlib.
The central compactness proof is reused by Lean name. The subgroup join
expresses the source's product with the center. The empty-product case is
the published statement's internal rank-zero extension. This theorem
asserts no representation-theoretic semisimplicity or Harish-Chandra
equivalence.
