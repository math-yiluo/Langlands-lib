# Recovering subset equality from actual normalization

This supporting unit proves that normalization by one lift of the specified
longest representative recovers equality of the associated simple-index subset,
provided the actual Levi Weyl identification and associated-Levi conjugation
comparisons hold. It also proves the converse and the resulting existence
equivalence. All declarations are in `Langlands.Aubert.General`.

The unit is an internal deduction from published group and Coxeter declarations.
It introduces no assertion from original literature. The representation-theoretic
implication from reducibility of cuspidal induction to normalization remains
unproved here, as does the full rational rank-one self-association target.

## Parameters and actual subgroup conventions

Fix independent universes `uI` and `uG`, a group `G : Type uG`, a finite index
type `B : Type uI`, a family `M : Finset B → Subgroup G`, a subgroup `T`, a
Coxeter matrix `C` on `B`, and
`actual : RelativeWeylIndexing.ActualCoxeterSystem T C`.
Except for the injectivity theorem, also assume
`Fintype (RelativeWeyl.Weyl T)`.

Here `RelativeWeyl.Weyl T` is the actual normalizer modulo the full centralizer,
`N_G(T) / Z_G(T)`. A lift is an element of `RelativeWeyl.normalizer T`;
its class is formed by `QuotientGroup.mk`. Write
`w_J = longestRep actual J` and `J' = associatedSubset actual J`.
These are the published constructions: `w_J` is the selected maximal-length
member of `D(J,∅)`, and `J'` is the simple-reflection image of `J` under
inverse conjugation by `w_J`.

The comparisons used in the theorems are precisely:

- `actualLeviWeylIdentification T M actual`: for every `I`,
  the range of `RelativeWeyl.inclusion T (M I)` equals
  `standardSubgroup actual I`.
- `actualAssociatedLeviConjugation T M actual`: for every `J` and every
  lift `n` of `w_J`,
  `(M J').map (MulAut.conj (n : G)) = M J`.

Both comparisons are visible hypotheses. An arbitrary subgroup family need
not satisfy them. No topology, representation, maximality condition on `J`,
or nonempty-index hypothesis occurs in this unit.

## Definition and proved declarations

`HasNormalizingLongestLift M T actual J` is the Prop-valued definition

```text
∃ n : RelativeWeyl.normalizer T,
  QuotientGroup.mk n = longestRep actual J ∧
  ∀ x : G, x ∈ M J ↔ (n : G) * x * (n : G)⁻¹ ∈ M J.
```

The quantified lift is of the specified quotient class. The membership
equivalence asserts normalization of the subgroup; it does not assert
that conjugation fixes each element.

`leviFamily_injective_of_actualLeviWeylIdentification` takes the first
comparison and proves `Function.Injective M`. It does not require finiteness
of the ambient Weyl group. Given `M I = M J`, apply
`RelativeWeylIndexing.standardSubgroup_injective actual`.
The comparison rewrites the standard subgroups as the two inclusion ranges.
Apply `congrArg` to `H ↦ (RelativeWeyl.inclusion T H).range` and the given
subgroup equality. Binding `H` in this function keeps the dependent normal
subgroup instances coherent.

`associatedSubset_eq_of_longestLift_normalizes` takes both comparisons,
`J`, a lift `n` of `w_J`, and its normalization membership equivalence.
It proves `associatedSubset actual J = J`. By the preceding injectivity
theorem, it suffices to show `M J' = M J`. From the actual associated-Levi
image equality, the published `conjugationMembership_of_map_eq` gives

```text
y ∈ M J ↔ (n : G)⁻¹ * y * (n : G) ∈ M J'.
```

Evaluate this at `y = (n : G) * x * (n : G)⁻¹` and cancel. It follows that
`x ∈ M J'` iff the forward conjugate of `x` belongs to `M J`.
The assumed normalization equivalence therefore gives
`x ∈ M J' ↔ x ∈ M J`. Subgroup extensionality finishes the equality.

`longestLift_normalization_iff_associatedSubset_eq` takes the same two
comparisons and any specified lift `n` of `w_J`. It proves

```text
(∀ x : G, x ∈ M J ↔ (n : G) * x * (n : G)⁻¹ ∈ M J)
  ↔ associatedSubset actual J = J.
```

The forward direction is the previous theorem. For the reverse direction,
rewrite the actual associated-Levi image equality using `J' = J`, then
apply `conjugationMembership_of_map_eq` to the forward conjugate of `x`.
Cancellation and symmetry give the displayed normalization direction.
Since `n` is arbitrary subject to its class equation, this direction proves
normalization for every such lift.

`hasNormalizingLongestLift_iff_associatedSubset_eq` takes both comparisons
and proves

```text
HasNormalizingLongestLift M T actual J ↔ associatedSubset actual J = J.
```

The forward direction extracts the witness and uses
`associatedSubset_eq_of_longestLift_normalizes`. For the reverse direction,
`QuotientGroup.mk_surjective` gives an actual lift of `w_J`, and
`longestLift_normalization_iff_associatedSubset_eq` supplies normalization
for that lift. Thus the quotient-class lift exists independently of the
normalization question.

## Dependencies and remaining obligation

The module imports `Langlands.Representation.Aubert.General.JacquetTarget`
and `Langlands.Group.RelativeWeylSolomonProof`. Its proof bodies use
`conjugationMembership_of_map_eq` from the former,
`standardSubgroup_injective` from the latter, and Mathlib's quotient
surjectivity, equality congruence, subgroup extensionality and group
simplification. The injectivity lemma uses only the standard-subgroup
injectivity result from the Solomon module, not its alternating
cancellation theorem.

The new unit depends only on published modules. In particular, it can be
used without importing the separate equality-only rational self-association
reduction. To obtain the required rational rank-one theorem by this route,
one must still prove that the actual reducible normalized induction in the
published target produces such a normalizing lift, or prove the associated
subset equality directly. Neither implication is assumed or discharged by
this supporting unit.
