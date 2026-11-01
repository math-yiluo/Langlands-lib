# Actual Bruhat support cores

Author: Worker 194.

This internal prerequisite identifies the corrected two-sided Weyl core with
the greatest parabolic-invariant subset of an actual matrix Bruhat support.
The equality is proved over every field and in every natural rank, including
zero. There is no topology or representation parameter.

`borelCell R w` is the double coset of the actual matrix
`(GeneralLinear.permutation n R w)⁻¹` under the actual invertible upper
triangular subgroup on both sides. `bruhatSupport R θ` is the union of these
sets for `w ∈ θ`. The inverse-permutation convention agrees with the Library's
geometric lemma: the matrix parabolics are `P_B` on the left and `P_C` on the
right, while the corresponding Weyl subgroups are `W_C` on the left and
`W_B` on the right.

The module first establishes elementary support monotonicity and the empty
support identity. Every Borel cell lies in the parabolic double coset with
the same inverse permutation matrix, because the upper triangular subgroup
is contained in both standard block parabolics.

The injectivity assertion
`inverse_permutation_borelCell_injective` is proved over every nontrivial
commutative ring. The published `BlockShape.singletons n` from
`Group/GL/SingletonBlocks` has `n` blocks of size one. The module reuses its
identity coordinate numbering and derives its trivial block-preserving Weyl
subgroup.
An equality of Borel matrix double cosets therefore gives an equality of its
parabolic matrix double cosets. The published
`Geometric.weyl_doubleCoset_eq_of_inverse_permutation_eq` reflects this to
its Weyl double cosets. Both Weyl factors are the identity, so the two
permutations agree. Consequently an inverse permutation matrix belongs to
`bruhatSupport R θ` exactly when its permutation belongs to `θ`.
The construction and coordinate calculation do not require positive rank.

Over a field, `exists_borelCell` uses the published actual upper Bruhat
factorization theorem. If `g = a * permutation w * b` with upper triangular
`a,b`, it lies in `borelCell F w⁻¹`. Thus every matrix lies in a Borel cell,
and `bruhatSupport F Set.univ = Set.univ`.

For any block shapes `B,C` and any Weyl set `θ`,
`twoSidedCore_bruhatSupport` proves the exact equality

```text
twoSidedCore (B.parabolic F) (C.parabolic F) (bruhatSupport F θ)
  = bruhatSupport F (weylSupport B C θ).
```

For the forward inclusion, choose a Borel cell containing the matrix `g`.
Every inverse permutation matrix whose Weyl representative is in the same
`W_C`-left, `W_B`-right double coset lies in the same actual parabolic
matrix double coset as `g`, by the published descent of permutation matrices.
Membership of `g` in the actual matrix core puts every such inverse
permutation matrix in `bruhatSupport F θ`. Borel injectivity then puts its
Weyl representative in `θ`. The chosen representative therefore lies in
the two-sided Weyl core.

For the reverse inclusion, let `g` lie in a Borel cell indexed by the Weyl
core, and take any `x` in its actual parabolic matrix double coset.
Choose a Borel cell containing `x`. Equality of the coarse matrix double
cosets reflects to equality of the Weyl double cosets. The core condition
puts this second Borel-cell index in `θ`, so `x` lies in the original matrix
support. This proves membership in the actual matrix core.

The previously proved greatest-core property shows that this equality
indeed identifies the largest subset of `bruhatSupport F θ` invariant
under left `P_B` and right `P_C`. The exported
`corrected_bruhatSupport_invariant` records that invariance directly.

The provenance is internal: this is a quotient-and-support comparison using
the already published actual upper Bruhat factorization, Weyl descent,
Weyl reflection and elementary block coordinate definitions.
The imported two-sided-core pair records its own corrected-source
provenance. This module does not prove that a chosen support is open,
construct a length-compatible filtration, identify support subspaces or
their images in actual Jacquet quotients, compare orbital integrals or
graded transition maps, introduce exterior signs, or prove exactness or
signed effectivity. Those representation-theoretic applications remain
separate obligations.
