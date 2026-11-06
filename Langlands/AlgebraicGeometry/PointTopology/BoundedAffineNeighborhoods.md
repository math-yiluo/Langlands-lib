# Finite affine families for bounded finite sets

This is derived geometric infrastructure for the finite locally free Weil
model used in Conrad, *Weil and Grothendieck approaches to adelic points*
(2011), Example 4.2, printed pages 9–10. It concerns the actual affine opens
of a scheme, rather than a supplied covering package. The source's
quasi-projective setting supplies affine neighborhoods of finite point sets
through the existing proved projective-immersion comparison. The finite
selection argument here is an auxiliary derivation, not a separately
numbered assertion quoted from Conrad.

Let X be a quasi-compact scheme, expressed by `CompactSpace X`, and suppose
`HasFiniteAffineNeighborhoods X`: every finite subset of its underlying
points lies in an affine open. `affineTupleNeighborhoodFamily X hX n`
constructs a finite set of original affine opens such that every tuple of
n original scheme points is wholly contained in one member. Its intrinsic
law is `affineTupleNeighborhoodFamily_covers`.

For each original affine open U, the set of tuples whose every coordinate
lies in U is open in the ordinary product topology on `Fin n → X`.
These opens cover that product because a tuple has finite range and hX
places its range in an affine open. Mathlib's compactness of products and
finite-subcover theorem give the finite family. This argument uses the
original topology of X and its product; it requires no Hausdorffness,
separatedness, quasi-separatedness, or Noetherian hypothesis.

`boundedAffineNeighborhoodFamily X hX n` is the finite union of these
families over tuple lengths zero through n. The law
`boundedAffineNeighborhoodFamily_covers` says that any map into X from a
finite type with at most n elements has its entire range in one member.
The proof enumerates the finite type using `Fintype.equivFin`, applies the
family for its actual cardinality, and includes that family in the finite
union. Empty indexing types and empty ranges are included through the
zero-length case. No nonemptiness of X or of the indexing type is assumed.

This construction does not assert a fiber bound or quasi-compactness of a
Weil scheme. Deriving a uniform bound for the actual finite coefficient
fibers and using this family to give a finite affine cover of the actual
Weil model remain subsequent host obligations.
