# Uniform bounds for fibre Lie dimensions over affine bases

These internal derived lemmas provide the uniform bound needed to truncate
Conrad's relative radical filtration (Theorem 5.4.3(i), p.174). They do not
construct that filtration. They bound the actual dual-number Lie dimension,
`Lie.dimension`, of every field-valued fibre of a smooth affine group scheme
over any affine scheme. There are no noetherian, connectedness, fixed-rank or
nonempty-base hypotheses.

For a spectrum base, the published `isLocallyConstant_lieRank` makes the
relative Lie rank locally constant. Compactness of the prime spectrum gives
finite range and hence a natural-number upper bound. Any map from a field
spectrum comes from a ring map; its algebra structure allows the published
`dimension_baseChange_eq_rankAtStalk` comparison to transfer the same bound to
the actual field fibre. For a general affine base, its canonical spectrum
isomorphism transports the group to a spectrum. The actual iterated pullback
comparison and invariance of Lie dimension under group-scheme isomorphisms
transport the bound back. The last lemma specializes this result to the
chosen geometric points of the Library.

`uniformDimensionBound` packages the general affine-base existence theorem
as data: a natural number and its bound for every field-valued fibre. The
constructor uses classical choice on that theorem. It does not assert that
the chosen bound is minimal or that local ranks are constant.
