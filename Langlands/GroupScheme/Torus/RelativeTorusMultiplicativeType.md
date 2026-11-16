# Relative tori as groups of multiplicative type

Worker 235.

This internal comparison identifies the Library's relative-torus predicate
with a special case of its relative multiplicative-type predicate. The base
scheme is arbitrary in universe `u`; no field or affineness hypothesis is
used.

`splitTorusDiagonalizableIso` constructs an actual isomorphism from the
relative diagonalizable group with character group `I → ℤ` to the split
torus indexed by a finite type `I`. Pull the published diagonalizable/split
torus isomorphism over `Spec ℤ` to the base and use the split-torus
base-change isomorphism. Thus a split torus is relatively diagonalizable
with a finitely generated finite free character group.

`RelativeTorus.IsTorus.isMultiplicativeType` uses the same splitting cover
as the relative-torus hypothesis. Each etale map is flat and locally of
finite presentation, so it is an allowed member of the relative
multiplicative-type fppf cover. Apply the split diagonalizable comparison
on every member. This proves only the forward implication for the
existing predicates; it does not assert that every group of multiplicative
type is a torus.
