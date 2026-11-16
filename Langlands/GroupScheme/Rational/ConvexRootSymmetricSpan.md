# Saturation of the symmetric part of a convex root subset

This internal helper uses the published definitions of `IsConvexRootSubset`
and `parabolicRootLevi`. It applies to any subset `R` of the actual character
lattice stable under negation; no root-system structure or reductivity is used.

`symmetricRootRatSpan X` is the rational span of the characters in
`parabolicRootLevi X = {γ | γ ∈ X ∧ -γ ∈ X}`. For a subset convex in the
published sense, its symmetric part consists exactly of the ambient roots
whose rational images lie in that span.

The proof chooses the cone defining convexity. Both signs of each symmetric
root lie in the cone, so its real tensor image lies in the cone's lineality
subspace. The real span of those images therefore lies in that subspace.
An ambient root in this span and its negative lie in the cone, and negation
stability keeps both in the ambient set. They consequently belong to `X`.
The published rational-to-real span comparison transfers this conclusion to
the rational span. The reverse implication is membership of a generator in
its span.

This is a derived linear-algebra step for the Borel–Tits intersection proof.
It does not assert the group intersection theorem or the Weyl stabilizer
theorem.
