# Recovering and comparing quotient points from cocycles

`Langlands.GroupScheme.QuotientPointCocycle.QuotientPointCocycleComparisonStatement`
concerns an inclusion `n` representing the kernel of `q : G ⟶ Q` on all
tests and a cover that is an effective epimorphism. It extends the
Library's comparison between quotient points and kernel cocycles.

Suppose a cocycle of the kernel becomes a coboundary in `G`. Composing
the cobounding cochain with `q` gives the same value on the two
projections of the cover because the cocycle maps to the identity in
`Q`. It therefore descends to a base point of `Q`. The obstruction
cocycle of that point and cochain agrees with the original cocycle on
each test by the monomorphism property of `n`.

If two quotient points differ by right multiplication by the image of
a base point of `G`, multiply the first lift by this base point. The
two lifts then differ by a kernel-valued cochain. The resulting twist
gives the cohomology relation of the two obstruction cocycles.
