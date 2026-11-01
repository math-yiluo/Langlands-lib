# Topological bounds for principal section cuts

`SectionCutDimensionStatement` records two bounds for the actual vanishing
locus of a section. Dimensions take values in `WithBot ℕ∞`; the empty
space has dimension bottom.

First, in any irreducible topological space `T`, a closed subset `Z`
which is not the whole space satisfies `dim Z + 1 ≤ dim T`. Empty
closed subsets are allowed.

Second, for any scheme `X`, point `x`, and global structure-sheaf
section `c`, the Krull dimension of the local ring quotient
`𝒪(X,x)/(c_x)` is at most the topological dimension of the complement
of the actual basic open `D(c)` in `X`. There is no Noetherian,
integrality, or nonvanishing hypothesis in this bound.

These are internal geometric bridges for dimension induction in the
ample Euler polynomial proof. The first follows by extending chains of
irreducible closed subsets by the whole space. The second follows from
the canonical embedding of `Spec(𝒪(X,x)/(c_x))` into `X`, whose image
lies in the complement of `D(c)`. They assert no Euler polynomial or
positivity conclusion and do not construct a Cartier subscheme.
