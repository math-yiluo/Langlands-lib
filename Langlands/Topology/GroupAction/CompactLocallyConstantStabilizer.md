# Open stabilizers of locally constant functions on compact action spaces

Worker 56 constructs the subgroup fixing an actual function `f : X → A`
under precomposition by a group action, using the equation
`f (g • x) = f x` for every `x`. The group, space, coefficient set and finite
index type have independent universes.

For a continuous action of a topological group on a compact space and a
locally constant function, `openStabilizer` equips precisely this subgroup
with a proved openness property. No topology on the coefficient set,
Hausdorff assumption, local compactness of the group, nonarchimedean group
assumption, or supplied fixedness condition is required. The space and
finite index type may be empty.

The proof compares the two locally constant functions on `G × X` with values
`f (g • x)` and `f x`. They agree near each `(1, x)`. Mathlib's
`IsCompact.eventually_forall_of_forall_eventually`, applied to the entire
compact space, supplies one neighborhood of the identity on which the
equality holds for every point. The subgroup laws follow from the action
laws, and `Subgroup.isOpen_of_mem_nhds` proves openness.

`functionStabilizer_comp_eq` proves that surjective equivariant pullback
preserves the entire stabilizer, using surjectivity to recover the
downstairs equation. `finiteOpenStabilizer` intersects the stabilizers of
a finite family. `refinedFiniteOpenStabilizer` intersects that subgroup
with a prescribed open subgroup. Their membership lemmas give the exact
fixedness equations.

This is an internal topological construction supporting the compact
represented-domain action data in the companion analytic adapter. Its
provenance is the action laws, local constancy and the cited Mathlib
compactness API. The existing Library proof
`Langlands.Representation.Hecke.CommonInvarianceProof` by Worker 108 uses
the same compact-uniformity method for left translation on the support of
a Schwartz–Bruhat function; the present construction treats compact action
spaces and arbitrary coefficient sets. It constructs neither a
representation category nor a smooth sheaf or cohomology comparison.
