# Propagation of etaleness on a relation slice

Let `B = V ×_U R`, let `p : B → V` be the first projection, and let
`h : B → U` be the second projection followed by `s`. Assume that `s` is
flat, `h` is locally of finite presentation, and `(t,s)` is the published
scheme equivalence relation. If `σ : V → B` is a section of `p`, then
formal etaleness of the actual stalk map of `h` at `σ(p(b))` implies
formal etaleness at `b`.

The proof uses the difference morphism `d : B ×_V B → R` and its two
cartesian squares. Pairing `σ(p(b))` with `b` gives an actual point of this
double pullback. Restricting its first projection to the etale locus of
`h` makes `d` etale near that point, by base change along `t`. Its stalk
map is consequently flat and formally unramified. Pointwise etale
descent in the second cartesian square, along the flat morphism `s`,
gives the conclusion at `b`. The auxiliary open-neighborhood argument
cancels the isomorphism on stalks induced by an open immersion.

This is internal groupoid infrastructure for the smooth equivalence
relation slicing proof. Worker 303 supplied the double-pullback
propagation argument. Worker 101's scheme etale-locus API supplies the
open etale locus; a private copy is used until that API is published.
The proof asserts no existence of a local slice and no quotient theorem.

The shrinking lemma takes `W = σ⁻¹(schemeEtaleLocus h)`. The canonical
map from the slice of `W` into `B` is an open immersion, as verified
by cancelling two cartesian squares. Every image point lies over
`W`, so the pointwise propagation lemma applies. Cancelling the open
immersion's stalk isomorphism gives formal etaleness at every point
of the new slice. The scheme etale-locus criterion then gives
etaleness of its whole map. The final theorem
`relationSliceEtalePropagation` proves exactly
`RelationSliceEtalePropagationStatement.{u}`.
