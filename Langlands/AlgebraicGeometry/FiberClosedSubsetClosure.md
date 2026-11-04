# Actual closures of closed subsets of a scheme fibre

This derived construction implements the closure-family step in the proof of
Stacks Project Lemma 37.28.4 (055G), in the registered source
`stacks-fibre-constructibility-local-dimension-2026-11-04`, retained `055C.html`.
The source takes closures in the source of the finitely many irreducible
components of the generic fibre, shrinks until they cover, and preserves their
pairwise nonempty intersections. This is a prerequisite for the geometric
connectedness input to Conrad's Theorem 3.4(2). The construction below supplies
actual closed subschemes and their exact point-set comparisons. The shrinking
conclusion explicitly retains a Noetherian base.

For an actual morphism `f : X ⟶ Y`, point `y : Y` and closed subset `C` of the
actual scheme-theoretic fibre `f.fiber y`,
`fiberClosedSubsetClosureIdeal f y C` is the vanishing ideal sheaf of the closure
in `X` of the image of `C` under the actual fibre projection. Its associated
scheme is `fiberClosedSubsetClosure f y C`, and
`fiberClosedSubsetClosureι f y C` is its actual closed immersion into `X`.
These are Mathlib's vanishing-ideal and closed-subscheme constructions, not an
assumed extension or a supplied family of putative components. The schemes have
arbitrary common universe `u`; an index family may have independent universe `v`.

The underlying range of this immersion is exactly that topological closure,
by the support formula for the vanishing ideal and the range formula for its
closed subscheme. Pulling this range back to the original fibre recovers `C`
exactly: the fibre projection is a topological embedding, so inverse image of
the closure of its image is the closure of `C`, and `C` is closed.
`range_baseChange_fiberClosedSubsetClosureι` identifies this inverse image with
the actual range of the scheme base change. This is equality of underlying
subsets; no isomorphism with a prescribed closed-scheme structure on `C` is
asserted. These comparisons require no finite type, quasi-compactness,
Noetherianity, affineness or separation hypothesis.

For an arbitrary family of closed subsets of the same fibre, the
`fiberSubschemeSets` construction recovers every original subset.
The coverage predicate on that fibre is therefore equivalent to their union
being the whole fibre, and the incidence predicates are exactly nonempty
intersections of the original closed subsets. Equal indices are included.

For a finite covering family at a whole-space generic point `η`, a locally
finite-type quasi-compact morphism over a Noetherian base has an open
neighbourhood of `η` on which these actual closures cover every fibre and
retain exactly the original nonempty-intersection pattern. The proof applies
the imported simultaneous cover/incidence shrinking theorem and the exact
original-fibre comparisons. The neighbourhood is nonempty because it contains
`η`. No flatness, properness, smoothness or separation assumption is added.

`fiberComponentClosedSubset` uses Mathlib's actual maximal irreducible
components of the actual fibre as closed subsets, and `fiberComponentClosureι`
constructs their actual closure immersions. A finite-type fibre over its
residue field is Noetherian, so this index family is finite. Its sets cover the
fibre. The final theorem applies the preceding construction to give a
neighbourhood where the closures of all actual generic irreducible components
cover every fibre with exactly their original incidence pattern. An empty
generic fibre and its empty component family are included.

The construction does not assert that the nearby pieces are maximal
irreducible components, geometrically irreducible or geometrically connected.
It proves no scheme isomorphism on the original fibre or geometric
irreducibility spreading. Finite generic splitting, those geometric properties
and the full generic-constancy theorem remain separate obligations.
