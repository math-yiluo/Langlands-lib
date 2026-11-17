# Recovering a centralizer Borel from an ambient Borel

Worker 249.

This is an internal reduction for the converse assertion of
`TorusCentralizerBorelStatement`. It derives that converse over an algebraically
closed field from the assertion that every Borel containing the torus has Borel
intersection with its centralizer. It does not assert or prove the intersection
assertion itself.

The theorem `exists_ambient_borel_of_torusCentralizer_intersections` assumes a
smooth connected affine group `G`, a closed torus `s : S.toGrp ⟶ G`, a closed
representative `c : C ⟶ G` of its all-test centralizer, and the Borel property
of the actual pullback intersection for every ambient Borel containing `S`.
For every Borel `d : D ⟶ C`, it constructs an ambient Borel `b : B ⟶ G`
containing `S`, with the exact equality of subgroup functors
`range (d ≫ c) = range c ⊓ range b`.

The proof first puts the smooth connected commutative torus into a Borel `B₀`
using the published solvable-subgroup containment theorem. Smoothness and
connectedness of the torus centralizer permit the published Borel-conjugacy
theorem to conjugate `C ∩ B₀` onto the prescribed Borel `D`, by a rational
point `z` of `C`. The image point in `G` fixes the original torus morphism.
Conjugating `B₀` by that point therefore still gives a Borel containing the
original torus. Naturality of inner automorphisms preserves the range of `C`
and identifies the conjugated intersection with `D`. Transport of subgroup
functors through an ambient isomorphism preserves pointwise intersections,
so this gives the stated equality on every test scheme.

The provenance is derived from the published Library theorems `borelConjugacy`,
`solvableSubgroupBorelContainment`, `torusCentralizerSmooth`, and
`IsTorus.connectedSpace_centralizer`. The conditional reduction adds no
mathematical assumptions to those published results. The intersection
assertion remains an explicit hypothesis of this helper.
