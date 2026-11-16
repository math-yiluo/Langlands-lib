# The only remaining conditional local rank-one E₆ marking

For an actual index of a simply connected group over a nonarchimedean
local field, suppose its split rank is one and an equivalence of its
actual simple vertices preserves every entry of the E₆ Cartan matrix.
Under the explicit `LocalAnisotropicCartanComponentsStatement` premise,
`localRankOneTypeE6_marking_of_components` proves that the exact
distinguished set is vertex 1 in zero-based numbering and every element
of the full absolute Galois group fixes every vertex. The theorem retains
every field and residue characteristic and arbitrary universe.

Every Cartan-preserving permutation of E₆ is identity or the simultaneous
exchange of the two equal arms. The actual rank-one orbit comparison
therefore confines the distinguished set to a chosen vertex and its
arm-exchange image. Actual opposition is that arm exchange by
`TypeE6Opposition`, and it preserves distinguished vertices. Thus the
distinguished set is exactly this pair, with a fixed vertex counted once.
All its simple roots have the same actual nonzero restriction.

The ten-reflection certificate gives an actual root with coefficients
`(1, 2, 2, 3, 2, 1)`. Applying the additive actual restriction map kills
the zero vertices. Summing the other coefficients gives the multipliers
`(2, 2, 4, 3, 4, 2)` at the six possible chosen vertices. The
characteristic-independent relative-root multiple theorem excludes
vertices 2, 3, and 4. If either endpoint 0 or 5 is chosen, the exact
distinguished pair is `{0, 5}`. Zero vertex 3 then has three distinct zero
neighbors 1, 2, and 4, which the supplied type-A component premise excludes
through the actual anisotropic-kernel comparison. Only vertex 1 remains.

For each full absolute Galois element, the Cartan symmetry bound is one
global choice between identity and arm exchange. In the remaining
marking, vertices 3 and 2 are zero. Arm exchange fixes 3. The component
premise forces an adjacent zero vertex to be fixed by that same element,
so it must fix 2 as well. This contradicts arm exchange, which sends 2 to
4. Hence the full star action is trivial.

This is an internal conditional reduction. The remaining coefficient-two
marking has zero subdiagram A₅, so the argument leaves it unresolved.
Neither E₆ exclusion, the component premise, nor the unconditional local
rank-one enumeration is proved here. No downstream local classification
or Kneser–Tits result is used.
