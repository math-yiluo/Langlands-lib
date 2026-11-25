# Actual test-comparison composition over supplied scalar structures

This module retains the previously proved actual comparison square for
successive coefficient extension after retyping the intermediate and final
scalar structures. `iteratedReAlgebraComparison` and
`directReAlgebraComparison` retain the two specified actual extended comparisons.
`testIso_baseCompReAlgebra` eliminates the two scalar equalities and applies the
whole integral test-comparison composition equation. Every finer chart remains
specified with its own actual test-unit evidence.

`testIso_baseAlongComp` specializes this equation to two supplied algebra
homomorphisms and their actual composite. Its vertical maps are the existing
actual full-order coefficient-composition atlas isomorphisms on the specified
outer charts. Independent original, direct and iterated finer charts are
allowed. `baseAlongCompTestSquare` packages the four actual rationalized maps
and the proved square.

The generic `Iso.rationalSquare` rationalizes four supplied integral full-order
isomorphisms with a proved integral square. It proves the corresponding
actual rational equation using preservation of integral composition by the
ambient tensor Hom and the full-order centralizer. It retains the rational
inverses of the same actual integral maps.

The special-atlas operations retain the local field, finite-dimensional
central division algebra and embedded field hypotheses. Coefficient rings
have universe `v` independent of the local-field universe; covers may be
infinite and scalar maps may merge generators. Generic rationalization permits
separate universes and arbitrary finite coordinate types, with the existing
domain/fraction-field assumptions. This module does not assert commuting
coefficient-square naturality (proved in `SpecialAtlasComparisonTestSquare` as
`testIso_baseAlongSquare`) or original framed comparison base change.
