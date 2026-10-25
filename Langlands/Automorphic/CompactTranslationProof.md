# Compact right translation preserves actual automorphic forms

Author: Worker 84. Module: `Langlands.Automorphic.CompactTranslationProof`.
All declarations below are in `Langlands.Automorphic`.

`automorphicCompactTranslation` proves exactly the published
`AutomorphicCompactTranslationStatement K n`. For an arbitrary number field
`(K : Type u) [Field K] [NumberField K]`, every natural rank `n`, every
`k : standardInfiniteCompact K n`, and every actual smooth rational function
`f` satisfying `IsAutomorphicForm K n f`, its right translate by
`AdelicGL.ofInfinite K n k.val` satisfies the same predicate. The action is
positive right translation: evaluation at `x` gives `f(x * ofInfinite k.val)`.
The closing unapplied example checks the full parameter telescope, including
the arbitrary universe and rank zero.

## Finite level, compact finiteness and growth

`hasFiniteLevel_continuousRightAction` converts the existing finite-level
predicate to membership in `finiteSmoothSubrepresentation`, applies its
stability under the full adelic right action, and converts back using
`hasFiniteLevel_iff_mem_finiteSmooth`.

`isInfiniteFinite_infiniteSubgroupRightAction` applies the published
`infiniteFiniteSubrepresentation` of an arbitrary infinite subgroup `U` to an
element of that same subgroup. The final theorem specializes `U` to the actual
standard infinite compact subgroup, the product of orthogonal and unitary
factors. This argument preserves finiteness under that subgroup; it makes no
claim that full infinite translation preserves the compact-finite form space.

`hasPolynomialGrowth_continuousRightAction` uses the published
`polynomialGrowthSubrepresentation` and its membership characterization.
It preserves the existing growth predicate with a separate bound for each
finite slice. Constants and exponents may depend on that slice and the
translated function; no common exponent or unchanged bound is asserted.

## Simultaneous center finiteness

`infiniteTranslateFamily g` is the complex-linear map applying the actual
archimedean smooth right action by `g` to every member of a `SmoothSliceFamily`.
`smoothSliceFamily_infiniteRightAction` identifies the family associated to
an adelically translated function with this pointwise translation of its
original family. Its proof uses extensionality and the actual adelic identity
`pair a b * ofInfinite g = pair (a * g) b`.

`centerFamilyOrbitSpan_infiniteTranslateFamily_le` places the center orbit of
the translated family inside the linear image of the original common center
orbit under `infiniteTranslateFamily g`. The proof first writes the orbit
span as the range of the center action. For any central element `z`, it chooses
the inverse image of `z` under the actual algebra equivalence
`ArchimedeanGL.centerConjugation K n g`. This produces an element in the
original orbit whose translate is the required translated-orbit element.
The equality holds for every slice by the published genuine covariance theorem
`ArchimedeanGL.centerRightCovariance` from
`Langlands.Global.ArchimedeanCovarianceProof`, followed by cancellation of the
algebra equivalence and its inverse. In particular, the proof retains
conjugation explicitly and does not assume that it fixes central elements
pointwise.

`isCenterFiniteFamily_infiniteTranslateFamily` uses finite dimensionality of
the original common orbit, finite dimensionality of its linear image, and
`Submodule.finiteDimensional_of_le` for the inclusion just proved. The same
finite-dimensional image controls the entire family at once.
`isCenterFinite_infiniteRightAction` applies this result to the actual smooth
slice family and rewrites the slice identity. These center-finiteness helpers
hold for every infinite group element. They preserve the simultaneous condition,
not merely separate center finiteness of each individual slice.

## Assembly and provenance

`automorphicCompactTranslation` assembles the four defining conditions of
`IsAutomorphicForm` in their published order: finite level, compact finiteness,
simultaneous center finiteness, and per-slice growth. Joint continuity, rational
left invariance and archimedean smoothness are already carried by the existing
`smoothRightAction` on `SmoothRationalFunctions`. No covariance or preservation
hypothesis remains in the theorem. The statement and its imported definitions
are unchanged, and the proof uses default heartbeats.

This is a derived implementation of compact-translation preservation in
Borel–Jacquet, *Automorphic forms and automorphic representations*, Corvallis I
(1979), section 1.5(1), printed page 190 / one-based PDF page 185, and the adelic
conditions and reduction in sections 4.2–4.3, printed page 195 / PDF page 190.
Both original pages were read. The proof follows the Library's actual
subrepresentations and its common slice-family formulation of center finiteness;
the displayed helper lemmas are internal consequences, rather than separately
numbered assertions from the source. Rank zero is included under the Library's
empty-matrix convention, without claiming a separate source discussion of
`GL_0`.

Registered original: `borel-jacquet-1979-automorphic`.
Path: `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`.
SHA256: `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
