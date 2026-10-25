# Row action on Schwartz–Bruhat functions

This internal construction bundles the pointwise row action already used by
`Langlands.RankinSelberg.EqualRankTrilinearUniquenessStatement` and
`Langlands.HarmonicAnalysis.RowTestSmoothStatement`. It applies to every
natural rank, including zero, over any topological field whose ring operations
are continuous. It introduces no assumptions about representations, measures,
or Fourier transforms.

For an invertible matrix `g`, `rowHomeomorph g` sends a row vector `x` to `xg`.
Its inverse is right multiplication by `g⁻¹`. Matrix associativity and the unit
identities prove both inverse laws; continuity follows from continuity of
finite matrix multiplication.

`rowTranslate g` is the existing `Hecke.TestFunction.pullback` applied to this
homeomorphism. Thus it is a complex linear equivalence on the actual space of
compactly supported locally constant functions, with
`rowTranslate g Φ x = Φ (xg)`. The convention gives
`rowTranslate (g*h) Φ = rowTranslate g (rowTranslate h Φ)`.
`rowSchwartzRepresentation` bundles these identities as a representation.

`rowEvaluationAtZero` is the linear functional `Φ ↦ Φ(0)`. Its value is preserved
by every row translate because `0g = 0`. Its kernel, `rowVanishingAtZero`, is
therefore a subrepresentation: it is precisely the actual test functions
vanishing at zero. Finally `eq_rowTranslate_iff` identifies any test function
specified by the pointwise row-translation equation with the bundled action.

The definitions are elementary adapters derived from the published Library's
Schwartz–Bruhat space, general linear group, and homeomorphism pullback. No
external theorem is asserted here. In particular this module does not identify
the kernel with compact induction or prove trilinear uniqueness.
