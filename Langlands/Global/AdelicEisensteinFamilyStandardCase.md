# The family comparison in standard position

Module `Langlands.Global.AdelicEisensteinFamilyStandardCase` proves
`FamilyRegularComparison.of_standard`.

## Statement

Assume `StandardEisensteinFamilyComparisonStatement` (module
`Langlands.Global.AdelicEisensteinStandardFamilyComparisonStatement`). Let `fam` be a standard
parabolic family of `G`, `I` and `Q` standard indices, `n` a rational point of the normalizer
of the maximal split torus (`normalizerPoints fam.i`), `c : M_Q → M_I` and
`proj : P_Q → M_Q` with `l_Q ≫ proj = 𝟙`, such that `(n, c)` is a Weyl conjugation from `P_I` to
`P_Q`, the Weyl class of `n` maps the simple roots in `I` into `Q`, and its inverse maps those
in `Q` into `I`. Let `K` be a maximal compact subgroup with Iwasawa coverage for `P_I`, `P_Q`
and `P_∅`, meeting every standard Levi in a maximal compact subgroup, and let `rho` be a closed
matrix embedding. Then `FamilyRegularComparison` holds, at all universes `v`, `w`, for the
standard presentations `⟨⟨T, i, ν, I, f I⟩, isCompatible I⟩` and
`⟨⟨T, i, ν, Q, f Q⟩, isCompatible Q⟩` of `P_I` and `P_Q`, the Levi projection `proj`, the Weyl
conjugation `(n, c)` and `K` (predicate of module
`Langlands.Global.AdelicEisensteinFamilyRegularComparison`).

## Proof

The family statement is formulated with families indexed by `Fin p` and `Fin k`; the predicate
allows arbitrary finite index types `Ix`, `Jx`. The proof transports the data along
`Fintype.equivFin Ix` and `Fintype.equivFin Jx`. The sums over `Ix` and `Jx` are rewritten as
sums over `Fin (card Ix)` and `Fin (card Jx)` by `Equiv.sum_comp`, both in the hypotheses and
in the conclusion.
