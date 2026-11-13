# Exact proof of Springer's split adelic fundamental-set statement

Author: Worker 306.

`Langlands.Global.AdelicSiegelFactors.splitAdelicFundamentalSetProof` proves
exactly `SplitAdelicFundamentalSetStatement.{u}`, defined in
`Langlands.Global.AdelicSplitFundamentalSet`, for arbitrary universe `u`.
The proof term is the imported theorem `splitAdelicFundamentalSet` from
`Langlands.Global.AdelicSplitFundamentalSetFromCover`. This module records
that result as an exact-target proof without changing the statement.

For every number field and every affine finite-type connected reductive
group scheme with an actual Siegel setup whose split torus is also a
maximal torus, the conclusion supplies a compact set `C` in the actual
norm-one adelic group and a positive unit `c`. Every norm-one adelic point
has the factorization

`g = x · i(s) · ι_P(p) · rational(q)`,

where `x ∈ C`, `s` is a full adelic torus point whose image is norm-one,
`p` belongs to the minimal parabolic's own norm-one subgroup, and every
simple-root character norm of `s` is at most `c`. The norm-one condition
on `p` uses all rational characters of the parabolic.

The imported proof first supplies the split rank-one rational-orbit height
bound from `RepresentationGrowth.splitRankOneParabolicRationalOrbitHeightBound`
in `SplitRankOneAdelic`. Its split root-Levi reduction gives all simple-root
height bounds. Adapted maximal-parabolic representations and successive
minima over preceding intersections of rational stabilizers then produce
a weak lower-chamber factorization. The compact factor comes from
`IsSiegelAlgebraicSetup.hasCompactNormOneParabolicCover` in
`AdelicParabolicCompactCover`: a compact set `Ω` inside the ambient norm-one
group with `P(𝔸) · Ω = G(𝔸)`. Compact height transport uses `Ω⁻¹`.

Applying this factorization to `g⁻¹` and inverting gives the displayed
right-action factorization. Its compact set is the set of norm-one points
lying in `Ω⁻¹`; its upper bound is the inverse of the lower-chamber
threshold. The inverted Levi and unipotent factors belong to the
parabolic's own norm-one subgroup by functoriality of character kernels
and triviality of unipotent characters.

The imported result has no additional proof premise. It retains all
number fields, actual scheme-point carriers and maps, and empty simple-root
systems, including split tori. Its proof uses the split rank-one and compact
parabolic-cover results; it does not use general anisotropic compactness or
the nonsplit chamber-reduction theorem. No Iwasawa existence statement is
needed.

This is a derived proof of the actual-scheme formulation of Springer,
*Reduction theory over global fields* (1994), §2.1 (F), printed pp.211–212,
and §§3.2–3.3, printed pp.214–215. Springer proves split (F) before the
Galois-descent compactness and general (F) arguments; the imported proof
keeps that dependency direction and works directly over arbitrary number
fields. The complete paper was consulted. The registered source is
`springer-1994-reduction-global-fields`, SHA-256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`.
The Library's Springer errata note explains the preceding-stabilizer
indexing and root-weight issues addressed by the imported height arguments.
