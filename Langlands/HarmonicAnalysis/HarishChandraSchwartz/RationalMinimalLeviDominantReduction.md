# Compact dominant reduction for the full minimal-Levi chamber

This internal geometric adapter preserves the full actual minimal-Levi closed
chamber while relating it to dominant cocharacter uniformizer points. It is
derived from the existing structural covering and normalized valuation
interfaces for the use of Waldspurger (2003), Lemma VI.2.3, printed pp.299–301.
The registered source is `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The compact-reduction interface is internal derived content, not a new literal
statement attributed to the paper.

`HasCompactDominantMinimalLeviReduction` says that every point of that chamber
is `k₁ y(ϖ) k₂`, where both factors lie in one fixed compact subset of the
actual minimal Levi and all simple-root pairings of `y` are nonnegative.
The factors need not belong to a compact subgroup.

The proof uses only compactness of the supplied `K₀`, its existing
empty-index standard-Levi Cartan covering and the original connected-reductive,
maximal-split and generic-cocharacter data, with the ambient affine and
locally-of-finite-type instances already present in the decay target. The covering writes a point as
`k₁ f y(ϖ) k₂` with `f` in a fixed finite centralizer set. Compact factors have
zero `H₀`, so closed-chamber membership bounds the negative root coordinates of
`y` by the finitely many coordinates of `H₀(f)`. Every simple root pairs with
the generic cocharacter in a positive integer. One sufficiently large integral
multiple `c` of that cocharacter therefore makes `y + c` dominant for every
covered point. The fixed factor `(-c)(ϖ)` is absorbed into the left compact
factor. Finite unions of compact translates give the single compact set.

This proves a geometric reduction only. It uses no Xi upper or lower estimate
and supplies no analytic estimate for the final positive-decay theorem.
