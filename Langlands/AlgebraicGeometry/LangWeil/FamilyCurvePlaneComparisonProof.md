# Proof of the plane-model comparison for curve families

Lean module: `Langlands.AlgebraicGeometry.LangWeil.FamilyCurvePlaneComparisonProof`.

Authors: Worker 189 and Worker 191 (Task 5581).

The theorem `Langlands.AlgebraicGeometry.LangWeil.familyCurvePlaneComparison` proves the
unchanged published statement
`Langlands.AlgebraicGeometry.LangWeil.FamilyCurvePlaneComparisonStatement.{u}`. Its meaning
and provenance (Tao, *The Lang–Weil bound*, 2012, Section 2; Lang and Weil, 1954, p.819) are
documented in the statement's paired Markdown.

The proof is one line: it applies the reduction
`CurvePlane.familyCurvePlaneComparison_of_core` (module `FamilyCurvePlaneReduction`) to the
affine core `CurvePlane.affineCurvePlaneComparison` (module `AffineCurvePlaneComparison`).

## Outline of the implemented proof

1. Affine core (`AffineCurvePlaneComparison`, with helper modules `CurvePlaneZeroDimensional`,
   `CurvePlaneRadicialPoints`, `CurvePlaneFibrePoints`, `CurvePlanePolynomial`; Worker 191,
   partly building on drafts by Worker 189). For a Noetherian domain `A` with fraction
   field `K` and a finite type `A`-algebra `R` whose geometric generic fibre has prime
   nilradical and whose generic fibre has dimension one, there are `a ≠ 0` in `A` and `B`
   such that, over every finite field `κ` with `a ≠ 0` in `κ` and `B < #κ`, some plane
   polynomial irreducible over `AlgebraicClosure κ`, with both degrees between `1` and `B`,
   has a zero count within `B` of `#(R →ₐ[A] κ)`. The proof uses the Library's uniform
   hypersurface model of the generic fibre, a radicial comparison of points, and root counts
   for the exceptional loci; see `AffineCurvePlaneComparison.md`.
2. Charts (`CurvePlaneCharts`). Rings of affine charts of the family inherit finite type,
   geometric irreducibility and pure dimension one of their fibres, and the field-valued
   points are counted by one chart up to finitely many principal closed pieces.
3. Local step (`FamilyCurvePlaneReduction.exists_prime_bound`). Over an affine open `S₀` with
   Noetherian ring `Γ(S, S₀)` and a prime `p`, the core is applied to `Γ(S, S₀) ⧸ p` and a
   chart meeting the fibre over `p`. Irreducibility and dimension one of the fibre give each
   other chart a principal closed piece with zero-dimensional fibre over `p`, whose points are
   uniformly bounded near `p` (`CurvePlaneZeroDimensional`).
4. Noetherian induction (`CurvePlaneNoetherianInduction`) makes the bound uniform over
   `S₀`, and a finite affine cover of the compact base gives one bound `B`, made positive by
   adding `1`.

The hypothesis `FamilyPointUpperBoundStatement` of the target is not used. All other
hypotheses are used: local finite type of the base over the integers (Noetherian sections),
compactness of the base (finite affine cover), and local finite type, quasi-compactness,
geometric irreducibility and pure fibre dimension one of the morphism.
