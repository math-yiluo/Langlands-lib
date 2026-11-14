# Geometric regularity and the map `H₁(L_{κ/k}) → 𝔪/𝔪²`

`Langlands.CommutativeAlgebra.Popescu.GeometricRegularityH1InjectiveStatement` (universe `u`). Let `k`
be a field of characteristic `p > 0` (`[Fact p.Prime] [CharP k p]`) and `Λ` a `k`-algebra that is
geometrically regular over `k` (Library `GeometricallyRegular k Λ` from
`Langlands.CommutativeAlgebra.RegularRingMaps`, which includes that `Λ` is Noetherian). Let `q` be a
prime of `Λ`, `A = Λ_q` and `K = κ(q) = q.ResidueField`. Then the canonical map
`Algebra.H1Cotangent.map k A K K : H₁(L_{K/k}) → H₁(L_{K/A})` is injective.

## Source

Stacks Project, More on Algebra, Proposition 15.36.1 (Tag 07E5), in the registered snapshots
`stacks-geometric-regularity-07E5-07E6-2026-11-14`. Let `k` be a field of characteristic `p > 0`
and `(A, 𝔪, K)` a Noetherian local `k`-algebra. Then (1) "`A` is geometrically regular over `k`"
is equivalent to (3) "`A` is regular and the canonical map `H₁(L_{K/k}) → 𝔪/𝔪²` is injective". This
statement records the injectivity part of (1) ⇒ (3), applied to `A = Λ_q`.

## Encoding

- `H₁(L_{K/A}) = 𝔪/𝔪²` for `K = A/𝔪`, as used in the proof of 07E5. The canonical map in the
  source is the map `H₁(L_{K/k}) → H₁(L_{K/A})` of the Jacobi–Zariski sequence for `k → A → K`,
  which is Mathlib's `Algebra.H1Cotangent.map k A K K`. Stacks identifies `H₁(L_{−})` with `H₁` of
  the naive cotangent complex (Tag 08RA), which is `Algebra.H1Cotangent`.
- The statement is phrased at a prime `q` of a geometrically regular `Λ`. `Λ_q` is geometrically
  regular over `k` as a localization of `Λ`, so this is (1) ⇒ (3) for `A = Λ_q`.
- Regularity of `A` (the other half of (3)) is not part of the statement.
- All types are in one universe `u`.
