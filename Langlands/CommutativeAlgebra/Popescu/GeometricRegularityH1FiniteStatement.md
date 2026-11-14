# Finiteness of `H₁(L_{κ(q)/k})` for geometrically regular algebras

`Langlands.CommutativeAlgebra.Popescu.GeometricRegularityH1FiniteStatement` (universe `u`). Let
`k` be a field of characteristic `p > 0` (`[Fact p.Prime] [CharP k p]`) and `Λ` a `k`-algebra that
is geometrically regular over `k` (the Library predicate `GeometricallyRegular k Λ` from
`Langlands.CommutativeAlgebra.RegularRingMaps`, which includes that `Λ` is Noetherian). Then for every
prime `q` of `Λ` the `κ(q)`-vector space `H₁(L_{κ(q)/k})` is finite-dimensional:
`Module.Finite q.ResidueField (Algebra.H1Cotangent k q.ResidueField)`.

## Source

Stacks Project, More on Algebra, Proposition 15.36.1 (Tag 07E5), in the registered snapshots
`stacks-geometric-regularity-07E5-07E6-2026-11-14`: for a Noetherian local `k`-algebra `(A, 𝔪, K)`,
`k` of characteristic `p > 0`, condition (1) "`A` is geometrically regular over `k`" implies
(3) "`A` is regular and the canonical map `H₁(L_{K/k}) → 𝔪/𝔪²` is injective". Since `𝔪/𝔪²` is
finite-dimensional, `H₁(L_{K/k})` is finite-dimensional. Apply this to `A = Λ_q`, which is
geometrically regular over `k` as a localization of `Λ`. This is the first sentence of the proof of
Smoothing Ring Maps, Lemma 16.11.2 (Tag 07FH; source `stacks-artin-axioms-approximation-2026-11-06`,
smoothing.pdf, printed p. 27): "Note that `dim H₁(L_{κ(q)/k}) < ∞` by More on Algebra,
Proposition 36.1."

## Encoding

- `Algebra.H1Cotangent k K` is Mathlib's `H¹` of the naive cotangent complex of `K` over `k`. It
  agrees with `H₁(L_{K/k})` (Stacks Tag 08RA).
- The statement is phrased at a prime `q` of a geometrically regular `Λ`. This is the form used in
  Lemma 16.11.2; the local ring `Λ_q` does not appear.
- All types are in one universe `u`.
