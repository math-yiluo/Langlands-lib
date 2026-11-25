# Proof of the finiteness of `H₁(L_{κ(q)/k})` for geometrically regular algebras

## Main theorem

```
Langlands.CommutativeAlgebra.Popescu.geometricRegularityH1Finite :
    GeometricRegularityH1FiniteStatement.{u}
```

Take a field `k` of characteristic `p > 0`, a geometrically regular `k`-algebra `Λ` and a prime
`q` of `Λ`. Then `H₁(L_{κ(q)/k})` is a finite-dimensional `κ(q)`-vector space. The proof uses
only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

This follows the first sentence of the proof of Stacks, Smoothing Ring Maps, Lemma 16.11.2
(Tag 07FH): `dim H₁(L_{κ(q)/k}) < ∞` by More on Algebra, Proposition 15.36.1 (Tag 07E5).

## Declarations

- `geometricRegularityH1Finite_of (h : GeometricRegularityH1InjectiveStatement) :
  GeometricRegularityH1FiniteStatement` is the reduction to the injectivity in 07E5 (1) ⇒ (3).
  Write `A = Λ_q` and `K = κ(q)`.
  - By `h`, the map `H₁(L_{K/k}) → H₁(L_{K/A})` is injective.
  - `Λ` is Noetherian (first component of `GeometricallyRegular`), so `A` is Noetherian and the
    finite-type algebra `A → K` is of finite presentation
    (`Algebra.FinitePresentation.of_finiteType`).
  - Mathlib's instance for finitely presented algebras then makes `H₁(L_{K/A})` a finite
    `K`-module. Mathematically, `H₁(L_{K/A}) = 𝔪/𝔪²`.
  - A `K`-module that injects into a finite `K`-module is finite (`Module.Finite.of_injective`).
- `geometricRegularityH1Finite` is the main theorem. It applies `geometricRegularityH1Finite_of`
  to the published Library theorem
  `GeometricRegularityH1.geometricRegularityH1Injective : GeometricRegularityH1InjectiveStatement`,
  imported from `Langlands.CommutativeAlgebra.Popescu.GeometricRegularityH1InjectiveProof`.
