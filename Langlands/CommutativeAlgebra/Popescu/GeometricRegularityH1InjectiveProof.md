# Proof of `GeometricRegularityH1InjectiveStatement` (Stacks 07E5, (1) ⇒ (3))

## Main theorem

```
GeometricRegularityH1.geometricRegularityH1Injective :
    GeometricRegularityH1InjectiveStatement.{u}
```

Take a field `k` of characteristic `p > 0`, a geometrically regular `k`-algebra `Λ` and a prime
`q` of `Λ`. Write `A = Λ_q` and `K = κ(q)`. The theorem states that the canonical map
`H₁(L_{K/k}) → H₁(L_{K/A})` is injective. Here `H₁(L_{K/A}) = 𝔪/𝔪²`. The proof uses only the
standard axioms.

The Stacks proof of More on Algebra, Proposition 15.36.1 (Tag 07E5) has two steps:

- (1) ⇒ (4), which is Faltings' argument. The Library proves it as
  `Faltings.geometricRegularityKaehlerInjective : GeometricRegularityKaehlerInjectiveStatement`.
  This module imports it from `GeometricRegularityKaehlerInjectiveProof`.
- (4) ⇒ (3), which is the equivalence (3) ⇔ (4) used in one direction. This module proves it as
  `geometricRegularityH1Injective_of`.

The main theorem applies `geometricRegularityH1Injective_of` to
`Faltings.geometricRegularityKaehlerInjective`.

The Library module `FieldH1CotangentTools` supplies `subsingleton_h1Cotangent_of_perfectField`:
`H₁(L_{K/F}) = 0` for a perfect field `F`. It comes from the proof of
`FieldH1CotangentInjectiveStatement` (Stacks 07E2).

## Reused naturality declarations

The following declarations are reused from namespace `Faltings` in
`FaltingsRows`; this module introduces no second copy of them.

- `defaultHom_base_toAlgHom`: the default hom of canonical presentations `S[T] → S'[T]` equals
  `MvPolynomial.map (algebraMap S S')`. The proof is by induction on the polynomial.
- `baseMap R S S' T`: the `T`-linear map `T ⊗_S Ω_{S/R} → T ⊗_{S'} Ω_{S'/R}` given by
  `t ⊗ ω ↦ t ⊗ ω|_{S'}`.
- `δAux_map` and `δ_map_base`: the Jacobi–Zariski connecting map
  `δ : H₁(L_{T/S}) → T ⊗_S Ω_{S/R}` is natural in the middle ring:
  `δ_{S'}(H1Cotangent.map S S' T T x) = baseMap (δ_S x)`.
  The proof computes `δ` with Mathlib's `δ_eq_δAux` and inducts on polynomials.
- `aeval_map_eq_zero`: mapping the coefficients of a relation of `T` over `S` to `S'` gives a
  relation of `T` over `S'`.
## Declarations in `GeometricRegularityH1`

- `map_int_eq_zero`: for fields `k → K` of characteristic `p`, the map `H₁(L_{K/ℤ}) → H₁(L_{K/k})`
  is zero.
  - The canonical presentations give homs `ℤ → 𝔽_p → k`. So the map factors through
    `H₁(L_{K/𝔽_p})` (`Extension.H1Cotangent.map_comp`, `map_eq`).
  - `H₁(L_{K/𝔽_p}) = 0` because `𝔽_p` is perfect.
- `h1Cotangent_map_injective_of_kaehler`: the abstract (4) ⇒ (3) step for maps `k → A → K` over a
  base ring `R₀`.
  - Hypothesis: the map `H₁(L_{K/R₀}) → H₁(L_{K/k})` is zero.
  - Then `δ : H₁(L_{K/k}) → K ⊗_k Ω_{k/R₀}` is injective, by Jacobi–Zariski exactness
    (`exact_map_δ`).
  - Let `x ∈ H₁(L_{K/k})` map to `0` in `H₁(L_{K/A})`. By naturality, `baseMap (δ x) = 0`.
  - By the injectivity hypothesis (4), `δ x = 0`, hence `x = 0`.
- `geometricRegularityH1Injective_of`: (4) ⇒ (3) at a prime of a geometrically regular algebra.
  It applies the abstract lemma with `R₀ = ℤ`, `A = Λ_q` and `K = κ(q)`, using `map_int_eq_zero`
  and the hypothesis `h : GeometricRegularityKaehlerInjectiveStatement`.
- `geometricRegularityH1Injective`: the main theorem.

The base ring stays general in `h1Cotangent_map_injective_of_kaehler`. This avoids conflicts
between different `ℤ`-algebra instances, such as those on localizations and on residue fields.

## Authorship

The proof was drafted by Worker 5698 (draft of Task 6744). Worker 720 added the final assembly.
