# Hilbert functions of relative effective divisors on geometric fibres (proof)

Authors: Worker 5705.

The module `Langlands.AlgebraicGeometry.Modules.ProjectiveRelativeDivisorFibreHilbertProof` proves

```lean
theorem projectiveRelativeDivisorFibreHilbert :
    ProjectiveRelativeDivisorFibreHilbertStatement.{u}
```

The statement concerns a relative effective Cartier divisor `E` on a projective flat family
`X_B ⟶ Spec B` over a noetherian ring. For all large `n`, the geometric
`dim_k H⁰(E_k, 𝒪_E(n))` equals `χ(𝒪(n)_t) − χ(K(n)_t)` on the fibre over the image point `t`.

## Proof

The theorem applies the reduction
`Picard.RelativeDivisorFibreHilbert.projectiveRelativeDivisorFibreHilbert_of_twistCohomology`
(module `Langlands.AlgebraicGeometry.Picard.RelativeDivisorFibreHilbert`) to
`projectiveFibreTwistCohomology`, the proof of `ProjectiveFibreTwistCohomologyStatement`. Only
the first clause of that statement is used: uniform vanishing of higher fibre cohomology of large
twists.

The reduction works on the fibre `X_t` (see the helper module's Markdown for details).

1. The divisor sequence `0 → K → 𝒪 → i_* 𝒪_E → 0` stays short exact after base change to `X_t`,
   because `E` is flat over `Spec B`. This uses the monomorphism of the proof of
   `RelativeEffectiveDivisorBaseChangeStatement`.
2. The sequence stays short exact after twisting by the line bundle.
3. Since `H¹(K(n)_t) = 0`, `h⁰` of the twisted sequence is additive. Vanishing of all higher
   cohomology turns the two outer `h⁰` into Euler characteristics.
4. `h⁰` of the third term is `h⁰(E_t, 𝒪_E(n))`, by the base-change and projection isomorphisms.
   The helper `GeometricFibreSectionsDim.geomFibreH0Finrank_eq` identifies it with
   `geomFibreH0Finrank`, by a perfect-model base change along `κ(t) → k`.

Sources: S. L. Kleiman, *The Picard scheme*, proof of Theorem 4.8, p.30 (literature id
`kleiman-2005-picard-scheme-arxiv-math0504020v1`). Field extension invariance follows
D. Mumford, *Abelian Varieties*, Chapter II, §5, Corollary 5, pp.53–54 (literature id
`mumford-abelian-varieties-chapter-ii-scan`).

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
