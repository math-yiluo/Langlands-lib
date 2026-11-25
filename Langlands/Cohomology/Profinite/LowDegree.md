# Cohomology in degree zero

`Langlands/Cohomology/Profinite/LowDegree.lean`, namespace `Langlands.ProfiniteCohomology`.

## Declarations

- `invariantsToCochains₀ A`: an invariant vector as a constant `0`-cochain.
- `shortComplexH0 A`, `shortComplexH0_exact`: `0 → A^G → C⁰(G, A) → C¹(G, A)` is exact (and the
  first map is injective): a `0`-cochain is a cocycle exactly when its value is `G`-invariant.
- `cocyclesIso₀ A : cocycles A 0 ≅ A^G`, `zeroIso A : cohomology A 0 ≅ A^G`: `H⁰(G, A)` is the
  module of invariants.

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/ContinuousCochains/Functoriality.lean`
(section `H0`) of the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository
has no licence file; its text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`). Source name `H0Iso` → `zeroIso`; the rest unchanged.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §2, p. 15 (`H⁰(G, A) = A^G`).
