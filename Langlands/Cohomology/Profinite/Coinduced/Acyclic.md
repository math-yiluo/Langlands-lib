# Acyclicity of coinduced modules and dimension shifting

`Langlands/Cohomology/Profinite/Coinduced/Acyclic.lean`, namespace `Langlands.ProfiniteCohomology`.

The smooth coinduced module `discreteCoind k G X` of a compact group has no cohomology in positive
degree: an explicit contracting homotopy on locally constant cochains (shifting the first
variable) shows that every cocycle of positive degree is a coboundary. With the exact sequence
`0 → A → Ind(A) → Ind(A)/A → 0` this gives dimension shifting.

## Declarations

- `contractNth_zero_cons`, `contractNth_succ_cons`, `eventually_forall_cons_eq`: auxiliary facts
  on face maps and locally constant functions on `G^{n+1}`.
- `coindHomotopyApply`, `coindHomotopy`, `coindHomotopy_identity`: the contracting homotopy and
  the identity `d h + h d = id` it satisfies in positive degree.
- `isZero_cohomology_discreteCoind`: `H^{n+1}(G, Ind(X)) = 0`; `cohomologyZeroDiscreteCoindIso`:
  `H⁰(G, Ind(X)) ≅ X`.
- `coindδ A n : Hⁿ(G, Ind(A)/A) ⟶ H^{n+1}(G, A)` (the connecting map), an epimorphism, and an
  isomorphism for `n ≥ 1`; `cohomologyCoindCokernelIso A n : H^{n+1}(G, Ind(A)/A) ≅ H^{n+2}(G, A)`;
  `cokernelCohomologyMapCoindCokernelπIso`: `H¹(G, A)` is the cokernel of
  `H⁰(G, Ind(A)) → H⁰(G, Ind(A)/A)`.

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/CoinducedModules/Acyclic.lean` and
`CoinducedModules/CohomologyCoindCokernelIsoHom.lean` of the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Names are the source's.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §3, Proposition (1.3.7) and dimension shifting, p. 32
  (induced modules are cohomologically trivial). They work with a profinite group and with
  `Ind_G(A) = Map(G, A)`, on which `σ` acts by `(σx)(τ) = σ x(σ⁻¹τ)`; here `G` is compact and acts
  on `Ind(A)` by right translation.
