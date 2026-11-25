# Smooth coinduced modules

`Langlands/Cohomology/Profinite/Coinduced/Basic.lean`, namespace `Langlands.ProfiniteCohomology`.

For a compact topological group `G` and a `k`-module `X`, the locally constant maps `G → X`
with `G` acting by right translation form the smooth coinduced module `discreteCoind k G X`
(the module `M_G(X)` of Serre and `Ind_G(X)` of Neukirch–Schmidt–Wingberg, coinduced from the
trivial subgroup). Every
smooth representation embeds into the coinduced module of its underlying module, which gives the
short exact sequence used for dimension shifting.

## Declarations

- `eventually_forall_mul_eq`: a locally constant function on a compact group is invariant under
  right translation by every element of some neighbourhood of `1` (uniformly).
- `discreteCoindRep k G X`, `discreteCoind k G X`: the representation `(g • f)(x) = f (x g)` on
  `LocallyConstant G X` and the object of `Rep k G`; `isSmoothRep_discreteCoind`: it is smooth
  (for compact `G`).
- `coindEval`: evaluation at `1`; `invariantsDiscreteCoindEquiv`: the invariants of the
  coinduced module are the constant functions, i.e. `X`.
- `coindEmbedding A : A ⟶ discreteCoind k G A`, `a ↦ (g ↦ g • a)`, injective
  (`coindEmbedding_injective`, a monomorphism), with `coindEval` as left inverse.
- `coindEmbeddingRange`, `coindCokernel A` (the quotient, smooth), `coindCokernelπ`, and
  `coindShortComplex A`: the short exact sequence `0 → A → Ind(A) → Ind(A)/A → 0`
  (`coindShortComplex_shortExact`); `coindCokernelSection`: a `k`-linear section of the
  projection (`coindCokernelπ_coindCokernelSection`).

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/CoinducedModules.lean` of the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Names are the
source's, with `isDiscreteRep_*` → `isSmoothRep_*`.

## References

- J.-P. Serre, *Galois Cohomology* (English translation of *Cohomologie galoisienne*, Springer 1997;
  corrected printing 2002), chapter I, §2.5, p. 13 (`M_G^H(A)`, and `M_G(A)` for `H = {1}`, with
  `(g a*)(x) = a*(xg)`).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter I, §3, Definition (1.3.5) and Proposition (1.3.6), p. 31
  (`Ind_G(A)`), and the exact sequence `0 → A → Ind_G(A) → A₁ → 0`, p. 32. Their action on
  `Map(G, A)` is `(σx)(τ) = σ x(σ⁻¹τ)`, which gives a module isomorphic to the one here.
