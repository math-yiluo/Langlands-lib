# Completeness of irreducible smooth representations

Author: Worker 138. Namespace `Langlands.Renard.Smooth`.

`heckeCompleteness` proves exactly the unchanged published `HeckeCompletenessStatement.{u,v}`: every nonzero element of the Haar Hecke algebra of a Hausdorff, locally compact, totally disconnected sigma-compact group acts nontrivially in some irreducible smooth complex representation with carrier in any independently prescribed universe.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, III.1.11, printed pp.64–65 / PDF pp.70–71; registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The theorem applies `heckeCompleteness_of_equivalence`, whose implemented proof is documented in the paired `RenardHeckeCompletenessReduction` module, to the independently proved `Langlands.Hecke.heckeNondegenerateModuleEquivalence`. This discharges the reduction's sole additional premise and adds no premise to the published completeness target.

The complete route uses only countability of the compact-open corner containing a nonzero test function `T`. The inversion-conjugation positive element `adjoint(T) * T` is nonzero and nonnilpotent. A non-left-invertible scalar shift in that corner is transferred to the full unitization by adding `1-e`. The simple quotient by a suitable maximal left ideal has a nonzero original Hecke action, and local units make it nondegenerate. The III.1.4 equivalence reconstructs an irreducible smooth representation. Nonvanishing of the positive element implies nonvanishing of `T` by multiplicativity. A countable-basis realization then moves the representation to the specified carrier universe while preserving its integrated action.

The supporting construction pairs explain the corner countability correction to the printed route, the actual unitization compression, additive simplicity, and carrier transport. The proof assumes neither countable dimension of the full Hecke algebra nor a countable identity-neighborhood basis. The statement's Lean/Markdown pair and all its imports remain unchanged.
