# The Alexander–Whitney cochain map

Let \(R\) be a commutative ring and \(F\colon \Delta\times\Delta\to
\mathrm{Mod}_R\) a bicosimplicial module, where \(\Delta\) is `SimplexCategory`.
The module `Langlands.Cohomology.Bicosimplicial.AlexanderWhitney` constructs
three complexes with the full nonnegative grading.

- `diagonalComplex F` has term \(F([n],[n])\) in degree \(n\). The
  differential in `diagonalComplex_d` is the signed sum of the
  simultaneous cofaces \(F(\delta_k,\delta_k)\).
- `bicomplex F` has term \(F([p],[q])\) in bidegree \((p,q)\).
  Applying the alternating-coface complex functor first in the second
  variable and then in the first gives the two commuting differentials.
  The lemmas `bicomplex_d_f` and `bicomplex_X_d` identify them with the
  alternating sums of \(F(\delta_i,\mathrm{id})\) and
  \(F(\mathrm{id},\delta_j)\), respectively.
- `totalComplex F` is the Mathlib total complex of `bicomplex F`, with
  degree-\(n\) term \(\bigoplus_{p+q=n} F([p],[q])\).
  The sign lemmas `ε₁_up_ℕ` and `ε₂_up_ℕ` identify the differential from
  the \((p,q)\) summand with \(d_1+(-1)^p d_2\), with each term included
  in its target summand. [Tensor signs for nonnegative cochains](../ModuleComplex/TensorSignsUpNat.md)

The cochain map `alexanderWhitney F` goes from the total complex to the
diagonal complex. Its degree-\(n\) component is defined by the coproduct
universal property. By `ιTotal_alexanderWhitney_f`, its restriction to
the \((p,q)\) summand for \(p+q=n\) is `awComponent`, namely
\(F(\alpha,\beta)\), where \(\alpha\colon[p]\to[n]\) sends \(i\) to \(i\)
and \(\beta\colon[q]\to[n]\) sends \(j\) to \(p+j\). These are the front
and back inclusions with common vertex \(p\).

The cochain-map proof in `alexanderWhitney` checks the differential
identity on each summand. In `sum_front_back`, splitting the diagonal
cofaces at \(k=p\) matches \(k\le p\) with the horizontal cofaces up to
\(p\), and \(k\ge p+1\) with the vertical cofaces \(j=k-p\), with sign
\((-1)^p(-1)^j\). The remaining horizontal coface at \(p+1\) and vertical
coface at \(0\) give the same pair of simplex maps. Their coefficients
\((-1)^{p+1}\) and \((-1)^p\) cancel. Distributing composition over the
sums gives `awComponent_comp_d`.

For a natural transformation of bicosimplicial modules, the naturality
square on each summand is the square for the pair \((\alpha,\beta)\).
The lemma `alexanderWhitney_naturality` assembles these squares to prove
naturality of the cochain map. The definition `alexanderWhitneyNatTrans`
packages it as a natural transformation from `totalComplexFunctor R` to
`diagonalComplexFunctor R`.

## Sources

- S. Eilenberg and J. A. Zilber, *On Products of Complexes*, Amer. J.
  Math. 75 (1953), 200–204, §§1–3. Section 1 compares the diagonal and
  signed tensor chain complexes of a pair of simplicial sets. Section 2
  constructs the natural chain equivalence by acyclic models and points
  to explicit formulas. Section 3 applies the comparison to product
  covers. The retained source is `eilenberg-zilber-1953-products`,
  SHA-256 `a184c3f85d47e53322c985f62a5bc0244041f1f556a21a28d137a67689b9280e`.
  [Original article](https://doi.org/10.2307/2372629)
- L. Grunenfelder and M. Mastnak, *Cohomology of abelian matched pairs
  and the Kac sequence*, J. Algebra 276 (2004), 706–736, Appendix A.2,
  pp. 732–733, and Appendix A.3, pp. 734–735. The formula for \(g_{p,q}\)
  in Appendix A.3 composes cofaces omitting the last vertex in the first
  direction and cofaces omitting the first vertex in the second. These
  composites are the inclusions \(\alpha\) and \(\beta\) above. The
  retained source is `grunenfelder-mastnak-2004-kac-sequence`, SHA-256
  `49439107f5b06bbe105453e6eeef4651521f8ae75f967a4246d4e675686b863a`.
  [Journal article](https://doi.org/10.1016/j.jalgebra.2003.07.024)
- The related AxiomMath chain construction `AlgebraicTopology.alexanderWhitney`
  compares the degreewise tensor of two simplicial objects to the total
  tensor complex. The retained source is `axiommath-stacks-c496df0`,
  tree SHA-256 `0054608470227f8d8d704adcb630454f3ec00a5b6cd3d521134e94472f40898f`,
  file `StacksFrontier/AlgebraicTopology/AlexanderWhitney.lean`.
  [AxiomMath source](https://github.com/AxiomMath/Stacks/blob/c496df0d9beea9deaeabcea8492605f9a0a2313b/StacksFrontier/AlgebraicTopology/AlexanderWhitney.lean)
