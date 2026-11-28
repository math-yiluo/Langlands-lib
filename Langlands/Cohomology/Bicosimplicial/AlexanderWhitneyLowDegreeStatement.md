# Low-degree cohomology of the Alexander–Whitney map

`Langlands.Cohomology.Bicosimplicial.AlexanderWhitneyLowDegreeQuasiIsoStatement`
is a proposition for every commutative ring \(R\), every bicosimplicial
\(R\)-module \(F\), and each natural number \(n\le 2\). It asserts that
`alexanderWhitney F` induces an isomorphism
\[
H^n(\operatorname{Tot} F)\longrightarrow H^n(\operatorname{diag} F)
\]
on the cohomology of the alternating-coface complexes. The underlying
cochain map is the front and back comparison, expressed on each summand
by `ιTotal_alexanderWhitney_f`. [The Alexander–Whitney cochain map](AlexanderWhitney.md)

The Lean predicate is `QuasiIsoAt (alexanderWhitney F) n`, equivalent by
`quasiIsoAt_iff_isIso_homologyMap` to the induced cohomology morphism being
an isomorphism. The two complexes have the full nonnegative grading, so
in degree two the cohomology uses the differentials to degree three.

## Sources

- S. Eilenberg and J. A. Zilber, *On Products of Complexes*, Amer. J.
  Math. 75 (1953), 200–204, §§1–3, establishes the natural chain
  comparison underlying the cosimplicial version. The retained source
  is `eilenberg-zilber-1953-products`, SHA-256
  `a184c3f85d47e53322c985f62a5bc0244041f1f556a21a28d137a67689b9280e`.
  [Original article](https://doi.org/10.2307/2372629)
- L. Grunenfelder and M. Mastnak, *Cohomology of abelian matched pairs
  and the Kac sequence*, J. Algebra 276 (2004), 706–736, Appendix A.2,
  Theorem A.3 on p. 733 and Appendix A.3 on pp. 734–735. The theorem
  compares cohomology for bicosimplicial objects in an abelian category
  with enough injectives, and Appendix A.3 identifies the isomorphism
  with the map induced by the cosimplicial Alexander–Whitney formula.
  The Lean proposition specializes to \(R\)-modules and degrees zero
  through two. The retained source is
  `grunenfelder-mastnak-2004-kac-sequence`, SHA-256
  `49439107f5b06bbe105453e6eeef4651521f8ae75f967a4246d4e675686b863a`.
  [Journal article](https://doi.org/10.1016/j.jalgebra.2003.07.024)
