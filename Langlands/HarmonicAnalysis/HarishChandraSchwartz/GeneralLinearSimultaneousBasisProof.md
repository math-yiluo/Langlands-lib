# Simultaneous basis from the standard general linear integral model

`Langlands.HarishChandraSchwartz.generalLinearSimultaneousBasis` proves
`GeneralLinearSimultaneousBasisStatement` for every nonarchimedean local
field \(F\), in either characteristic, and every natural rank \(N\).
[Statement](GeneralLinearSimultaneousBasisStatement.md)

## The argument

Fix \(F\), \(N\) and a generic cocharacter \(\nu\) of the diagonal torus
\(i : D_N \to \mathrm{GL}_{N,F}\). Let \(M\) be
`GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N)`: its group is
\(\mathrm{GL}_{N,\mathcal O_F}\) and its generic isomorphism is the
base-change isomorphism `GeneralLinear.baseChangeIso` of the general
linear group along \(\mathcal O_F \to F\). Its integral-point subgroup
`M.integralPoints` is the compact \(K\) of the statement.

The Lean proof applies the Library theorem
`CongruenceGL.simultaneousStandardBasisAt_integralPoints` to \(M\). Its
hypotheses are supplied as follows.

- The generic fibre is connected reductive by
  `GroupScheme.GeneralLinear.isConnectedReductiveStatement`.
- The diagonal torus is a maximal split torus by
  `GeneralLinear.isMaximalSplitTorus_diagonalTorus`.
- \(\nu\) is generic by hypothesis.
- Every cocharacter \(y\) of the diagonal torus lifts to \(M\). Let
  \(w = \) `cocharacterCoordEquiv (Fin N) F y` \(\in \mathbb Z^N\) be its
  integer weights, so \(y = \) `cocharacterOfWeights F w`. The lift is the
  diagonal cocharacter `diagonalCocharacter (Fin N) 𝒪[F] w` of
  \(\mathrm{GL}_{N,\mathcal O_F}\), \(t \mapsto \mathrm{diag}(t^{w_1},
  \dots, t^{w_N})\). By `cocharacterOfWeights_comp_diagonalTorus`, \(y\)
  followed by \(i\) is the diagonal cocharacter of \(\mathrm{GL}_{N,F}\)
  with weights \(w\). By `baseChangeCocharacter_diagonalCocharacter`, the
  base change of the integral diagonal cocharacter followed by the
  base-change isomorphism is that same cocharacter, which is the generic
  cocharacter `M.genericCocharacter` of the lift.

## The imported theorem on its subgroups

`CongruenceGL.simultaneousStandardBasisAt_integralPoints` works with the
congruence subgroups `M.congruenceSubgroupAt n`, \(n \ge 1\): the images
in \(\mathrm{GL}_N(F)\) of the kernels of reduction of the integral
sections of \(\mathrm{GL}_{N,\mathcal O_F}\) modulo
\(\mathfrak p_F^{\,n}\). They lie in \(K\), are compact, open and normal
in \(K\), and every neighbourhood of the identity contains one of them, by
`LocalFieldIntegralModel.congruenceNeighborhoodBasis_proof`. For each set
\(J\) of simple relative roots of the positive system of \(\nu\), each
congruence subgroup has the ordered opposite–Levi–radical decomposition
along the standard parabolic of \(J\) by
`hasIwahoriIntersectionDecomposition_congruenceSubgroupAt`, and satisfies
the contraction clauses for the standard split component of \(J\) by
`weakChamberContraction_congruenceSubgroupAt`. Both lemmas use the lifts
of the cocharacters to \(M\). The reduction
`simultaneousStandardBasisAt_of_cofinal_weakIwahoriNormalFamily` turns
this cofinal family into the whole `SimultaneousStandardBasisAt`
property: the common compact open normal basis of \(K\), the inherited
bases on the standard Levi subgroups, the compatible split components
and the `StandardParabolicBasisMember` clauses at every member.

## Source

The statement specializes David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, V.5.2(i)–(iv),
printed p. 123 (PDF p. 129), to \(\mathrm{GL}_N\) and its standard
integral model. Registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
