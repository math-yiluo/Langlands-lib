# Quaternionic symplectic groups of rank one over local fields

Authors: Worker 5197.

`Langlands.GroupScheme.Quaternionic.LocalSymplecticRankOneStatement.{u}` is a proposition
definition with arbitrary universe `u`. It states that the symplectic groups in family (iii)
of Prasad–Raghunathan (1985), §2, are simply connected, almost simple and of split rank one.
This module does not prove the proposition.

## Exact statement

For every `K : Type u` with `[Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]`, every `D : Type u` with `[DivisionRing D] [Algebra K D]
[Algebra.IsCentral K D] [FiniteDimensional K D]` and `Module.finrank K D = 4`, and every
`σ : FirstKindInvolution K D` with `Module.finrank K σ.symmetricSubspace = 3`: for every
`m : ℕ` with `[NeZero m]` and `m = 2 ∨ m = 3`, and every `H : Matrix (Fin m) (Fin m) D` with

- `σ.IsAntihermitian H`,
- `IsUnit H`, and
- `σ.wittIndex H = 1`,

the group scheme `G = σ.symplecticGroup H` over `Spec K` satisfies

`IsSimplyConnected G ∧ IsAlmostSimple G ∧ splitRank G = 1`.

These are all the data and premises. The characteristic of `K`, including residue
characteristic 2, is unrestricted. The instance `[NeZero m]` only supplies `Nonempty (Fin m)`,
which the reduced norm of `M_m(D)` in `symplecticGroup` needs; it follows from `m = 2 ∨ m = 3`.

## Meaning of the data

- `D` is a quaternion central division algebra over `K`: a central division algebra of
  dimension 4.
- `σ` is an involution of the first kind with `dim_K D^σ = 3` (module
  `Langlands.GroupScheme.Quaternionic.Involution`).
- `H` is the Gram matrix of a nondegenerate (`IsUnit H`) trace-valued `σ`-antihermitian form
  on `D^m` of rank `m` and Witt index 1 (module `Langlands.GroupScheme.Quaternionic.Forms`,
  which also explains the row-vector convention and its agreement with the sources' column
  convention).
- `σ.symplecticGroup H` is the special unitary group of this form: the reduced-norm-one
  subgroup scheme of its unitary group, a closed subgroup of `GL_1(M_m(D))` (module
  `Langlands.GroupScheme.Quaternionic.GroupSchemes`).
- `IsSimplyConnected` (`Langlands.GroupScheme.SimplyConnected.Basic`), `IsAlmostSimple`
  (`Langlands.GroupScheme.Reductive.AlmostSimple`, simplicity over `K`) and the `ℕ∞`-valued
  `splitRank` (`Langlands.GroupScheme.Rational.SplitTorus`) are the Library's notions, as in
  `Langlands.GroupScheme.LocalRankOneKneserTitsStatement`.

## Sources

- G. Prasad and M. S. Raghunathan, *On the Kneser–Tits problem*, Comment. Math. Helv. 60
  (1985), 107–121 (`prasad-raghunathan-1985-kneser-tits`), §2, printed p. 111 / PDF p. 6.
  The source lists the absolutely simple, simply connected `K`-groups of `K`-rank 1 over a
  nonarchimedean local field `K`. Family (iii) contains "the symplectic group of a
  σ-antihermitian form of rank 2 or 3 and Witt index 1; where σ is an involution of the
  quaternion central division algebra D over K such that the dimension of D^σ, the space of
  symmetric elements, is 3". The listed groups are simply connected, absolutely simple
  (hence simple over `K`, which is `IsAlmostSimple`) and of `K`-rank 1, which is
  `splitRank G = 1`. The source works in arbitrary characteristic (classification by Kneser
  in characteristic zero and by Bruhat–Tits in general).
- J. Tits, *Classification of algebraic semisimple groups*, Proc. Sympos. Pure Math. 9 (1966),
  33–62 (`tits-1966-classification-algebraic-semisimple`), Table II, type `C_n`, printed
  p. 56 / PDF p. 61. These groups are the "special unitary group SU_{2n/d}(D, h)" for
  `d = 2`, absolute rank `n = m`, relative rank `r` equal to the Witt index, and index
  `C^{(2)}_{n,r}`. The p-adic line of the table reads "d = 2 and n = 2r or 2r − 1". With
  `d = 2` the drawn index has distinguished vertices `d, 2d, …, rd`, so `rd ≤ n`, and
  `n = 2r − 1` is impossible. The value `2r + 1` is consistent with PR's ranks 2 and 3 for
  `r = 1`, so the line is read as a misprint for "n = 2r or 2r + 1". The statement follows PR.
- J. Tits, *Groupes de Whitehead de groupes algébriques simples sur un corps*, Séminaire
  Bourbaki 505 (1977) (`tits-1977-whitehead-bourbaki-505`), 1.1.5, printed p. 220 / PDF p. 4,
  concerns forms of type `C_n` (cited by PR as [8]).

The statement keeps PR's exact family (rank 2 or 3, Witt index 1). This is the case needed by
`Langlands.GroupScheme.LocalRankOneKneserTitsStatement` through the classification of
rank-one groups over local fields.
