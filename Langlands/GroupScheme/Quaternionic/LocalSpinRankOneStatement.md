# Quaternionic spin groups of rank one over local fields

Authors: Worker 5197.

`Langlands.GroupScheme.Quaternionic.LocalSpinRankOneStatement.{u}` is a proposition definition
with arbitrary universe `u`. It states that the quadratic forms in family (iii) of
Prasad–Raghunathan (1985), §2, have spin groups, and that these spin groups are simply
connected, almost simple and of split rank one. This module does not prove the proposition.

## Exact statement

For every `K : Type u` with `[Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]`, every `D : Type u` with `[DivisionRing D] [Algebra K D]
[Algebra.IsCentral K D] [FiniteDimensional K D]` and `Module.finrank K D = 4`, and every
`σ : FirstKindInvolution K D` with `Module.finrank K σ.symmetricSubspace = 3`: for every
`m : ℕ` with `m = 4 ∨ m = 5`, and every `q : σ.QuadraticForms (Fin m)` with

- `σ.IsNondegenerateQuadratic q`, and
- `σ.quadraticWittIndex q = 1`,

both of the following hold.

1. *Existence.* There are a group scheme `S` over `Spec K` and a homomorphism
   `π : S ⟶ σ.isometryGroup q` with `σ.IsSpinCover q π`.
2. *Properties.* For every group scheme `S` over `Spec K` and every
   `π : S ⟶ σ.isometryGroup q` with `σ.IsSpinCover q π`,
   `IsSimplyConnected S ∧ IsAlmostSimple S ∧ splitRank S = 1`.

These are all the data and premises. The characteristic of `K`, including residue
characteristic 2, is unrestricted.

## Meaning of the data

- `D` is a quaternion central division algebra over `K`, and `σ` is an involution of the first
  kind with `dim_K D^σ = 3` (module `Langlands.GroupScheme.Quaternionic.Involution`).
- `q` is a `σ`-quadratic form on `D^m` in the sense of Tits: an element of
  `M_m(D) ⧸ {x - ᵗx^σ}`. It is nondegenerate (its polar Gram matrix `Q + ᵗQ^σ` is invertible)
  and has Witt index 1 (the largest totally singular subspace has `D`-dimension 1). See module
  `Langlands.GroupScheme.Quaternionic.Forms`, which also explains the row-vector convention.
  "Rank" is the number of variables `m`.
- `σ.isometryGroup q` is the isometry group scheme `O(q)` over `Spec K`, a closed subgroup of
  `GL_1(M_m(D))`. `σ.IsSpinCover q π` says that `S` is simply connected, that `O(q)` is smooth,
  and that `π` is a central isogeny onto the identity component `O(q)⁰`
  (`σ.connectedIsometryGroup q`) followed by the inclusion `O(q)⁰ ⊆ O(q)`. See module
  `Langlands.GroupScheme.Quaternionic.GroupSchemes` for the definition and for why spin groups
  are characterized by this predicate rather than constructed.
- `IsSimplyConnected` (`Langlands.GroupScheme.SimplyConnected.Basic`), `IsAlmostSimple`
  (`Langlands.GroupScheme.Reductive.AlmostSimple`, simplicity over `K`) and the `ℕ∞`-valued
  `splitRank` (`Langlands.GroupScheme.Rational.SplitTorus`) are the Library's notions, as in
  `Langlands.GroupScheme.LocalRankOneKneserTitsStatement`.

The conjunct `IsSimplyConnected S` in part 2 repeats a field of `IsSpinCover`; it is kept so
that the conclusion lists the three properties of the task in the same form as the symplectic
statement. Part 1 also asserts that `O(q)` is smooth, because smoothness is a field of
`IsSpinCover`. Part 2 alone would hold vacuously if no spin group existed; part 1 excludes
this.

## Sources

- G. Prasad and M. S. Raghunathan, *On the Kneser–Tits problem*, Comment. Math. Helv. 60
  (1985), 107–121 (`prasad-raghunathan-1985-kneser-tits`), §2, printed p. 111 / PDF p. 6.
  The source lists the absolutely simple, simply connected `K`-groups of `K`-rank 1 over a
  nonarchimedean local field `K`. Family (iii) contains "the spin group of a σ-quadratic form
  of Witt index 1 and rank 4 or 5 ...; where σ is an involution of the quaternion central
  division algebra D over K such that the dimension of D^σ, the space of symmetric elements,
  is 3". The listed groups are simply connected, absolutely simple (hence simple over `K`,
  which is `IsAlmostSimple`) and of `K`-rank 1, which is `splitRank S = 1`. The source works in
  arbitrary characteristic (classification by Kneser in characteristic zero and by
  Bruhat–Tits in general).
- J. Tits, *Groupes de Whitehead de groupes algébriques simples sur un corps*, Séminaire
  Bourbaki 505 (1977) (`tits-1977-whitehead-bourbaki-505`).
  - Introduction, printed p. 218 / PDF p. 2: a universal cover of `G` is `p : G̃ → G` with
    "G̃ simplement connexe et p une isogénie centrale". `IsSpinCover` formalizes this for
    `G = O(q)⁰`.
  - 1.1.6, printed p. 220 / PDF p. 4: the quadratic forms `Q = E/T` with `E = M_m(D)` and
    `T = {x − ᵗx^σ}`. "A toute forme quadratique non dégénérée q ... est associé un groupe
    algébrique Spin q qui est une forme de D_n avec n = ½md". Here `d = 2`, so `Spin q` is a
    form of `D_m`, that is, of `D_4` or `D_5`.
- J. Tits, *Classification of algebraic semisimple groups*, Proc. Sympos. Pure Math. 9 (1966),
  33–62 (`tits-1966-classification-algebraic-semisimple`), Table II, printed pp. 56–57 / PDF
  pp. 61–62. Type `¹D_n`: in characteristic not 2, `SU_{2n/d}(D, h)` for a nondegenerate
  hermitian form `h` of index `r` relative to an involution of the first kind with
  `dim D^σ = ½d(d + 1)`; in characteristic 2, the "special orthogonal group" of a
  nondegenerate and nondefective "quadratic form". Type `²D_n` is the same with discriminant
  not 1. The p-adic lines read "d = 2 and n = 2r or 2r + 3" (type `¹D_n`) and "d = 2 and
  n = 2r + 1 or 2r + 2" (type `²D_n`). For `r = 1` and `n ≥ 4` these give `n = 5` and `n = 4`,
  Prasad–Raghunathan's ranks 5 and 4. (The values `n = 2` and `n = 3` are not of type `D`
  proper: `D_2 = A_1 × A_1` and `D_3 = A_3` are other types.) Module `Langlands.GroupScheme.Quaternionic.Forms`
  explains why Tits's quadratic forms correspond to these hermitian forms when `2` is
  invertible.

The statement keeps Prasad–Raghunathan's exact family (rank 4 or 5, Witt index 1). This is the
case needed by `Langlands.GroupScheme.LocalRankOneKneserTitsStatement` through the
classification of rank-one groups over local fields.
