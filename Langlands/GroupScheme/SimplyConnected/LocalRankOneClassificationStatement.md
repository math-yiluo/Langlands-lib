# Rank-one absolutely almost-simple simply connected groups over local fields

Author: Worker 5198.

## Statement

`Langlands.GroupScheme.LocalRankOneClassificationStatement.{u}` says the
following. Let `K : Type u` be a nonarchimedean local field (instances
`[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]`).
Let `G` be a group scheme over `Spec (CommRingCat.of K)` with
`[IsAffineHom G.X.hom]`, `IsSimplyConnected G`, `IsAbsolutelyAlmostSimple G`
and `splitRank G = 1`. Then `G` belongs, up to isomorphism in the category
of group schemes over `Spec K`, to one of these families:

1. **(i) `SL₂(D)`.** For some `D : Type u` with `[DivisionRing D]`,
   `[Algebra K D]`, `[FiniteDimensional K D]` and `[Algebra.IsCentral K D]`,
   `G ≅ CentralSimpleUnits.BinaryRoot.groupScheme K D`. This published group
   is the reduced-norm-one group `normOne K (Matrix (Fin 2) (Fin 2) D)`, that
   is, `SL₂(D)`. `DivisionRing.isSimpleRing` supplies its `IsSimpleRing`
   argument.
2. **(ii) Special unitary groups.** For some field `L : Type u` with
   `[Algebra K L]`, `[Algebra.IsQuadraticExtension K L]` and
   `[Algebra.IsSeparable K L]`, some `m` with `m = 1 ∨ m = 2`, some diagonal
   Hermitian form `H : HermitianRoot.DiagonalForm (SU3Root.fieldInvolution K L) (Fin m)`,
   and unit witnesses `w : Fin m → Lˣ` with `hw : ∀ i, (w i : L) = H.weight i`:
   `H.IsAnisotropic` and
   `G ≅ HermitianRoot.SchemeModel.groupScheme K L H w hw`.
3. **(iii) Quaternionic groups.** For some `D : Type u` with
   `[DivisionRing D]`, `[Algebra K D]`, `[Algebra.IsCentral K D]` and
   `[FiniteDimensional K D]` and `Module.finrank K D = 4` (a quaternion
   central division algebra), and some
   `σ : Quaternionic.FirstKindInvolution K D` (a `K`-linear anti-automorphism
   of order 2, that is, an involution of the first kind) with
   `Module.finrank K σ.symmetricSubspace = 3` (`dim_K D^σ = 3`), one of the
   following holds:
   - **symplectic:** for some `m` with `NeZero m` and `m = 2 ∨ m = 3`, and
     some `H : Matrix (Fin m) (Fin m) D` with `σ.IsAntihermitian H`,
     `IsUnit H` and `σ.wittIndex H = 1`, `G ≅ σ.symplecticGroup H`;
   - **spin:** for some `m` with `m = 4 ∨ m = 5` and some
     `q : σ.QuadraticForms (Fin m)` with `σ.IsNondegenerateQuadratic q` and
     `σ.quadraticWittIndex q = 1`, there is `π : G ⟶ σ.isometryGroup q` with
     `σ.IsSpinCover q π`.

Only this forward direction is stated. That each listed group satisfies the
hypotheses is not stated here. For family (iii), Task 5197 states it as
`Quaternionic.LocalSymplecticRankOneStatement` and
`Quaternionic.LocalSpinRankOneStatement`, whose hypotheses on `D`, `σ`, `m`,
`H` and `q` are exactly those of the (iii) disjunct. There
is no restriction on the characteristic of `K` or of its residue field, so
characteristic 2 and residue characteristic 2 are included. The universe `u`
is arbitrary. `K`, `D` and `L` are in `u`. The finite index types `Fin m`
are in `Type`, as `HermitianRoot.SchemeModel.groupScheme` and the
quaternionic groups require.

The statement is one closed `Prop`-valued definition. Nothing is proved.

## Source

G. Prasad and M. S. Raghunathan, *On the Kneser–Tits problem*, Comment.
Math. Helv. 60 (1985), registered `prasad-raghunathan-1985-kneser-tits`,
§2, printed p.111 / PDF p.6. Let `G` be an absolutely simple, simply
connected group of `K`-rank 1 over a nonarchimedean local field `K`. The
source says it is one of:

- (i) `SL₂(D)`, `D` a finite-dimensional central division algebra over `K`;
- (ii) `SU(f)`, `f` a hermitian form of Witt index 1 in 3 or 4 variables,
  defined in terms of a quadratic Galois extension of `K`;
- (iii) the spin group of a `σ`-quadratic form of Witt index 1 and rank 4
  or 5, or the symplectic group of a `σ`-antihermitian form of rank 2 or 3 and
  Witt index 1, where `σ` is an involution of the quaternion central division
  algebra `D` over `K` such that `dim D^σ = 3`.

The same passage notes that "there are no rank 1 forms of exceptional
groups over a nonarchimedean local field". It credits the classification to
Kneser in characteristic zero (its [3]) and to Bruhat–Tits in arbitrary
characteristic (its [2], *Groupes algébriques simples sur un corps local*,
Driebergen 1966).

J. Tits, *Classification of algebraic semisimple groups*, Proc. Sympos.
Pure Math. 9 (1966), 33–62, registered
`tits-1966-classification-algebraic-semisimple`, in the proceedings file at
`/home/taskhub/central-library/Borel-Mostow--Algebraic groups and discontinuous subgroups (proceedings)--1966/`:

- 3.3.3, printed p.47 / PDF p.52. Over the `p`-adic numbers, an anisotropic
  absolutely almost simple group is of inner type `A_n`. Removing the
  distinguished vertices of an admissible index must leave an admissible
  anisotropic index. 3.3.4 (printed p.48 / PDF p.53) refers to Table II for
  the complete list of indices that occur.
- Table II, printed pp.54–61 / PDF pp.59–66. Column `p` ("p-adic fields")
  lists the indices that occur over `p`-adic fields.

### Tits indices of each family

Here `n` is the absolute rank, `r = 1` is the relative rank and `d` is the
degree of the division algebra in Tits's notation `ᵍX_{n,r}^{(d)}`.

- **(i)** Type `¹A_n`, printed p.55 / PDF p.60. The index is `¹A_{n,1}^{(d)}`
  with `d(r+1) = n+1`, so `n = 2d−1`. Its description is `SL_{r+1}(D) = SL₂(D)`
  with `D` central of degree `d`. Over `p`, `d` is arbitrary. The value `d = 1`
  (split `SL₂`) also covers the coincident indices of `B₁ = C₁ = A₁`.
- **(ii)** Type `²A_n`, printed p.55 / PDF p.60. Over `p`, `d = 1` and
  `n = 2r−1, 2r or 2r+1`; for `r = 1` this gives `n = 1, 2 or 3`. The
  description is `SU_{n+1}(k', h)` with `h` hermitian of index 1 relative
  to a quadratic extension `k'`. The value `n = 1` gives no group of outer
  type, because `A₁` has no diagram automorphism; the hermitian hyperbolic
  plane gives `SL₂`, which is in (i). So `n = 2` and `n = 3`, that is 3 or 4
  variables, are the indices `²A_{2,1}^{(1)}` and `²A_{3,1}^{(1)}`.
- **(iii), symplectic.** Type `C_n`, printed p.56 / PDF p.61. Take `d = 2`
  and `r = 1`. The description is `SU_{2n/d}(D, h) = SU_n(D, h)` with `h`
  antihermitian of index `r` relative to an involution of the first kind with
  `dim D^σ = d(d+1)/2 = 3`, which is PR85's symplectic group of rank `n`.
  *Source discrepancy:* the `p` line of Table II prints "`d = 2` and `n = 2r`
  or `2r − 1`". But the distinguished vertices of this index are
  `d, 2d, …, rd`, which forces `rd = 2r ≤ n`; the drawn index thus excludes
  `n = 2r−1`. The reading consistent with the drawing and with PR85's
  "rank 2 or 3" is `n = 2r` or `2r+1`, giving the indices `C_{2,1}^{(2)}` and
  `C_{3,1}^{(2)}`. For `d = 1` the group is `Sp_{2n}` with `r = n`; in rank
  one that is `Sp₂ = SL₂`, which is in (i). The type `B_n` (printed pp.55–56 /
  PDF pp.60–61) allows `r = n` or `n−1` over `p`. Its rank-one cases are
  `B₁ = A₁`, which is in (i), and `B_{2,1}`. Under `B₂ = C₂` the index
  `B_{2,1}` coincides with `C_{2,1}^{(2)}`.
- **(iii), spin.** Types `¹D_n` (printed pp.56–57 / PDF pp.61–62) and `²D_n`
  (printed p.57 / PDF p.62). For `d = 2` the description is the group of a
  rank-`n` hermitian form relative to an involution with `dim D^σ = 3`. In
  characteristic 2 Tits uses Seip-Hornix quadratic forms instead, as do
  Tits's `σ`-quadratic forms in PR85. Over `p`, `¹D` allows `d = 2` with
  `n = 2r` or `2r+3`, and `²D` allows `d = 2` with `n = 2r+1` or `2r+2`. For
  `r = 1` the cases are:
  - `n = 2`: not absolutely simple;
  - `n = 3`: `²D_{3,1}^{(2)} = ²A_{3,1}^{(1)}`, which is in (ii);
  - `n = 4`: `²D_{4,1}^{(2)}`, rank 4;
  - `n = 5`: `¹D_{5,1}^{(2)}`, rank 5.

  For `d = 1` the rank-one cases are as follows. In `¹D`, `r = n−2` gives
  `n = 3`, and `¹D_{3,1}^{(1)} = ¹A_{3,1}^{(2)}` is `SL₂(D)` with `D`
  quaternion, which is in (i). In `²D`, `n = r+1` gives `n = 2`, which is not
  absolutely simple. So the spin groups not already in (i) or (ii) are exactly
  those of rank 4 and 5.
- **Exceptional types**, printed pp.58–61 / PDF pp.63–66. The rank-one
  indices `³D_{4,1}^9`, `⁶D_{4,1}^9`, `²E_{6,1}^{35}`, `²E_{6,1}^{29}`,
  `E_{7,1}^{78}`, `E_{7,1}^{66}`, `E_{7,1}^{48}`, `E_{8,1}^{133}`,
  `E_{8,1}^{91}` and `F_{4,1}^{21}` all have "−" in the `p` column. `¹E₆`
  and `G₂` have no rank-one index. This matches PR85's remark.

### Arbitrary characteristic

Tits 1966 states 3.3.3 for the `p`-adic numbers. PR85 attributes the
general case to Bruhat–Tits. Their paper F. Bruhat and J. Tits, *Groupes
algébriques simples sur un corps local*, in T. A. Springer (ed.),
*Proceedings of a Conference on Local Fields* (Driebergen 1966), Springer
1967, pp.23–36, is registered as `springer-1967-conference-local-fields`.
Its §4 (printed p.29 / PDF p.35) takes `K` complete for a discrete valuation
with perfect residue field `k`, in any characteristic. Proposition 6 (printed
p.35 / PDF p.41) says: if `dim k ≤ 1` and `G` is `K`-anisotropic, then `G`
is of type `A_n`; if moreover `Gal(k̄/k)` is commutative, `G` is an inner form
of `A_n` and `G_K` is the reduced-norm-one group of a central division
algebra over `K`. This is the characteristic-free form of Tits's 3.3.3 for
local fields with finite residue field. It is combined with Tits's
field-independent index theory (§§2–3) and the Table II descriptions, which
include the characteristic-2 forms (`B_n` with defect 1; `D_n` with
Seip-Hornix quadratic forms). J. Tits, Séminaire Bourbaki 505 (1977),
registered `tits-1977-whitehead-bourbaki-505`, 1.2 (PDF pp.5–6), applies the
same classification to every locally compact nondiscrete field. In that
exposé "p-adic" means any local field with finite residue field.

## Correspondence of conventions

- **"Absolutely simple" and `IsAbsolutelyAlmostSimple`.** PR85 and Tits use
  "absolutely simple" for a semisimple group that is simple, in the
  algebraic-group sense of having no proper nontrivial connected normal
  subgroup, after extension to an algebraic closure. Its center may be
  finite. The published `IsAbsolutelyAlmostSimple G` is
  `IsAlmostSimple G ∧ IsAlmostSimple (G ⊗ k̄)` along `toAlgebraicClosure K`.
  Here `IsAlmostSimple` means semisimple, noncommutative and without proper
  nontrivial smooth connected normal subgroups. This is Milne's
  "geometrically (absolutely) almost-simple" (Definition 19.7 and Notes).
  The conjunct over `K` is part of the definition; no descent equivalence is
  used or asserted.
- **Simply connected.** The published `IsSimplyConnected G` requires `G` to
  be semisimple and every central isogeny onto `G` from a semisimple group to
  be an isomorphism. PR85's groups are simply connected in this algebraic
  sense.
- **`K`-rank.** PR85's "`K`-rank 1" is `splitRank G = 1`. The published
  `splitRank` takes values in `ℕ∞`.
- **`[IsAffineHom G.X.hom]`.** Linear algebraic groups are affine. The
  hypothesis matches the published `LocalRankOneKneserTitsStatement`, which
  this classification serves.
- **Isomorphism.** `Nonempty (G ≅ …)` is an isomorphism in the category of
  group schemes over `Spec (CommRingCat.of K)`. The spin case of (iii) is
  the one exception: there `G` is required to be a spin group of `q` through
  `σ.IsSpinCover q π`, explained below.
- **Family (ii).** In characteristic 2 a quadratic Galois extension is a
  separable quadratic extension, encoded by `Algebra.IsQuadraticExtension`
  and `Algebra.IsSeparable`. The published model
  `HermitianRoot.SchemeModel.groupScheme K L H w hw` is the group scheme
  whose points on every test scheme are the determinant-one matrices
  preserving the Gram matrix `HermitianRoot.gram H`. That matrix is a
  hyperbolic plane on the two outer indices of `Unit ⊕ (Fin m ⊕ Unit)` plus
  the diagonal form `−diag(H.weight)` on `Fin m`. The forms covered are
  therefore the hyperbolic plane plus a nondegenerate diagonal form in `m`
  variables, that is, `m + 2 = 3` or `4` variables. The units `w` express
  nondegeneracy. `H.IsAnisotropic` (`H.pairing x x = 0 → x = 0`) says the
  middle form is anisotropic, which together with the hyperbolic plane gives
  Witt index exactly 1. Conversely, every nondegenerate hermitian form of
  Witt index 1 in 3 or 4 variables has this shape: the trace of a separable
  quadratic extension is surjective, so a nonzero hermitian form has a
  nonisotropic vector and nondegenerate hermitian forms are diagonalizable;
  Witt decomposition splits off one hyperbolic plane and leaves an
  anisotropic form. The sign in `−diag(H.weight)` is harmless because the
  statement quantifies over all `H`. This is the model and anisotropy
  predicate consumed by
  `HermitianRoot.SchemeModel.parabolicElementarySubgroup_eq_top_of_model_iso`.
- **Family (iii).** The groups are those of Task 5197, module
  `Langlands.GroupScheme.Quaternionic.GroupSchemes`, with the forms of
  `Langlands.GroupScheme.Quaternionic.Forms`. A form on `D^m` is given by a
  Gram matrix in `M_m(D)`; `m` is PR85's "rank", the `D`-dimension of the
  space.
  - `σ.IsAntihermitian H` says `ᵗH^σ = −H` and every diagonal entry lies in
    `{a − σ a}` (trace-valued; automatic when `2` is invertible in `K`).
    `IsUnit H` is nondegeneracy, and `σ.wittIndex H` is the largest
    `D`-dimension of a totally isotropic subspace of `D^m`.
    `σ.symplecticGroup H` is the kernel of the reduced norm of `M_m(D)` on
    the unitary group `U(h) = {u : u H ᵗu^σ = H}`, which is PR85's symplectic
    group of `h`. `NeZero m` only supplies `Nonempty (Fin m)` for the reduced
    norm; it follows from `m = 2 ∨ m = 3`.
  - `σ.QuadraticForms (Fin m)` is Tits's space of `σ`-quadratic forms,
    `M_m(D) ⧸ {x − ᵗx^σ}`. `σ.IsNondegenerateQuadratic q` says the polar
    Gram matrix `Q + ᵗQ^σ` is invertible, and `σ.quadraticWittIndex q` is the
    largest `D`-dimension of a totally singular subspace. These include the
    characteristic-2 forms that PR85 and Tits use.
  - Spin groups are characterized rather than constructed, as agreed with
    the owner of Task 5197. `σ.IsSpinCover q π` says that `G` is simply
    connected, that the isometry group `σ.isometryGroup q = O(q)` is smooth,
    and that `π` is a central isogeny onto the identity component `O(q)⁰`
    followed by the inclusion `O(q)⁰ ⟶ O(q)`. So the spin disjunct says that
    `G` is a spin group of `q`, the simply connected central cover of
    `O(q)⁰`. Such a cover is unique up to isomorphism, so this is the
    isomorphism `G ≅ Spin(q)` of PR85 written without a chosen model of
    `Spin(q)`.
  - In characteristic not 2, an involution of the first kind on a
    quaternion algebra with `dim D^σ = 3` is orthogonal; `σ`-antihermitian
    forms then have symplectic groups of type `C_m`, and `σ`-quadratic forms
    have spin groups of type `D_m`. This matches the Tits indices listed
    above (`C_2`, `C_3`, `D_4`, `D_5`).
- **Family (i).** `D` is a central division algebra, as in PR85 (i). `D = K`
  is allowed and gives the split `SL₂`. These are the binders of the
  published consumer
  `CentralSimpleUnits.BinaryRoot.WeilRoot.parabolicElementarySubgroup_eq_top_of_localSK1_of_iso`.

## Provenance

The statement is PR85 §2's list, with each group replaced by the Library
construction designated for its family by this task's contract: the published
`CentralSimpleUnits.BinaryRoot.groupScheme` for (i), the published
`HermitianRoot.SchemeModel.groupScheme` for (ii), and Task 5197's
quaternionic symplectic groups and spin-cover predicate for (iii).
