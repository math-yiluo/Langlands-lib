# Actual quaternionic spin covers from rank-one type-D indices

Author: Worker 5442.

`Langlands.GroupScheme.TypeDRankOneSpinStatement.{u}` is an unproved
identification statement. It supplies the forward type-D case needed
after the enumeration `LocalRankOneTitsIndexStatement` of the actual
local rank-one indices, namely its last two alternatives
`d.HasRankOneOuterD4Index` and `d.HasRankOneInnerD5Index`.

## Statement

For any field `K : Type u`, any affine locally finite type group scheme
`G` over `Spec K`, actual `d : TitsIndexData G` and natural number `n`,
assume `IsSimplyConnected G`, `IsAbsolutelyAlmostSimple G`,
`splitRank G = 1`, and

- either `n = 4` and `d.HasRankOneOuterD4Index` (the index
  `²D_4,1^(2)`),
- or `n = 5` and `d.HasRankOneInnerD5Index` (the index `¹D_5,1^(2)`).

The conclusion supplies:

- a central division algebra `D : Type u` over `K`, finite dimensional
  with `Module.finrank K D = 4` (a quaternion division algebra);
- `σ : Quaternionic.FirstKindInvolution K D` whose symmetric subspace
  has `K`-dimension 3;
- a `σ`-quadratic form `q : σ.QuadraticForms (Fin n)` with
  `σ.IsNondegenerateQuadratic q` and `σ.quadraticWittIndex q = 1`;
- a morphism of group schemes `π : G ⟶ σ.isometryGroup q` with
  `σ.IsSpinCover q π`.

The number `n` only names the number of quaternionic variables, which
is the absolute rank of the index: 4 for `²D_4,1^(2)` and 5 for
`¹D_5,1^(2)`.

The actual-index predicates are those published in
`LocalRankOneTitsIndexStatement`. `HasRankOneOuterD4Index` compares all
Cartan entries with `CartanMatrix.D 4`, marks exactly vertex 2 in
one-based numbering as distinguished, and requires the full absolute
Galois star image to be exactly the identity and the transposition of
the two fork tips numbered 3 and 4. `HasRankOneInnerD5Index` compares
all Cartan entries with `CartanMatrix.D 5`, marks exactly vertex 2, and
requires the full star action to be trivial. No algebra, involution,
form or spin cover is a field of the supplied data.

The statement is over arbitrary fields and every characteristic,
including characteristic 2. There is no local-field hypothesis. The
universe `u` is arbitrary and shared by `K` and `D`; the coordinates use
the small type `Fin n`.

## Model conventions

These are the conventions of the imported
`Langlands.GroupScheme.Quaternionic.Forms` and
`Langlands.GroupScheme.Quaternionic.GroupSchemes`, consumed by the
spin disjunct of family (iii) of `LocalRankOneClassificationStatement`.

- `σ.QuadraticForms (Fin n)` is Tits's space of `σ`-quadratic forms,
  `M_n(D) ⧸ {x − ᵗx^σ}`, on left row vectors of `D^n`.
- `σ.IsNondegenerateQuadratic q` says that the polar Gram matrix
  `Q + ᵗQ^σ` of a representative `Q` is invertible.
- `σ.quadraticWittIndex q` is the largest `D`-dimension of a totally
  singular subspace of `D^n`.
- `σ.isometryGroup q` is the actual isometry group scheme `O(q)`: on a
  test scheme with global sections `R` its points are the units `u` of
  `R ⊗[K] M_n(D)` with `u Q ᵗu^σ − Q ∈ R ⊗ {x − ᵗx^σ}`.
- `σ.IsSpinCover q π` says that `G` is simply connected, that `O(q)` is
  smooth, and that `π` is a central isogeny onto the identity component
  `O(q)⁰` followed by the inclusion `O(q)⁰ ⟶ O(q)`. So the conclusion
  says that `G` is a spin group of `q`, the simply connected central
  cover of `O(q)⁰`, without a chosen model of `Spin(q)`.

An isomorphism of field-valued point groups alone is not the conclusion.

## Original sources and derived formulation

J. Tits, *Classification of algebraic semisimple groups* (1966),
`tits-1966-classification-algebraic-semisimple`, Table II, types `¹D_n`
(printed pp.56–57 / PDF pp.61–62) and `²D_n` (printed p.57 / PDF p.62),
are the original classification passages. The registered proceedings
PDF has SHA-256
`962203f9e47e9c3c43fc1049a38e28c751aa42beb7ee5250a095a132e215a5d4`.

For `¹D_n^(d)_{n,r}` the distinguished vertices are `d, 2d, ..., rd`.
For `²D_n` they are the same, except that the last one is replaced by
the orbit `(n − 1, n)` when `n = rd + 1`. In our two indices the only
distinguished vertex is 2 and `n` is 4 or 5, so `d = 2`, `r = 1` and
`n ≠ rd + 1`. For `d = 2` Tits's description is, when `char k ≠ 2`, the
special unitary group `SU_{2n/d}(D, h) = SU_n(D, h)` of a nondegenerate
hermitian form `h` of index `r` relative to an involution of the first
kind of the quaternion division algebra `D` with
`dim D^σ = d(d + 1)/2 = 3`; when `char k = 2` it is the special
orthogonal group of a nondegenerate, nondefective "quadratic form" in
the sense of Seip-Hornix of index `r` relative to an involution of the
first kind. The form has discriminant 1 for `¹D` and discriminant
`≠ 1` for `²D`. Tits's `p`-adic lines allow `d = 2` with `n = 2r` or
`2r + 3` for `¹D` and with `n = 2r + 1` or `2r + 2` for `²D`; for `r = 1`
these give `n = 5` for `¹D` and `n = 4` for `²D` (the other values
`n = 2` and `n = 3` are not absolutely simple or are of type `A`, as
recorded in `LocalRankOneClassificationStatement.md`). The local
restriction is not used here: the actual index is supplied as a
hypothesis.

G. Prasad and M. S. Raghunathan, *On the Kneser–Tits problem* (1985),
`prasad-raghunathan-1985-kneser-tits`, Section 2, printed p.111 / PDF
p.6, describes the corresponding local family as the spin group of a
`σ`-quadratic form of Witt index 1 and rank 4 or 5, where `σ` is an
involution of the quaternion central division algebra `D` with
`dim D^σ = 3`. The PDF SHA-256 is
`42f4db49659757b703d1b9c72c6ae5e17d75161eb13088790bd60b549a30058f`.
The conclusion here uses exactly the binders of that spin disjunct in
`LocalRankOneClassificationStatement`.

This formulation is derived. Tits describes strict-isogeny
representatives through unitary or orthogonal groups, while the
conclusion here asks for the simply connected group itself, as PR85
does, through the spin-cover predicate. Tits's description uses
hermitian forms in characteristic not 2 and Seip-Hornix quadratic forms
in characteristic 2; the conclusion uses Tits's `σ`-quadratic forms in
every characteristic, as PR85 does. In characteristic not 2 a
`σ`-quadratic form is determined by its polar hermitian form `Q + ᵗQ^σ`.
The discriminant condition is not part of the conclusion: the consumer
family (iii) of the classification does not record it. A proof of this
statement must construct the algebra with involution and the
`σ`-quadratic form, justify its degree, nondegeneracy and Witt index
from the actual index, prove smoothness of `O(q)`, and construct the
central isogeny from `G` onto `O(q)⁰`. None of these steps is supplied
as a premise.

The declaration is only a closed `Prop`-valued definition. There is no
proof theorem, no proof of local admissibility or of the exclusion of
trialitarian and exceptional indices, and no converse assertion that
arbitrary supplied forms have this index. Its focused proof remains
necessary before this identification can be used without an explicit
premise.
