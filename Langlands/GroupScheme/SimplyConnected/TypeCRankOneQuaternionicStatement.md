# Actual quaternionic symplectic models from rank-one type-C indices

Author: Worker 165.

`Langlands.GroupScheme.TypeCRankOneQuaternionicStatement.{u}` is an
unproved identification statement. It supplies the forward type-C case
needed after enumeration of the actual local rank-one indices.

For any field `K : Type u`, any affine locally finite type group scheme
`G` over `Spec K`, actual `d : TitsIndexData G`, and natural number `n`,
assume `IsSimplyConnected G`, `IsAbsolutelyAlmostSimple G`,
`d.HasRankOneCIndex n` and `splitRank G = 1`. The conclusion supplies:

- a central division algebra `D : Type u` over `K`, finite dimensional
  with `Module.finrank K D = 4`;
- `σ : Quaternionic.FirstKindInvolution K D` whose symmetric subspace
  has `K`-dimension 3;
- `NeZero n` and a matrix `H : Matrix (Fin n) (Fin n) D` with
  `σ.IsAntihermitian H`, `IsUnit H` and `σ.wittIndex H = 1`;
- `Nonempty (G ≅ σ.symplecticGroup H)`, an isomorphism of actual
  group schemes over `Spec K`.

The actual-index predicate already requires `n = 2` or `n = 3`.
It compares all Cartan entries with `CartanMatrix.C n`, identifies
exactly vertex 2 in one-based numbering as distinguished, and requires
triviality of the full absolute Galois star action. No algebra,
involution, form or presentation is a field of the supplied data.
The extra `NeZero n` witness only supplies the nonempty index type
needed to form the reduced norm; positivity also follows from the
index's small-rank condition.

The statement is over arbitrary fields and every characteristic,
including characteristic 2. There is no local-field hypothesis: the
small absolute ranks and the distinguished subset are already given
by the actual-index hypothesis. The universe `u` is arbitrary and
shared by `K` and `D`; the coordinates use the small type `Fin n`.

## Model conventions

The imported `Quaternionic.Forms` uses left `D`-vector spaces of row
vectors and the Gram formula `h(x,y) = ∑ i j, x i * H i j * σ(y j)`.
The antihermitian condition includes both `ᵗH^σ = -H` and trace-valued
diagonal entries in `{a - σ(a)}`. The latter condition is essential in
characteristic 2. Invertibility of `H` is nondegeneracy. The Witt
index is the largest `D`-dimension of a totally isotropic subspace.
These are the published conventions consumed by family (iii) of
`LocalRankOneClassificationStatement`.

The imported actual group `σ.symplecticGroup H` is the kernel of
reduced norm on the unitary isometry group. On every test scheme with
global sections `R`, its ambient isometries are units in
`R ⊗[K] Matrix (Fin n) (Fin n) D` satisfying
`u * (1 ⊗ H) * ᵗu^σ = 1 ⊗ H`; the group imposes reduced norm 1.
An isomorphism of field-valued point groups alone is not the
conclusion. Neither the supplied-form group construction nor its
split-rank calculations identify an arbitrary `G` from `d`.

## Original sources and derived formulation

J. Tits, *Classification of algebraic semisimple groups* (1966),
`tits-1966-classification-algebraic-semisimple`, Table II explanations,
printed pp.54--55 / PDF pp.59--60, and type C entry, printed p.56 /
PDF p.61, are the original classification passages. The registered
proceedings PDF has SHA-256
`962203f9e47e9c3c43fc1049a38e28c751aa42beb7ee5250a095a132e215a5d4`.

For type `C_n` its general-field entry has distinguished vertices
`d,2d,...,rd`, where `d` is the division degree and `r` the relative
rank. In our index the only distinguished vertex is 2. Thus the
corresponding presentation has `d = 2`, `r = 1`, and its form has
`2n/d = n` quaternionic variables. The symmetric subspace dimension
is `d(d+1)/2 = 3`. The table describes a nondegenerate antihermitian
form of index `r` relative to such a first-kind involution.
The `d = 1` split case instead has `r = n`; it cannot have the supplied
marked index with `n = 2` or `3`. The table's p-adic special-field
line is not used to infer small ranks here. Its printed `2r - 1`
discrepancy and the independent arbitrary-characteristic enumeration
obligation are recorded in `LocalRankOneTitsIndexStatement.md`.

Prasad--Raghunathan, *On the Kneser--Tits problem* (1985),
`prasad-raghunathan-1985-kneser-tits`, Section 2, printed p.111 /
PDF p.6, describes the corresponding local family as the symplectic
group of a sigma-antihermitian form of rank 2 or 3 and Witt index 1,
over a quaternion central division algebra with symmetric subspace
of dimension 3. The PDF SHA-256 is
`42f4db49659757b703d1b9c72c6ae5e17d75161eb13088790bd60b549a30058f`.
Its local restriction is used only to identify the intended consumer
family; the conditional identification here uses the supplied index.

This formulation is derived: Tits explicitly gives strict-isogeny
representatives described through rational points. A proof of this
statement must construct the algebra with involution and trace-valued
form, justify its degree and Witt index from the actual index, and
identify the original simply connected group scheme with the
published reduced-norm-one isometry model on all test schemes.
Changing column and row conventions must preserve the group law
and the Witt index. None of these steps is supplied as a premise.

The declaration is only a closed Prop-valued definition. There is no
proof theorem, no proof of local admissibility or exceptional
exclusions, and no converse assertion that arbitrary supplied forms
have this index. Its focused proof remains necessary before this
identification can be used without an explicit premise.
