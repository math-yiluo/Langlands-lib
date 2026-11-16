# Statement: the rank-one Bruhat relation for Weyl-normalized simple root data

This module defines the predicate `LocalSplitCell.RankOneBruhat`. It states, without proof,
that Weyl-normalized simple-root data over a local ring satisfy it. It contains one
definition and one `Prop`-valued statement, and no theorems.

## The predicate

Notation, from the imported modules:

- `rootPoint v Z x` is the point of `G` over `Z` given by `v : 𝔾ₐ ⟶ G` at the global
  function `x` (module `LocalSplitCell`);
- `cocharPoint ν Z t` is the point of the coordinate split torus `T_I` over `Z` with
  coordinates `t ^ ν j`, for a unit `t` (module `LocalSplitPositiveCell`);
- `i.hom.hom` is the underlying morphism of the torus `i : T_I → G`.

Let `R` be a commutative ring and `G` a group scheme over `Spec R`. Let `i : T_I → G` be a
coordinate split torus, `P : RootDatum J (I → ℤ) (I → ℤ)`, and `v : J → (𝔾ₐ ⟶ G)`. For an
index `a`, write `-a` for `P.reflectionPerm a a` (the index of `-P.root a`) and
`a^∨(d) = cocharPoint (P.coroot a) Z d ≫ i.hom.hom`.

`RankOneBruhat i P v a` says: for every commutative ring `B` in universe `u`, every
`s : Spec B → Spec R`, all global functions `x`, `y` on `Spec B` and every unit `d` with
`d = 1 + x y`,

`v_a(x) · v_{-a}(y) = v_{-a}(d⁻¹ y) · a^∨(d) · v_a(d⁻¹ x)`

over `s`.

## Statement

`LocalSplitRankOneBruhatStatement.{u}` says the following. Let `R` be a commutative local
ring and `G` a reductive group scheme over `Spec R` with affine structure morphism, all in
universe `u`. Let `I` be a finite type with decidable equality and `i : T_I → G` a closed
(`IsClosedSubgroup`) coordinate split torus, maximal on every residue-field fibre
(`IsFibrewiseMaximalTorus`). Let `P : RootDatum J (I → ℤ) (I → ℤ)` be a fibrewise root
datum of `(G, i)` (`IsFibrewiseRootDatumOf`), `b` a base of `P`, and `u : J → (𝔾ₐ ⟶ G)`.
Assume that for every simple root `a` of `b`:

- `u a` is a root parametrization of `i` for `P.root a`, and `u (-a)` is one for
  `P.root (-a)` (`IsRootParametrization`);
- `weylPoint (u a) (u (-a))` is a Weyl point of `i` acting by `P.reflection a`
  (`IsWeylPoint`).

Then `RankOneBruhat i P u a` holds for every simple root `a`.

The hypotheses are those of the published `LocalSplitRankOneNormalStatement` (module
`Langlands.GroupScheme.Reductive.LocalSplitRankOneNormalStatement`).

## Provenance and scope

This is an internal statement, written for this project. It is a rank-one input of the proof
of the Isomorphism Theorem over an arbitrary local ring: right translation of big-cell points
by `u_{-a}(-1)` is computed with it. The relation is SGA 3, Exp. XX, Lemma 6.2.2:
`f_α(a) f_{-α}(b) = f_{-α}(b / (1 + ab)) f_T(α^*(1 + ab)) f_α(a / (1 + ab))` when `1 + ab`
is invertible. There it is proved for invertible `b`, from the structure of reductive groups
of semisimple rank one (Exp. XX, 6.2.1). In `SL₂`, with `u_a(x)` upper unitriangular,
`u_{-a}(y)` lower unitriangular and `a^∨(d) = diag(d, d⁻¹)`, both sides equal the matrix
`[[1 + x y, x], [y, 1]]`. The Weyl-point hypothesis fixes the normalization of `u (-a)`
relative to `u a`, as explained in the Markdown of `LocalSplitRankOneNormalStatement`. The
statement asserts the relation for every reductive group over a local ring, including rings
with nilpotents. It is not proved here; its proof over a general local ring is open in the
Library.
