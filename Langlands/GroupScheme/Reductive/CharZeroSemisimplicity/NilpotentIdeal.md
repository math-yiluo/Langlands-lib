# Tangent vectors in a nilpotent normalized family are trivial

Author: Worker 1498. The flag lemma
`Langlands.Algebra.exists_stable_flag_of_isNilpotent` that the second theorem
applies is by Worker 1429 (module `Langlands.Algebra.NilpotentStableFlag`).

This module is an internal helper for the proof of
`Langlands.GroupScheme.ReductiveCharZeroSemisimplicityStatement`. It is the place
where the hypothesis that the unipotent radical is trivial
(`HasTrivialUnipotentRadical G`, from `Reductive.Basic`) enters the proof.
Throughout, `σ : MatrixRepresentation G n` is a closed embedding
(`IsClosedSubgroup σ`) of a group scheme `G` over a field `k`.

## Declarations

- `mem_comap_blockUnipotent_affine`: an affine point lies in the inverse image
  under `σ` of the block unipotent subgroup of a weight `e : n → ℤ` iff its matrix
  agrees with the identity matrix at every entry `(i, j)` with `e i ≤ e j`.
- `basisCoordinateGL_mulVec`: the basis-coordinate matrix of `b` sends `v` to
  `b.repr v`.
- `conjugate_basisCoordinatePoint_tangentMatrix_apply`: the `(i, j)` entry of a
  tangent matrix of the conjugate `σ.conjugate (basisCoordinatePoint b)` is the
  `i`-th `b`-coordinate of the tangent endomorphism applied to `b j`.
- `eq_one_of_tangentMatrix_blockUnipotent` (Part A). Assume `CharZero k` and that
  `G` is affine, locally of finite type, smooth and connected, with trivial
  unipotent radical. Suppose every tangent matrix of `σ` vanishes at the entries
  `(i, j)` with `e i < e j` (`hP`). Then every `X ∈ lieKernel G k` whose tangent
  matrix vanishes at all entries with `e i ≤ e j` is `X = 1`.
- `eq_one_of_nilpotent_normalized` (Part B). Same hypotheses on `k` and `G`. Let
  `A` be a `k`-subspace of `End (n → k)` such that:
  - every element of `A` is nilpotent (`hnil`);
  - every element of `A` is a tangent endomorphism `toLin' (σ.tangentMatrix k Y)`
    (`hsub`);
  - `A` is closed under the commutator with every tangent endomorphism of `σ`
    (`hbr`).

  Then every `X` whose tangent endomorphism lies in `A` is `X = 1`.

## Proof of Part A

Let `K` be the inverse image under `σ` of the block unipotent subgroup of `e`, with
its closed embedding `jK : K → G`. The Library provides that it is represented and
closed (`comap_subgroupIntersectionFst`, `isClosedSubgroup_subgroupIntersectionFst`).
It is affine and locally of finite type, hence smooth by Cartier's theorem
(`affineCartierSmooth`).

*`K` is unipotent.* Reindex `n` by an antitone enumeration of `e`
(`GeneralLinear.reindexIso`). This carries the block unipotent subgroup of `e` into
the standard unitriangular group of `Fin N` (`matrixReindex_mem_unitriangular`). So
`K` factors through that group by a morphism that is again a closed subgroup
(`IsClosedSubgroup.of_comp`). The unitriangular group is unipotent
(`unitriangularUnipotent`), and closed subgroups of unipotent groups are unipotent
(`unipotentClosedSubgroup`).

*`K` is normal.* By `hP` and `comap_blockParabolic_eq_top` (module
`TangentStability`), `σ` maps all of `G` into the block parabolic of `e`. The
block parabolic normalizes the block unipotent subgroup
(`range_blockUnipotent_isNormalizedBy_range_blockParabolic`), so the range of `jK`
is normal.

The identity component `K⁰` is smooth, connected and unipotent, and its range in
`G` is normal (`isNormal_range_identityComponentι_comp`). Since the unipotent
radical is trivial, the range of `K⁰ → G` is `⊥`. Passing to the identity
component does not change the tangent image
(`tangentSubmodule_range_identityComponent_comp`), so the tangent submodule of `K`
is `⊥`. The hypothesis on `X` says that `1 + ε·σ.tangentMatrix k X` satisfies the
block-unipotent equations, so `X` lies in that tangent submodule. Hence `X = 1`.

## Proof of Part B

Apply `exists_stable_flag_of_isNilpotent` to `A`. `A` is closed under commutators
by `hsub` and `hbr`, and the normalizing set `S` consists of all tangent
endomorphisms of `σ`. This gives an antitone flag `F` with `F 0 = ⊤`, `F m = ⊥`,
`a (F t) ⊆ F (t + 1)` for `a ∈ A`, and `g (F t) ⊆ F t` for `g ∈ S`.

`exists_basis_flag` (module `FlagBasis`) gives a basis `b` and levels `e` adapted
to `F`. The conjugate `σ' = σ.conjugate (basisCoordinatePoint b)` is again a closed
embedding (`IsClosedSubgroup.comp_iso`). By
`conjugate_basisCoordinatePoint_tangentMatrix_apply`, its tangent matrices are the
tangent endomorphisms written in `b`.

`repr_apply_eq_zero_of_flag` with shift `d = 0` shows that every tangent matrix of
`σ'` vanishes at the entries with `e i < e j`. With `d = 1` it shows that the tangent
matrix of `X`, whose endomorphism lies in `A`, vanishes at the entries with
`e i ≤ e j`. Part A for `σ'` and the weights `e` (cast to `ℤ`) gives `X = 1`.
