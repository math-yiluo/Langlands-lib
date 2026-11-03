# Borel subgroups of cocharacter centralizers inside ambient Borels

Authors: Worker 1386 and Worker 1150.

`Langlands.GroupScheme.CentralizerBorelIntersectionStatement.{u}` is a
Prop-valued definition. This module states the proposition and supplies no proof.
It imports the published Borel and dynamic-centralizer definitions unchanged.

## Hypotheses and conclusion

The universe `u` is arbitrary. Let `k : Type u` be a field with `IsAlgClosed k`,
and let `G` be a group scheme over `Spec (CommRingCat.of k)`. The premises
`Smooth G.X.hom`, `IsAffineHom G.X.hom`, and `ConnectedSpace G.X.left` say that
`G` is smooth and affine over `k` and its underlying topological space is
connected. These hypotheses give the source's setting of a connected affine
group variety. Reductivity and a characteristic restriction are not assumed.

The morphism `χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G` is any
cocharacter. It need not be injective, nontrivial, or chosen inside a maximal
torus.

The group scheme `M` and homomorphism `j : M ⟶ G` are arbitrary subject to four
explicit premises:

- `IsClosedSubgroup j` says that the underlying scheme morphism is a closed
  immersion.
- `(Dynamic.centralizer χ).IsRepresentedBy j` says that the underlying morphism
  in `Over (Spec k)` is a monomorphism and that `SubgroupFunctor.range j`
  equals `Dynamic.centralizer χ`.
- `Smooth M.X.hom` says that `M` is smooth over `k`.
- `ConnectedSpace M.X.left` says that its underlying space is connected.

The published dynamic centralizer is defined on every test scheme `T` over
`Spec k`. Its points are the `g : T ⟶ G.X` whose conjugation orbit map on
`T ×_k 𝔾ₘ` is constant. Equivalently, after every further change of test scheme,
`g` commutes with every point of the cocharacter. The representation premise
identifies precisely this subgroup functor, including on non-affine and
nonreduced tests. It is not only an equality of groups of `k`-points.

For every group scheme `B` and homomorphism `b : B ⟶ G`, assume
`IsBorelSubgroup b` and
`SubgroupFunctor.range χ ≤ SubgroupFunctor.range b`. The latter inclusion says
that, on every test scheme, every point coming from `χ` factors through `b`.
The conclusion produces a group scheme `C` over `Spec k` and homomorphism
`c : C ⟶ M` with `IsBorelSubgroup c` and
`SubgroupFunctor.range (c ≫ j) ≤ SubgroupFunctor.range b`. Thus a Borel subgroup
of `M` lies in the given ambient Borel on every test scheme. In both
inclusions, `range` is the actual range of the map of groups of test-scheme
points, as defined in `SubgroupFunctor`; no restriction to affine or reduced
tests is made.

## Meaning of Borel subgroup

The imported `IsBorelSubgroup i` requires a closed immersion, a smooth and
connected domain, and `IsSolvableGroupScheme` of that domain. Solvability means
that the abstract group of points of its base change to `AlgebraicClosure k`,
valued in `AlgebraicClosure k`, is solvable.

Its maximality field says that for every smooth, connected, solvable closed
subgroup `i' : B' ⟶ H` of the same ambient group `H`, every factorization
`f ≫ i' = i` has `IsIso f`. For `b` the ambient group is `G`; for the
conclusion's `c` it is `M`. In particular, the conclusion requires maximality
among such subgroups of `M`.

## Source and derived provenance

The source is J. S. Milne, *Algebraic Groups* (2017), Theorem 17.46, printed
pp.365–366, zero-based PDF pages 380–381 (one-based PDF pages 381–382).
Registered source: `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The full official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` has been read and contains no
correction to 17.46.

Milne takes an embedded torus `S` in a connected group variety and a Borel
subgroup `B` containing `S`; his first assertion makes `C_G(S) ∩ B` a Borel
subgroup of `C_G(S)`. The present proposition is derived from that assertion
in two respects:

- It uses a cocharacter. The route from Milne's assertion takes `S` to be the
  scheme-theoretic image of `χ`, a split torus that may be trivial. Since `B`
  is closed and contains `χ`, it contains `S`. Comparing the all-test-scheme
  centralizers of `χ` and `S` identifies the represented group `M` with
  `C_G(S)`. These comparisons are proof obligations, not extra assumptions
  or results of this module. The Library's `Rational.SplitTorusImage` provides
  a split-image factorization construction for this route.
- It asserts only the existence of a Borel subgroup of `M` lying in `B`.
  Milne's `C_B(S)` supplies the intended witness. The proposition does not
  assert that the intersection of `M` with `B` is representable or is itself
  Borel. It also omits the theorem's second assertion, which describes every
  Borel subgroup of the centralizer over an algebraically closed field.

Smoothness and connectedness of `M` are premises here. Milne obtains the
corresponding properties from 13.10 and 17.38; their unrestricted dynamic
centralizer analogues belong to separate work. When `χ` is trivial, `M`
represents all of `G`, and transporting `B` along that identification gives
the required witness. The statement includes this case and noninjective
cocharacters in every characteristic.
