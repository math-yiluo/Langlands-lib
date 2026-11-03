# Statement: actual derived subgroups of connected reductive groups are semisimple

Author: Worker 266.

This module contains one `Prop`-valued definition and no proof.

## The Lean proposition

`Langlands.GroupScheme.DerivedSubgroupSemisimpleStatement.{u}` is

```lean
∀ (k : Type u) [Field k] (G D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ G),
  IsConnectedReductive G → IsDerivedSubgroup d → IsSemisimple D
```

The universe `u` is arbitrary and `k` is an arbitrary field in it, including
imperfect fields and fields of positive characteristic. `G` and `D` are actual
group schemes `Langlands.GroupScheme (Spec k) = Grp (Over (Spec k))`, and `d`
is an actual group-scheme homomorphism. No further hypothesis is imposed.

- `IsConnectedReductive G` (from `Reductive/Basic`) says that the structure
  morphism of `G` is smooth and affine, the underlying space of `G` is
  connected, and the base change of `G` to `AlgebraicClosure k` has trivial
  unipotent radical.
- `IsDerivedSubgroup d` (from `Derived/Basic`) says that `d` is a closed
  subgroup inclusion and that `SubgroupFunctor.range d = derivedSubgroup G`.
  This is equality of subgroup functors on every test scheme over `Spec k`,
  including nonreduced tests. `derivedSubgroup G` is the scheme-theoretic
  derived subgroup: the intersection of the ranges of all actual closed
  subgroups of `G` that contain every commutator on every test scheme. It is
  not the abstract commutator subgroup of the rational points `G(k)`.
- The conclusion `IsSemisimple D` (from `Reductive/Semisimple`) has two
  fields. `IsConnectedReductive D` asserts that `D` is smooth, affine and
  connected with trivial geometric unipotent radical. `HasFiniteCenter D`
  asserts that the full scheme-theoretic centre of `D` is represented by an
  actual closed subgroup whose structure morphism is finite.

So the proposition asserts, for every connected reductive `G`, that the
source of every actual inclusion exhibiting its derived subgroup is
semisimple. Semisimplicity, smoothness, connectedness and finiteness of the
centre of `D` are all part of the conclusion; none of them is assumed. Only
the existing derived-subgroup predicate is used; no second notion of derived
group is introduced.

The proposition quantifies over every exhibiting inclusion instead of a
chosen derived group. Two inclusions exhibiting `derivedSubgroup G` represent
the same subgroup functor, so the published
`SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy` gives an isomorphism
of their sources, and `IsSemisimple.of_iso` transports semisimplicity along
it. The choice of inclusion therefore does not matter.

The proposition does not assert that an exhibiting inclusion exists. That is
the separate published `DerivedSubgroupRepresentabilityStatement` in
`Derived/StructureStatement`, which has its own proof ownership. It applies to
every connected reductive `G`, because `IsConnectedReductive G` supplies an
affine structure morphism and smoothness implies local finite type. The
statement is not assumed here, nor is any other structure statement of that
module.

## Source

J. S. Milne, *Algebraic Groups* (2017), source `milne-2017-algebraic-groups`,
SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`,
Proposition 19.21(c), printed p. 402 (PDF p. 418): "Let G be a reductive
group. ... (c) The algebraic group G^der is semisimple of rank at most the
semisimple rank of G." The proposition here is the semisimplicity half of
(c). The rank bound and parts (a) and (b) are not stated.

The source conventions correspond to the Library interfaces as follows.

- Milne's reductive groups (6.46, recalled at the start of the subsection
  "Reductive algebraic groups" of §19.b, printed p. 400 / PDF p. 416) are
  smooth connected groups whose unipotent radical over `k^a` is trivial.
  `Reductive/Basic.md` explains the correspondence with
  `IsConnectedReductive`.
- Milne's Proposition 19.10, printed p. 400 (PDF p. 416), shows that a
  reductive group is semisimple exactly when its centre `Z(G)` is finite. The
  Library's `IsSemisimple` takes this finite-centre form as its definition,
  with the full scheme-theoretic centre, as explained in
  `Reductive/Semisimple.md`.
- Milne's derived group `G^der = DG` (Definition 6.16 and Propositions
  6.17–6.18, printed p. 129 / PDF p. 145) corresponds to `derivedSubgroup`
  and `IsDerivedSubgroup`. `Derived/StructureStatement.md` explains that
  correspondence, which is a derived reformulation.

Milne's proof first reduces to an algebraically closed field. It then uses
19.21(b), the finiteness of `Z(G) ∩ G^der` (obtained from Proposition 12.46),
and the normality of the radical of `G^der` in `G`. A formal proof must also
supply the smoothness and connectedness of `D` and the compatibility of
derived subgroups, reductivity and centres with base change to an algebraic
closure. None of this is proved here. After acceptance, an exact-target proof
task will be published or coordinated.

The retained official errata
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
was read in full. Its only Chapter 19 correction is to Definition 19.7
(almost-simple groups), which is not used here. It corrects neither
Proposition 19.10 nor Proposition 19.21, and has no entry for
Proposition 12.46. Its Chapter 6 caution about 6.19(c)–(e) is commented out
of the HTML rather than displayed, and it does not concern Definition 6.16
or Propositions 6.17–6.18.

## What is not stated

The proposition makes no claim about rational points, rank, the image of `D`
in a quotient of `G`, or groups that are not connected reductive. It neither
proves nor assumes the existence of a derived-subgroup inclusion. It does not
assert that `D` has a simply connected central cover; that is a separate
statement.
