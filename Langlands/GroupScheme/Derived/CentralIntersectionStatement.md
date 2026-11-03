# Finiteness of the full central intersection with an actual derived subgroup

Worker 1482, using the exact target and source route supplied by Workers 1367
and 1451.

`Langlands.GroupScheme.DerivedCentralIntersectionFinitenessStatement.{u}` is a
proposition definition. It states finiteness of the full scheme-theoretic
intersection of the centre of a connected reductive group with its derived
subgroup. The module contains no proof of this proposition.

## Exact scope

For every field `k : Type u`, every pair of actual group schemes `G` and `D`
over `Spec k`, and every homomorphism `d : D ⟶ G`, the only premises are
`IsConnectedReductive G` and `IsDerivedSubgroup d`. The universe `u` is arbitrary.
Imperfect fields and positive characteristic are included.

The imported reductive predicate requires smoothness, affineness, connectedness,
and triviality of the geometric unipotent radical. Smoothness and affineness
imply that `G` is of finite type over the field. The imported
`IsDerivedSubgroup d` requires a closed immersion and equality
`SubgroupFunctor.range d = derivedSubgroup G`. The latter functor is the
intersection of the ranges of all actual closed subgroup inclusions containing
every test-scheme commutator. No additional property of `D` or `d` is assumed.

The conclusion supplies an actual group scheme `C` and homomorphism `c : C ⟶ D`
over the same field, with these three properties:

- `IsClosedSubgroup c`: the underlying scheme morphism is a closed immersion.
- `SubgroupFunctor.range c = (center G).comap d`: its range is the inverse
  image of the full scheme-theoretic centre of `G`.
- `IsFinite C.X.hom`: the structure morphism `C ⟶ Spec k` is finite.

All four notions are existing Library or Mathlib predicates. There is no new
definition of a centre, derived subgroup, or intersection.

## Correspondence with the source intersection

Put `S = Spec k`. For every `T : Over S` and `x : T ⟶ D.X`, the asserted range
equality means precisely

```text
(there exists y : T ⟶ C.X with y ≫ c.hom.hom = x)
  if and only if
x ≫ d.hom.hom belongs to (center G).carrier T.
```

By the published definition of `center`, the right side says that for every
test scheme `T'`, every `a : T' ⟶ T`, and every `h : T' ⟶ G.X`, the points
`a ≫ x ≫ d.hom.hom` and `h` commute. These are full functor equalities on all
schemes over the field, including non-affine and nonreduced test schemes.
Closedness of `c` makes a lift `y`, when it exists, unique.

Given an actual closed centre representative `z : Z ⟶ G`, its pullback along
`d` is the scheme-theoretic intersection `D ×_G Z`. The projection to `D`
has exactly the all-test membership condition above, by the pullback universal
property. Under `d`, this is the source's `Z(G) ∩ Gder` inside `G`.
Milne's commutator description of the derived group, Proposition 6.18,
agrees with the published derived functor: containment of the commutator
morphism in a closed subgroup is equivalent to containment of all its
test-scheme commutators. Affine-test factorizations extend to arbitrary tests
by gluing through the closed monomorphism. Once that comparison is proved,
the published `IsRepresentedBy.isoOfIsRepresentedBy` identifies any two
exhibiting derived inclusions compatibly with their maps to `G`. Thus the
source assertion transfers to every `d` in this statement.

Constructing the centre representative, this pullback as an actual group
scheme, its range equality, and its finiteness are future proof obligations.
This description does not supply those Lean proofs. The statement concerns
the centre of `G` intersected with `D`; it makes no assertion identifying it
with the centre of `D`. It retains the entire finite group scheme, including
any nilpotents.

## Original source and independent proof route

The original source is J. S. Milne, *Algebraic Groups: The Theory of Group
Schemes of Finite Type over a Field* (2017), registered as
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The retained PDF is
`/home/taskhub/central-library/Milne--Algebraic groups, the theory of group schemes of finite type over a field (book)--2017.pdf`.
Printed page `p` is PDF page `p + 16`.

Proposition 19.21(b), printed p.402 / PDF p.418, states the finiteness of
`Z(G) ∩ Gder` for a reductive group over a field. The present proposition is
its derived packaging with an explicit finite closed representative inside
each actual exhibiting `D`. The following route uses part (b) independently
of the derived semisimplicity assertion in part (c):

1. Proposition 12.46(a) and its proof, printed pp.245–246 / PDF pp.261–262,
   give finiteness of `T ∩ DG` for any central torus `T` in a connected group
   variety. After passing to an algebraic closure, choose a faithful
   representation and decompose it into `T`-weight spaces. Centrality makes
   these spaces stable under `G`. Commutators have determinant one on each
   space, whereas the action of `T` there is scalar. Each scalar in the
   intersection therefore satisfies a fixed positive power equation.
   Milne concludes that the intersection has finitely many geometric points
   and hence is a finite algebraic group.
2. A scheme-theoretic implementation can express those power equations
   using finite root-of-unity group schemes. The block determinants are
   characters whose closed kernels contain every commutator; the defining
   minimality of `derivedSubgroup` then places the derived subgroup in each
   kernel. This adapts the source argument without assuming an unproved
   Library character-annihilation statement. The scalar bounds retain
   nonreduced roots of unity in positive characteristic.
3. The paragraph before Proposition 19.10 and its proof, printed p.400 /
   PDF p.416, say that the full centre is of multiplicative type and that
   its largest subtorus `T = Z(G)t` has finite index. The multiplicative-type
   assertion is also Corollary 17.62(a), printed p.372 / PDF p.388. Thus the
   intersection with the full centre has a finite kernel from `T ∩ DG` and
   finite image in `Z(G)/T`; equivalently it has dimension zero. As a closed
   subgroup of an affine finite-type group, it is finite. This is the
   finite-index step used explicitly in the proof of 19.21(b).
4. Compare the source subgroups with the all-test predicates, construct the
   pullback representative inside the given `D`, and descend finiteness from
   the algebraic closure. These comparisons and descent need actual Lean
   proofs; no perfectness assumption is introduced.

The proof of part (c) uses part (b), so using derived semisimplicity to prove
the present statement would reverse the intended dependency. The route above
does not use `DerivedSubgroupSemisimpleStatement`, `IsSemisimple D`, or
central-torus/derived product generation. The source propositions and this
route justify the target; unproved Library proposition definitions are not
established results.

## Errata

The complete official author errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
was read at
`/home/taskhub/pilot/literature/J. S. Milne - Errata for Algebraic Groups (2017), HTML snapshot 2026-11-02.html`.
It has no entry for 6.18, 12.46, 17.62, 19.10, or 19.21. The displayed
Chapter 12 corrections concern 12.41 and 12.57, and the Chapter 19 correction
concerns 19.7 and 19.8. The caution about 6.19(c)–(e) is inside an HTML
comment. The determinant-kernel route above uses neither that generation
assertion nor the corrected quotient argument involving 12.41.
