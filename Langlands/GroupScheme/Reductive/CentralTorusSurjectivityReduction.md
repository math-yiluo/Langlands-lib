# Reduction of central-torus surjectivity to a semisimple quotient and perfectness

This module reduces `ReductiveCentralTorusSurjectivityStatement` (a central
torus and the derived subgroup cover a connected reductive group) to two
published statements whose proofs are separate obligations:

- `ReductiveCentralTorusSemisimpleQuotientStatement` (module
  `Langlands.GroupScheme.Reductive.CentralTorusSemisimpleQuotientStatement`):
  every connected reductive group over a field `k` has a closed central torus
  `j : Z ⟶ G` (affine and locally of finite type) such that every affine,
  locally finite type represented fppf quotient of `G` by the range of `j` is
  semisimple;
- `SemisimplePerfectStatement` (module
  `Langlands.GroupScheme.Derived.SemisimplePerfectStatement`): the derived
  subgroup functor of every semisimple field group is the whole group.

## Statement

`reductiveCentralTorusSurjectivity_of_semisimpleQuotient` takes proofs of both
statements, at universe `u`, and returns a proof of
`ReductiveCentralTorusSurjectivityStatement.{u}`. It is an internal
proof-producing `def` whose type is this implication (the `linter.defProp`
linter is disabled for it), so that the module can be published as a
definition artifact before the two hypotheses are proved; it is used exactly
like a theorem.

## Proof

Fix a field `k`, a connected reductive group `G`, and an inclusion
`d : D ⟶ G` of its derived subgroup.

1. The semisimple-quotient statement gives a commutative group scheme `Z`
   and `j : Z ⟶ G` with `Z` affine and locally of finite type, a torus,
   `j` a closed immersion and central, and the semisimplicity property for
   quotients. These five properties of `Z` and `j` are exactly the first five
   conjuncts of the target, so they are passed on unchanged.
2. `G` is smooth, affine and connected because it is connected reductive.
   The torus `Z` is smooth (`IsTorus.smooth`), and the range of a central
   homomorphism is normal (`IsCentral.range_isNormal`). So
   `SmoothNormalQuotient.ofClosedNormal` gives an actual quotient group
   scheme `Q` with projection `q : G ⟶ Q`. Here `Q` is smooth, separated,
   quasi-compact and locally of finite type over `k`, and `q` is smooth (hence
   flat), surjective and quasi-compact. Moreover `q` is a represented fppf
   quotient with kernel the range of `j`.
3. `Q` is affine by the published `affineGroupSchemeQuotient`, so the
   semisimple-quotient property applies to `q`: `Q` is semisimple, and
   `SemisimplePerfectStatement` gives `derivedSubgroup Q = ⊤`.
4. `IsDerivedSubgroup.surjective_comp_of_derivedSubgroup_eq_top` (module
   `Langlands.GroupScheme.Derived.PerfectQuotientImage`) then shows that
   `d ≫ q` is surjective on underlying schemes.
5. `surjective_subgroupProductMap_of_isFppfQuotient` (module
   `Langlands.GroupScheme.Reductive.CentralTorusProductSection`) combines
   this with the fppf-quotient property of `q` and concludes that
   `subgroupProductMap j d` is surjective on underlying schemes, the last
   conjunct of the target.

## Provenance

This is a derived, internal reduction. It follows the proof route recorded in
the Markdown of `ReductiveCentralTorusSurjectivityStatement`, using J. S.
Milne, *Algebraic Groups* (2017), source `milne-2017-algebraic-groups`
(printed page `p` is PDF page `p + 16`):

- Corollary 17.62(b),(d) (printed pp.372–373): for reductive `G` over any
  field, `R(G) = Z(G)_t` is a central torus and `G/R(G)` is semisimple. This
  is the content of the first hypothesis.
- Corollary 21.50 (printed p.440): semisimple groups are perfect. This is the
  second hypothesis.
- Proposition 12.46(b) (printed pp.245–246): for a central torus `T` with
  `G/T` perfect, `T × D(G) → G` has image `G`. Steps 4 and 5 replace Milne's
  argument (that `G/(T · D(G))` is commutative and perfect) by surjectivity of
  `D(G)` onto `G/T` and a section argument on a fibre product.
