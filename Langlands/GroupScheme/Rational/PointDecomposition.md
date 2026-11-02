# Rational points of dynamic parabolics and their Levi decompositions

This module specializes the published dynamic theory to the rational points of
a group scheme `G` over an arbitrary field `k`. A rational point is the actual
scheme morphism `Over.mk (𝟙 (Spec k)) ⟶ G.X`, with its published group law.
The cocharacter `χ : (Gm (Spec k)).toGrp ⟶ G` is defined over `k`. In particular,
for a torus inclusion `i` and `μ : cocharacterLattice T`, take
`χ = CommGroupScheme.groupHom μ ≫ i`.

The abbreviations `RationalPoint.parabolic`, `RationalPoint.levi` and
`RationalPoint.unipotent` are the carriers of the published dynamic parabolic,
centralizer and unipotent subgroup functors at this test scheme. They are
subgroups of the same group `G(k)`, with no separate model or structural data.

## Sources and scope

- Renard, *Représentations des groupes réductifs p-adiques*, French version dated
  9 July 2026, V.3.1 (printed p.110, one-based PDF p.116), states the Levi
  decomposition, with the Levi normalizing the unipotent radical. V.3.8
  (printed p.111, PDF p.117) fixes the standard torus, minimal parabolic and
  its Levi. Source ID:
  `renard-2026-representations-groupes-reductifs-padiques`.
- Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
  Lemma 2.1.5 (printed p.50, PDF p.76) identifies the unipotent subgroup with
  the kernel of the limit homomorphism. Proposition 2.1.8(2), and Step 2 of
  its proof (printed pp.53–54, PDF pp.79–80), gives the semidirect
  decomposition and the limit projector onto the centralizer.
  Source ID: `conrad-gabber-prasad-2015-pseudo-reductive`.

Renard's chapter concerns rational points over a nonarchimedean local field.
The implemented arbitrary-field dynamic statements are derived
specializations of the already published modules
`Langlands.GroupScheme.Dynamic.Decomposition` and `Dynamic.LimitMap`.
Their general separated-scheme arguments supply the broader scope, rather
than an assertion that Renard states this generality.
CGP writes the Levi factor first in its semidirect product notation.
Mathlib puts the normal factor first, so the implemented equivalence is
`U(k) ⋊[leviConj χ] L(k) ≃* P(k)`, with map `(u,l) ↦ u*l`.

## Implemented facts

The inclusions of the Levi and unipotent subgroups in the parabolic,
normality of the unipotent subgroup inside the parabolic, and normalization
by the Levi require no affineness assumption. They directly specialize
`Dynamic.centralizer_le_parabolic`, `unipotent_le_parabolic`,
`unipotent_subgroupOf_parabolic_normal` and
`centralizer_le_normalizer_unipotent`. The action `leviConj` is conjugation
by the actual rational points, and `leviInclusion` is subgroup inclusion.

The remaining declarations assume only that the structure morphism of `G`
is affine. Mathlib's `IsSeparated.of_isAffineHom` supplies separatedness.
`IsConnectedReductive.isSeparated` also gives this explicitly for any
connected reductive `G`, using the published affineness field of
`IsConnectedReductive`. No smoothness or field restriction is needed in
the decomposition proof.

The trivial intersection follows because a centralizing point has itself
as limit, while a unipotent point has limit one, and limits are unique for
a separated target. Both unique-factorization theorems quantify over pairs
of ambient rational points, require the specified subgroup memberships,
and assert the product equality:

- For `g ∈ P(k)` and its unique limit `l ∈ L(k)`, the factors in the order
  `U(k)L(k)` are `(g*l⁻¹,l)`. The first factor has limit one by
  multiplicativity. Any other pair has Levi factor equal to the limit of
  `g`, and cancellation determines its unipotent factor.
- In the order `L(k)U(k)`, the pair is `(l,l⁻¹*g)`, with the same limit
  and cancellation argument.

`limitHom`, `ker_limitHom`, `limitHom_comp_leviInclusion`,
`limitHom_leviInclusion`, `limitHom_surjective`, `semidirectEquiv` and
`limitHom_comp_semidirectEquiv` specialize their published dynamic
counterparts. The kernel equality uses `subgroupOf` because the kernel
is a subgroup of `P(k)`. The section is the actual inclusion of `L(k)`.
The equivalence's product formula is recorded by
`semidirectEquiv_apply_coe`.

These declarations give rational-point decompositions for every field-defined
cocharacter. They do not assert the Borel–Tits classification or identify
the standard-cocharacter intersections with one dynamic subgroup; those
are separate statements of the standard-parabolic task.
