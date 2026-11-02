# Relative Weyl conjugation of actual subgroups

This internal group construction extends `Langlands.Group.RelativeWeyl`.
Its only ambient assumption is a group `G`; `T` and every other subgroup are
actual `Subgroup G` objects. No root realization, reductivity, topology,
representation theory or positive-rank assumption is used.

## Source and mathematical meaning

Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026 edition,
V.4.3, printed p.119 / PDF p.125, defines
`W_M = N_M(A_empty)/Z_M(A_empty)` and embeds it into the ambient Weyl group.
It then defines `w · M = g M g⁻¹` using a normalizer lift of `w` and explains
lift independence by `Z_G(A_empty) = M_empty ⊆ M`.
The registered original is
`renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The text and rendered source page were read directly.

The Lean construction proves this lift independence at the elementary group
level, for every subgroup containing `Z_G(T)`. Thus it applies to standard Levis
once the shared reductive adapter supplies their actual subgroup values and
centralizer containment. It does not prove that an arbitrary overgroup is a
Levi, that a conjugated Levi is standard, or that a root-label description
matches these actual subgroups. Those remain separate realization obligations.

## Declarations and proof route

`conjugateSubgroup g L` is the image of `L` under the actual map
`x ↦ g*x*g⁻¹`. Its identity and product laws are proved by subgroup image
composition and the conjugation formula. An element of `L` preserves `L`
under this conjugation.

`conjugateSubgroup_centralizer` uses the normality of the centralizer inside
the normalizer to show that each normalizer lift preserves the full centralizer.
Consequently a conjugate of an overgroup of that centralizer is again an
overgroup.

`conjugateSubgroup_eq_of_mk_eq` takes two lifts `n,m` with equal classes in
`RelativeWeyl.Weyl T = N_G(T)/Z_G(T)`. The quotient relation puts `n⁻¹*m` in the
centralizer and therefore in `L`. Conjugation by that element preserves `L`;
writing `m = n*(n⁻¹*m)` proves equality of the two image subgroups.

`CentralizerOvergroup T` is the subtype of actual subgroups containing
`Z_G(T)`. `weylConjugate` is quotient elimination using the proved
lift-independence lemma, and `weylConjugationAction` gives a genuine action of
the actual Weyl quotient on this subtype. `mk_smul_overgroup` exposes the
actual representative formula. `inclusion_smul_overgroup` proves that the
image of `WeylIn T L` in the ambient Weyl quotient fixes `L`, since its
representatives lie in `L`.

`weylTransporters T L L'` is the actual set `{w | w · L = L'}`, corresponding
to Renard's `W(L,L')` with source first and target second.
`mem_weylTransporters_mk` identifies it with equality of actual subgroup images
for any specified lift.

## Transport boundary

Lift independence here concerns image subgroups. It does not make the maps
`L ≃* L'` associated to different lifts equal on elements. Those maps can
differ by inner conjugation. The existing `conjugationEquiv` continues to take
an actual ambient element and the subgroup image equality. Continuity,
pullback of smooth representations, compatibility of normalization and
lift independence up to representation isomorphism or on exact K0 classes
remain separate obligations owned by the actual-functor adapter. In
particular this construction neither assumes nor proves Weyl-conjugacy of
induced K0 classes, Aubert identity (1.2), or any Theorem 1.7 assertion.

The construction is independent of finiteness and therefore includes the
empty-root case. Triviality of the ambient Weyl quotient in that case still
uses the separate actual Coxeter realization from `RelativeWeylIndexing`;
it does not follow merely from centralizer containment.
