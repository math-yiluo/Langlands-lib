# The actual-centralizer character-restriction comparison

`CentralizerValuationComparisonStatement` states the comparison needed to use
`centralizerValuation` for the actual algebraic centralizer of a maximal split
torus. It ranges over every nonarchimedean local field, including mixed and
equal characteristic, every connected reductive group scheme `G`, and every
chosen maximal split torus `i : S → G`. The homomorphism `j : Z → G` must be a
closed subgroup and represent the all-test-scheme functor `torusCentralizer i`;
`s : S → Z` must satisfy `s ≫ j = i`. No arbitrary centralizer subgroup can
satisfy the input merely by being assigned that name.

The conclusion is exactly bijectivity of `restrictionEvaluation s`, the map
from `V(S)` to real-valued additive homomorphisms on the actual rational
characters of `Z` given by evaluation after actual restriction to `S`.
It provides the comparison argument used by `centralizerValuation s h` and
its character-normalization and uniqueness laws. This file states the target;
it proves neither that comparison nor the existence of a centralizer model.
There is no building, special point, parahoric or decomposition assumption.
No hypothesis restricts the group to the split, quasi-split or tame case.

This is a derived formulation of Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), §2.6(d), printed p.103/PDF134, and §5.2, printed
p.187/PDF218. The first passage uses injective finite-index restriction from
a connected reductive group's rational characters to its central split torus;
the second applies the resulting valuation with `S` as the centralizer's
maximal central split torus. The present real evaluation map expresses that
comparison in the Library's actual real cocharacter space. Proving it still
requires the actual centralizer/split-component comparison and the real-dual
consequence of finite-index character restriction. The existing
`CharacterRestrictionStatement` is not itself this theorem and does not make
this statement a proof.

Read these passages with *Corrections and additions*, 1 November 2024,
PDF24–25 and 30. The valuation that this comparison enables is normalized by
`χ(ω_Z(z)) = ord_F(χ(z))`, with positive order. Thus the positive-root chamber
uses `α(ω_Z(z)) ≥ 0`. Bijectivity is a comparison of real spaces, not an
identification of the actual valuation image with the full integral
cocharacter lattice. It supplies no rank, index, representative-set or
Cartan-bijection result. The subsequent parahoric and maximal-compact targets
retain their different quotient relations.
