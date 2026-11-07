# Character twists and compact-open completion

## Source and purpose

Renard, *Représentations des groupes réductifs p-adiques*, 2026 version,
I.1.4 (printed p.9 / PDF p.15) and VI.9.7 (printed pp.205–206 /
PDF pp.211–212), realizes completion as compatible compact-open fixed-vector
components. His VI.9.7 theorem uses the unnormalized opposite Jacquet module;
the published represented-parabolic statement uses the normalized one.

This derived construction proves the compact-character comparison needed to
pass between these completion models. It reuses the published normalized
finite-orbit average, positive-character triviality on compact subgroups,
and the intrinsic closed Haar character. It does not assert the Jacquet
completion isomorphism itself.

## General compact-trivial twist

Let `G` be a topological group, `V` a complex module, and `ρ` and `twist χ ρ`
smooth representations on the same module. Group and carrier universes are
independent. No local compactness or existence of compact open subgroups is
required for this general comparison.

`Compact.averageMap_twist` assumes that the compact open averaging subgroup
`K` lies in `ker χ`. The restricted representations on `K` are equal, so their
finite-orbit means, and hence their normalized averaging linear maps, are equal.

If every compact open subgroup lies in `ker χ`, `completion_twist_eq` gives an
equality of submodules of `CompactOpenSubgroup G → V`: the defining transition
equations for the two completions have equal averages.
`CompactCompletion.twistEquiv` packages this equality as a complex linear
equivalence from the twisted completion to the original completion. The forward
and inverse maps leave every component unchanged, as their application lemmas
state. This compares vector spaces of compatible families; no equivariance
between the differently twisted actions is claimed.

## Positive and intrinsic Haar normalization

For a positive character `δ : G →* ℝ≥0ˣ` with open kernel,
`inverseHalfCharacter_compact_le_ker` proves that every compact open subgroup
is killed by `Jacquet.inverseHalfCharacter δ`. The proof uses
`PositiveCharacter.eq_one_on_compact`, followed by the existing equivalence
between `δ(g) = 1` and its inverse half being one.
`inverseHalfTwistEquiv` specializes the identity-on-families equivalence to
this normalization, with the displayed forward component formula.

For a locally compact nonarchimedean ambient group `A`, a closed subgroup `N`,
and a subgroup `M` normalizing `N`, consider a continuous homomorphism
`ι : G →* M`. The character
`(HaarModulus.closedInverseHalfCharacter N hN M hMN).comp ι`
is the actual intrinsic Haar normalization pulled back to `G`.
`closedInverseHalfCharacter_compact_le_ker` proves its compact triviality:
the corresponding positive character has open kernel by the existing closed
Haar theorem and continuity of `ι`, and positive compact triviality then applies
on `G`. No closedness of `M`, compact-triviality assumption, or modulus comparison
premise is added.

`closedInverseHalfTwistEquiv` consequently compares its twisted completion
with the original one, with each component unchanged. The compact triviality
lemmas need no vector space or representation. All equivalences accept any
proof of smoothness for the displayed twist, so they can use the smoothness
proof already supplied by an actual normalized Jacquet object. The relevant
smoothness also follows from the existing open-kernel twist theorem.

## Remaining obligations

This unit supplies the character comparison for completion spaces. The
specific Levi-point specialization, the cofinal parabolic subgroup system,
the stable-image limit comparison, and both exact parent proof targets remain
separate obligations. No new premise has been added to either parent statement.
