# Left exactness of the actual pseudo-forgetful functor

This is a focused internal proof for the actual pseudo-F of Renard I.2.3–4.
The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`
(SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).
The exactness theorem and its proof are printed pp.18–19 / PDF24–25.
The registered `renard-2010-corrections-complements` PDF1 confirms the directions
of the two induction adjunctions; PDF1–2 and PDF18–19 contain no change to this
left exactness assertion.

The construction uses the original regular left B-action on the actual carrier B,
the specified commuting right A-action, and the published residual action on
`NonUnitalModuleHom B B M`. The auxiliary kernel proof is restricted to this
actual carrier B. It is internal derived content, not a claim that the source
states a general theorem for arbitrary nonunital rings.

For a morphism `f : M ⟶ N`, a family of B-linear maps into M annihilated by
postcomposition with f lifts pointwise to the concrete subtype kernel of f.
The original B-linearity of each lift follows from the published kernel lift.
The family is additive and A-linear by evaluating the original family identities
and using equality of subtype values. Equality after the kernel inclusion proves
uniqueness. Thus the actual ambient Hom preserves kernels, and its additivity
gives finite-limit preservation. The published inclusion and nondegenerate-part
functors preserve homology, hence finite limits. Their actual composite is
`RenardHomFunctors.pseudoF`. The published finite-limit comparison proves
`SequenceLeftExact`, including exactness and preservation of the initial mono
for every exact short complex with that mono.

The independent universes are `uA`, `uB` and source carrier `v`; the target
carrier is exactly `max uB v`. No universe comparison, nontriviality, coefficient
action or unit-action hypothesis is used. Renard works with complex algebras;
this internal result concerns arbitrary original additive nonunital modules.
Complex-linearity, coefficient and unitization comparisons remain separate.
