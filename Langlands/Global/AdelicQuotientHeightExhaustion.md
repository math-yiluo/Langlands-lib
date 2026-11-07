# Compact exhaustions of actual adelic quotients by height images

Author: Worker 94.

For any topological group `H` and any subgroup `Γ`, the existing
`LeftCosetSpace Γ` carries its original quotient topology on `Γ \ H`.
`LeftCosetSpace.compactExhaustionImage Γ K` sends a compact exhaustion `K`
of `H` to one of this quotient. Its level `n` is exactly the image
`LeftCosetSpace.mk Γ '' K n`. Continuity of the projection preserves
compactness. Openness sends the inclusion of each ambient level in the
interior of the next to the corresponding quotient inclusion, and
surjectivity gives coverage. This construction needs no normality or
closedness of `Γ`, and makes no separation claim about the quotient.

Fix a number field `F : Type u`, an actual group scheme `G` over `Spec F`,
a matrix representation `rho` of rank `N`, and a subgroup `Γ` of the
original `AdelicGroupPoints F G`. The actual evaluation topology and
existing full representation height are unchanged.
`RepresentationGrowth.adelicQuotientHeightSublevel F G rho Γ B` is the
image of the ambient sublevel of height at most the real number `B`.
Membership is exactly the existence of an actual representative with that
height bound. For a specified representative `g`, membership is equivalently
the existence of `γ : Γ` such that `rho`-height of `γ * g` is at most `B`.
This follows from the original left-coset equivalence relation. The
sublevels are monotone in `B`.

At positive rank, if `g` belongs to ambient level `C`, positive right
translation by `g` sends quotient level `B` into quotient level `B * C`.
Indeed an actual representative `x` is sent to `x * g`, and the published
submultiplicative height bound applies. There are no sign assumptions on
`B` or `C`: the ambient level product law already handles empty sublevels.

Assume now that `G` is affine, `N > 0`, and
`GroupScheme.IsClosedSubgroup rho`, the existing scheme-theoretic closed
matrix embedding condition. Every real quotient sublevel is compact as a
continuous image of the published compact ambient sublevel.
`adelicQuotientHeightCompactExhaustion F G rho Γ hN hrho` is the image
construction applied to the published exact natural height exhaustion.
Its level `n` is precisely the quotient sublevel at `n`, and its membership
formula again uses a representative with height at most `n`.

Every compact subset of the quotient lies in some such level. The proof
uses the compact exhaustion's interior nesting and compact-cover argument;
it does not assume that the full inverse image of a compact quotient set
is compact. The image exhaustions for any two positive-rank closed matrix
embeddings of the same affine group are cofinal, by taking images of the
published ambient containment. Interchanging the embeddings gives reverse
cofinality. A compact subset of the ambient adelic group has height bounded
by some natural number `m`. All positive right translations by its points
then send quotient level `n` into level `n * m`, simultaneously for every
natural `n`.

The module gives named specializations to the existing actual rational
quotient and the existing positive-central rational quotient, over
`F : Type u`. `RestrictionSplitCentre.quotientHeightCompactExhaustion`
specializes to the original restriction split-centre quotient, retaining
its `F : Type`, affineness, and local finite type hypotheses and supplied
`S` and `j`. These are abbreviations of the same construction with the
original subgroup. They need no extra torus, centrality, finite-index,
closed-subgroup, or measure assumptions beyond the displayed hypotheses
of their underlying quotient definitions and the ambient height
compactness hypotheses.

The provenance is internal: this unit consumes
`AdelicRepresentationHeightExhaustion`, the original left quotient's
continuous open surjective projection, the actual quotient definitions,
and Mathlib's compact-exhaustion interface. No external literature
assertion is introduced. The levels are images of ambient height
sublevels; no function on the quotient or continuous choice of
representatives is constructed. This unit supplies no split-component
existence, Hausdorff property, quotient measure, reduction, Siegel-set,
finite-volume, integrability, or cuspidal-density assertion. Those
obligations of the host task retain their existing owners.
