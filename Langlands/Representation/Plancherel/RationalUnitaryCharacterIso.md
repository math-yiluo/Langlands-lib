# Unitary characters and kernel-scaled Haar measures under scheme isomorphisms

This module, whose provenance is derived, transports actual unitary unramified character groups
through an isomorphism of affine group schemes over a nonarchimedean local
field. Waldspurger I.1 introduces rational algebraic characters on printed
p. 238 and fixes the norm-kernel and Haar conventions on printed p. 239
(PDF p. 5). The application is the full-group standard Levi in the lower
inclusion of VIII.4.2, printed p. 330 (PDF p. 96).

`rationalUnitaryCharacterIso` uses the existing restriction maps along the two
inverse scheme morphisms. Each restriction already preserves the kernel of all
actual rational-character norms. The inverse laws follow from the scheme
isomorphism laws on points, and continuity is that of the existing restriction
maps. No artificial norm family is introduced.

For a morphism from an affine commutative group scheme, restriction of a
transported character along its composite with the isomorphism equals the
original restriction. This identifies the two restriction kernels and proves
equality of their `Nat.card` values, using the Lean convention of zero for an
infinite type.

For affine group schemes locally of finite type, the unitary character groups
are compact and their Haar probabilities are carried to one another by this
isomorphism. For a central source morphism with the displayed finite-index
valuation-image hypotheses on both sides, the Library's kernel-scaled Haar
measure is the restriction-kernel cardinality times that probability. The
hypotheses give finite kernels, and the equal cardinalities give transport
of the scaled measures.

When the central morphism exhibits the maximal split central torus, the
Library theorem `isLocallyMeasurePreserving_rationalUnitaryUnramifiedCharacterRestrict`
gives the local restriction normalization of Waldspurger I.1. The
scheme-isomorphism comparison uses that same scale in the full-Levi
split-component application.
