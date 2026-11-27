# Spherical pair Euler products at finite completions

`sphericalCuspidalPairCompletionEuler` compares actual cuspidal pairs of
arbitrary positive ranks over a number-field extension with compact adelic
quotients. It concerns the finite Euler factors at one lower place and all
places above it. Both members of the upper pair have the residue-degree
powers of the respective lower Satake spectra. The first member below is
twisted by each given global norm character times a common Hecke character.
The first member above is twisted by the norm pullback of the common
character. The theorem uses pair polynomials certified for the twisted
presentations with the supplied local additive characters and self-dual
measures. It assumes that the distinct restrictions of the global
characters are exactly the local norm-trivial characters, each occurring
with multiplicity equal to the number of upper places. It identifies the
product of the lower finite Euler values with the product of the upper values.

The proof forms the finite set of distinct restrictions of the global norm
characters and selects a representative index for each local restriction.
Two indices with the same restriction give the same twisted local class and
the same certified polynomial. At each upper place, the bundle for the
completion is indexed by the common residue prime. Local compatibility
of the idele-class norm identifies the upper character with the pullback
by the completion norm. The spherical pair norm comparison then
identifies the product of distinct local terms with the single upper
term. Evaluating the polynomial identity uses
`q_w^(-z) = (q_v^(-z))^f` for the residue degree `f`. Grouping the lower
terms by their restrictions supplies the multiplicity of each term and
thus the product over the upper places.

This is the finite-place product step of Henniart and Lemaire, *Changement
de base et induction automorphe pour GL_n en caractéristique non nulle*
(2011), II.6.19, printed p. 133 (PDF p. 141). The retained copy is registered
as `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
The local polynomial proof applies to both ramified and unramified common
twists wherever the original two pairs have the stated spherical spectra.
