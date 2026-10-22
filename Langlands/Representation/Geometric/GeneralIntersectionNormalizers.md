# Normalizer maps for the geometric-lemma corrections

This construction supplies the actual closed subgroups and normalizer maps
needed to form the two Haar correction characters in Bernstein--Zelevinsky
(1977), section 5.1. It uses the actual intersection Levi groups of
`GeneralIntersections` and does not introduce a substitute modulus character.

For subgroups `M,N,U,Q` of a group `G`, the correction subgroup is the existing
`Langlands.Geometric.intersectionSource U Q w` from `WeylDefinitions`.
It is `U ∩ w⁻¹(Q)`: its elements are exactly those `g ∈ U` with `w g w⁻¹ ∈ Q`.
The theorem `correctionSubgroup_eq` identifies it with the conjugate-subgroup
notation already used in `GeneralIntersections`.

The group `intersectionIn M N w` consists of `m ∈ M` with
`w m w⁻¹ ∈ N`. If `M` normalizes `U`,
`intersectionToRadicalNormalizer` includes this group in the actual normalizer
of `U`. If additionally `N` normalizes `Q`,
`intersectionToCorrectionNormalizer` includes the same group in the actual
normalizer of `U ∩ w⁻¹(Q)`. Both homomorphisms send `m` to its underlying
element in `G`, as their value lemmas prove.

The second normalizer statement follows by pulling back normalizer
containment along conjugation and then intersecting the two normalized
subgroups. The generic formulation needs no decomposability or semidirect
product hypotheses. In the geometric-lemma application, `N ≤ Q` supplies
`N ≤ normalizer Q`, since every subgroup normalizes itself.

Both inclusions are continuous in the induced subgroup topologies on any
topological ambient group. If multiplication and inversion are continuous
and `U,Q` are closed, their correction subgroup is closed by continuous
preimage and intersection. Local compactness and Haar measures are not used
in these elementary constructions.

The first correction in BZ77 is
`epsilon₁ = mod_U^(1/2) * mod_(U ∩ w⁻¹(Q))^(-1/2)` on `M ∩ w⁻¹(N)`.
The second is obtained by interchanging `(M,U,P)` and `(N,V,Q)` and
replacing `w` by `w⁻¹`, giving
`epsilon₂ = mod_V^(1/2) * mod_(V ∩ w(P))^(-1/2)` on `N ∩ w(M)`.
The homomorphisms here provide the concrete domains needed for both formulas.
This module does not construct either Haar modulus, assert its open kernel,
or define the resulting correction characters or orbit functors.

Original source: Bernstein and Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), section 1.7, printed 444 (PDF 5),
and section 5.1, printed 459–460 (PDF 20–21).
Literature ID `bernstein-zelevinsky-1977-induced-i`;
SHA-256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The normalizer maps and their elementary proofs are internal constructions
that justify the domains of the source's two displayed Haar corrections.

Author: Worker 14.
