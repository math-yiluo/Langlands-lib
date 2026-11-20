# Pairing actual semistandard wave packets for nonconjugate Levis

`WavePacketPairing.NonconjugatePairingStatement` is the Prop-valued target
for VII.2.2(i) of J.-L. Waldspurger, *La formule de Plancherel pour les
groupes p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2
(2003), 235–333. The registered source is
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
VII.2.2 is on printed pp. 318–319 (PDF pp. 84–85), VI.3.1 on printed
pp. 302–305 (PDF pp. 68–71), and the ambient Haar convention in I.1 on
printed p. 240 (PDF p. 6). [Original article](https://doi.org/10.1017/S1474748003000082)

The field is an arbitrary nonarchimedean local field with finite residue
field. The ambient group scheme is affine, locally of finite type and
connected reductive. The field and complex representation-carrier
universes are independent. The source special compact, intrinsic
semistandard indices, literal rational Levi subgroups, split components
and Haar measures on their Borel central quotients use the existing
Library constructions. The inputs admit nonsplit and non-quasisplit
ambient groups, positive characteristic and rank zero.

The input `OrbitPacketData` retains the primitive scalar prerequisites,
including the actual continuation domains, generic irreducibility and
inverse regularity on the entire unitary locus. The source I.1 character
scale and reciprocal self-twist factor come from
`SourceMeasure.normalizedOrbitMeasure` in the existing packet, with the
actual valuation-image finite-index premise. `SourceCompactCompatibility`
requires the published special-compact properties and a common compact
for the coefficient and scalar pictures, as in the preceding VI.3.1
component continuity target. The integral uses `RationalDynamicSource.ambientHaar`.
`RationalDynamicSource.ambientHaar_self` gives the source normalization
`dg(K) = 1`.

The named conclusion is the ambient pairing
`∫ g, conj (f_psi' g) * f_psi g = 0` for every two smooth coherent sections
at actual pairs `(P,O)` and `(P',O')` whose literal Levi subgroups are
nonconjugate in `G(F)`. `LevisConjugate` means that conjugation by some
point of `G(F)` maps the source subgroup onto the target subgroup.
`levisConjugate_of_isRationallyConjugate` proves the passage from the
corresponding all-test equality by evaluating on rational points and
applying the published inner-conjugation formula. The paper's proof of
orthogonality uses VI.4.1(i) and VII.1.2 in the semisimple-rank ordering,
then conjugate symmetry in the other ordering.

The following derived adapters use the same actual packet at every step.

| Declaration | Implemented construction or exact condition |
| --- | --- |
| `ComponentSchwartzMembershipStatement` | The actual `GlobalSynthesis.componentPacket` belongs to the existing Schwartz submodule for every section. This is the VI.3.1 membership prerequisite. |
| `componentSchwartzMembership_of_componentContinuity` | Applies the published VI.3.1 component continuity target to the identical section in `OrbitSectionSpace` and uses its exact evaluation formula. |
| `schwartzPacket`, `schwartzPacket_apply` | Codomain restriction of the existing linear packet using that membership. Pointwise evaluation is the original density-weighted integral. |
| `integrable_pairing` | `Space.integrable_conj_mul` with the actual rational `L2Weights` gives integrability of the displayed scalar integrand under prior Schwartz membership and the ambient square-integrable-weight premise. |
| `NonconjugatePairingStatement` | The unproved VII.2.2(i) conclusion on the actual source-normalized packets. |

This pair is the nonconjugate part of VII.2.2 and supports the later
VII.2.3 deduction. The conjugate-Levi formula requires the separately
owned normalized comparison and its quotient and representative laws.
