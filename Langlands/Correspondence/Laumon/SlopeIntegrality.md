# Integrality of ℓ-adic slopes

Laumon (1987), Théorème (2.1.2.6), p. 153: for an `I`-module `V` the slopes are rational, for
every slope `λ` the number `λ · r(V_λ)` is an integer, and `s(V)` is an integer; a fortiori for
`G`-modules. Laumon calls it a reformulation of the Hasse–Arf theorem (Serre, *Local Fields*,
IV §3, p. 76) and refers to Katz 1983, pp. 211–215. Katz deduces it (p. 213) from the integral
break-points of the Swan polygon of a representation of inertia; his Lemma and Corollary
(pp. 213–214) show that a representation of `P` alone extends to an open subgroup of `I`
through an isomorphic finite quotient, so that its slopes are rational but `λ · r(V_λ)` need
not be an integer. The integrality of the Swan conductor of a finite-image representation of
inertia is Serre VI §2, Theorem 1 and Corollary 1', pp. 99–101 (the Artin conductor is a
natural number, and the Swan conductor is the Artin conductor minus the codimension of the
inertia invariants).

Notation is that of `Langlands.Correspondence.Laumon.Slopes`: `G^u` are the Library's absolute
upper ramification groups, `V_λ = slopeSummand f A λ` and `s(V) = ladicSwan f A`.

This module carries out the row `SlopeIntegrality` of §4.1 of the [design note for Laumon's local Fourier bijection](../../../notes/henniart/laumon-local-fourier-weil-conjectures-design.md), with its two
statements under the names of the row.

## `FiniteInertiaPositiveBreakModelStatement`

For `ℓ ≠ p` (`((ℓ : ℕ) : 𝓀[K]) ≠ 0`) and every continuous representation `A` with a finite model
of the inertia group `Langlands.LocalGalois.SepClosed.absoluteInertia K Ω` (as a topological
subgroup of `Ω ≃ₐ[K] Ω`), there is a representation `B` of the inertia group which is continuous,
has a finite model and finite image (`Set.range B.representation` is finite), has the same rank,
and for every `u > 0` has a space of vectors fixed by `G^u` of the same dimension as that of `A`.

This is the finite model of the positive breaks used to bring the finite-image results of the
Library to `ℓ`-adic `I`-modules. The construction behind it is the following. For an
irreducible `I`-module, choose a stable lattice over the integers of a finite extension `L` of
`ℚ_ℓ`; let `H` be the compact image and `P_H` its finite wild image (`WildImageFiniteStatement`
in `Langlands.Correspondence.Laumon.Slopes`). The kernel `U` of reduction of `H` modulo the
maximal ideal is open, normal and pro-`ℓ`, so `U ∩ P_H = 1`. As `H/P_H` is a quotient of the
procyclic tame inertia `I/P` (Laumon (2.1.1)), commutators of `U` with `H` lie in `U ∩ P_H`,
so `U` is central and acts by scalars. The scalar character on the open image of `U` in
`H/P_H` takes principal-unit values; it extends to a continuous character of the procyclic
quotient by extracting an `ℓ^a`-th root in a finite extension of `L` on the `ℓ`-primary factor
and taking the trivial character on the prime-to-`ℓ` factor. Twisting by the inverse of this
tame character kills `U`, gives finite image and changes nothing on `P` and on the positive
upper groups. For a general `I`-module, sum these models over the factors of a composition
series; positive upper invariants are exact because those groups act through finite `p`-groups
and `E` has characteristic zero.

## `SlopeIntegralityStatement`

For `ℓ ≠ p`, a group `H` with a topological embedding `f : H →* (Ω ≃ₐ[K] Ω)` whose image
contains the inertia group (so `I`-modules and `G`-modules), and a continuous `A` with a finite
model:

1. every slope (every `μ` in `slopeSupport f A`) is a rational number;
2. for every real `μ` and every subspace `W ⊆ V_μ` stable under the elements of `H` mapped into
   inertia, `μ · dim W` is an integer; in particular `μ · dim V_μ` is (take `W = V_μ`, which is
   `H`-stable by `SlopesExactStatement`);
3. `s(V)` is a natural number.

Clause 2 is stated for every inertia-stable block of a slope summand, not only for `V_λ`. Such a
block `W` is itself an `I`-module whose only slope is `λ` (by the exactness clauses of
`SlopesExactStatement`, the slope-`λ` part of `W` is `W ∩ V_λ = W`), so the block form is
Laumon's statement applied to `W`. It is the form needed for Proposition (2.1.2.7)(ii) (see
`Langlands.Correspondence.Laumon.SlopeCalculus`), where Laumon's proof applies integrality to
simple `P`-submodules, for which, by Katz's remark, it can fail.

## Generality

Both statements are for all nonarchimedean local fields, of either characteristic: the
Hasse–Arf theorem and Serre VI §2, Theorem 1, hold for complete discretely valued fields with
perfect residue field, so for mixed and equal characteristic. Laumon states (2.1.2.6) for
henselian traits of equal characteristic.

## Inputs of the proofs

This module states the results and does not prove them. The proof of the integrality uses
`FiniteInertiaPositiveBreakModelStatement` to pass to a finite-image model, factors that model
through a finite inertia group `Gal(L/K)_0` by the surjectivity of inertia restriction
(`Langlands.Ramification.Local.AbsoluteInertiaRestrictionSurjectivityStatement`, a clause of the
statement proved by `Langlands.Ramification.Local.inertiaSurjectivityPresentationAndConductorIndependence`),
identifies its positive upper fixed spaces by
`Langlands.Ramification.Wintenberger.localAbsoluteUpperFiniteImage`, compares with complex
coefficients through the fixed-space dimensions, and applies to each slope block the
weighted-break formula `Langlands.Ramification.Local.FiniteUpperBreakWeightedSwan` (proved by
`Langlands.Ramification.Local.finiteUpperBreakWeightedSwan`) together with the integrality of the finite inertia
Swan conductor. For `p`-adic fields the latter is
`Langlands.Ramification.Padic.exists_nat_inertiaSwanConductor`; in characteristic `p` the same
result of Serre VI §2 is the input. The total rank and the positive fixed dimensions account for
the slope-zero multiplicity.

## Declarations used

The module imports `Langlands.Correspondence.Laumon.Slopes`. It uses `slopeSummand`,
`slopeSupport` and `ladicSwan` of that module and the Library's
`localAbsoluteUpperRamificationGroup`, `absoluteInertia`, `Langlands.fixedVectors`,
`IsLadicContinuous` and `IsLadicDefinedOverFiniteExtension`. It uses no declaration of
weil-conjectures. Every declaration of this module depends at most on `propext`,
`Classical.choice` and `Quot.sound`.
