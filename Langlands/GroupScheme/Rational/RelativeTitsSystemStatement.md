# Statement: the relative Tits system of a reductive group

This module states that the actual rational-point data of a connected reductive group form
the Tits system of Borel–Tits §§5.15–5.18 and Renard V.4.1. It contains no proof of that
statement. The proved results are elementary consequences of the predicate.

## The data

The setting is a field `k`, a group scheme `G` over `Spec k`, a commutative group scheme `T`,
a homomorphism `i : T ⟶ G` and a cocharacter `ν` of `T`. All the data are published Library
constructions on the categorical rational-point group `G(k) = (Over.mk (𝟙 (Spec k)) ⟶ G.X)`.

- `B = standardParabolicPoints i ν ∅`: the rational points of the minimal standard
  parabolic `P_∅`, the subgroup `P_k` of Borel–Tits and `P_∅` of Renard.
- `N = normalizerPoints i`: the rational points normalizing `i`. This is the
  morphism-defined normalizer, the group `N_k = 𝒩(S)_k` of Borel–Tits.
- The Weyl map is `QuotientGroup.mk'` onto
  `relativeWeylGroup i = normalizerPoints i ⧸ centralizerPoints i`, the actual quotient
  `N(k)/Z(k)`.
- `S = simpleRelativeReflections i ν`: the elements of `N(k)/Z(k)` that act on the span
  of the relative roots as a reflection in a simple relative root of `ν`
  (`Rational.RelativeReflection`).

## The predicate `HasRelativeTitsSystem i ν`

`HasRelativeTitsSystem i ν` is the conjunction of three parts.

1. `Langlands.Group.IsTitsSystem B N (QuotientGroup.mk' _) S` (`Langlands.Group.TitsSystem`).
   Spelled out for this data, it says:
   - The kernel of `N(k) → N(k)/Z(k)` is `B ∩ N(k)`.
   - `B` and `N(k)` generate `G(k)`.
   - `S` generates `N(k)/Z(k)` and consists of elements of order `2`.
   - Bruhat multiplication axiom: `s B w ⊆ B w B ∪ B s w B`.
   - Nondegeneracy: `s B s ≠ B`, in the form `n B n⁻¹ ⊄ B` for every representative `n`
     of `s`.

   The last two are stated for all representatives in `N(k)`.
2. Every simple relative root `α` has exactly one `w ∈ N(k)/Z(k)` with
   `IsRelativeReflection i α w`.
3. Two simple relative roots with a common relative reflection are equal.

Parts 2 and 3 are the simple-reflection compatibility. Together they say that
`α ↦ r_α` is a bijection from `simpleRelativeRoots i ν` onto `S`. So `S` is the set of
fundamental reflections `r_a` (`a ∈ _kΔ`) of Borel–Tits §5.16 and `S_∅` of Renard V.4.1.
Since `ker (QuotientGroup.mk' _)` is `centralizerPoints i` seen in `N(k)`, part 1 contains
the identity `B ∩ N(k) = Z(k)`. It is extracted as the theorem
`HasRelativeTitsSystem.inf_eq`.

## The statement

`RelativeTitsSystemStatement` asserts `HasRelativeTitsSystem i ν` for every universe-`u`
field `k`, every `G` with `hG : IsConnectedReductive G`, every `i` with
`hi : IsMaximalSplitTorus i` and every cocharacter `ν` with `IsGenericCocharacter i ν`.
The statement uses the instances `hG.isAffineHom` and `hi.isSplitSubtorus.mono`, in the same
way as the published `RationalBruhatStatement` and `StandardParabolicPointsStatement`. No
splitness of `G`, perfectness, characteristic or local-field hypothesis is made, and the
field is arbitrary, as in Borel–Tits. The generic cocharacter `ν` fixes the chamber, which
is the order on `_kΦ` in Borel–Tits §5.12. Its positive and simple relative roots are those
of the published `positiveRelativeRoots` and `simpleRelativeRoots`. Nonreduced relative
root systems are included.

The target does not assume the Bruhat decomposition, the Tits axioms, a Coxeter
presentation, the relative root system or the faithfulness of the Weyl action. Each of
these is either a conclusion of the statement or a separate Library statement. This module
does not restate `RationalBruhatStatement`, `StandardParabolicPointsStatement` or
`StandardParabolicEndpointsStatement`, and it does not import them. The comparison of the
standard parabolic subsets `B W_J B` of this Tits system with `standardParabolicPoints i ν J`
and `standardRelativeWeylGroup i ν J` is not part of this module. It belongs to a separate
unit of the same task.

## Rank zero

When `simpleRelativeRoots i ν = ∅`, the set `S` is empty (`simpleRelativeReflections_eq_empty`).
The Tits axioms then force `N(k)/Z(k)` to be trivial and `B = G(k)`. The theorems are
`HasRelativeTitsSystem.eq_one_of_simpleRelativeRoots_eq_empty` and
`HasRelativeTitsSystem.eq_top_of_simpleRelativeRoots_eq_empty`. This matches Borel–Tits
§5.12, where `_kP_θ` equals `G` for `θ = _kΔ`, so `P_∅ = G` when `_kΔ = ∅`. It also matches
the trivial Weyl group of the empty root system. These are consequences of the predicate,
not extra hypotheses.

## Proved consequences

For `h : HasRelativeTitsSystem i ν`:

- `h.isTitsSystem`: the Tits-system part.
- `h.existsUnique_isRelativeReflection` and `h.eq_of_isRelativeReflection`: parts 2 and 3.
- `h.inf_eq`: `standardParabolicPoints i ν ∅ ⊓ normalizerPoints i = centralizerPoints i`.
  It uses `QuotientGroup.ker_mk'`, `centralizerPoints_le_normalizerPoints` and
  `IsTitsSystem.inf_eq`.
- `h.eq_one_of_simpleRelativeRoots_eq_empty` and
  `h.eq_top_of_simpleRelativeRoots_eq_empty`: rank zero.

## Sources and provenance

- Borel and Tits, *Groupes réductifs* (1965), source `borel-tits-1965-groupes-reductifs`.
  - §5.3 (printed pp.95–97): `_kW = 𝒩(S)/𝒵(S)` is generated by the reflections `r_a`, and
    every component of `𝒩(S)` meets `G_k`, so `N_k/Z_k = _kW`. Its proof (printed p.97)
    shows `𝒩(S) ∩ P = 𝒵(S)` for the minimal parabolic `P`.
  - §5.8 (printed p.98): `_kΦ` is a root system.
  - §5.12 (printed p.99): standard parabolics, with `P = _kP_∅` minimal and `_kP_θ = G` for
    `θ = _kΔ`.
  - §5.15 (printed pp.100–101): `G_k = U_k N_k U_k`, and `G_k` is the disjoint union of
    the `P_k w P_k`.
  - §5.16 (printed p.101): `r.P_k.{w, r.w}.P_k = P_k.{w, r.w}.P_k` and `r.P_k.r ≠ P_k` for
    a fundamental reflection `r`.
  - §5.18 (printed p.101): "5.15 et 5.16 montrent que les axiomes de [33] sont vérifiés".
- Renard, *Représentations des groupes réductifs p-adiques*, French version dated
  9 July 2026, source `renard-2026-representations-groupes-reductifs-padiques`, V.4.1
  (printed p.118). It states that `(G, P_∅, N_G(A_∅), S_∅)` is a Tits system, with
  `W_G = N_G(A_∅)/Z_G(A_∅)` and `S_∅` the reflections in the simple roots. Renard works over
  a nonarchimedean local field; Borel–Tits gives the arbitrary-field scope.

The statement is a **derived** formulation of these source results. The source groups are
replaced by the published rational-point subgroups. The Weyl group is the published
quotient. The fundamental reflections are characterized by their action on the relative
root span, and their bijection with the simple roots is part of the target. The Tits axioms
are in the representative form of `Langlands.Group.TitsSystem`. Part 2 also uses that
`N(k)/Z(k)` acts faithfully on the root span. That holds because an element fixing every
root fixes a chamber, and `_kW` acts simply transitively on chambers (Borel–Tits §5.3,
§5.9).
