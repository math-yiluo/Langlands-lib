# Vanishing of the cohomology of a class formation in degrees ≥ 3

`Langlands/Cohomology/Profinite/ClassFormation/HighDegree.lean`, namespace
`Langlands.ProfiniteCohomology`.

For a class formation `C` over a profinite group `G` (coefficients over `ULift ℤ`),
`Hʳ(U, C) = 0` for every open subgroup `U` and every `r ≥ 3`; in particular `Hʳ(G, C) = 0`.
A class of `Hʳ(U, C)` is inflated from a finite quotient `U/W`; by Tate's theorem for the
fundamental class of `U/W` it is `u ∪ y` with `y` killed by some `m ≠ 0`; writing
`inv(u) = m · inv(β)` with `ℚ/ℤ` divisible, the class becomes `β ∪ (m • y) = 0`.

## Declarations

- `subsingleton_cohomology_of_top`: vanishing of `Hʳ(⊤, A)` (the subgroup `⊤` of `G`) implies
  vanishing of `Hʳ(G, A)`.
- `exists_openSubgroup_subgroupOf_eq`: an open subgroup of an open subgroup `U` is the trace on
  `U` of an open subgroup of `G` contained in `U`.
- `ClassFormation.exists_cupH_quot`: for `N` open normal in `U` and `n ≥ 1`, every class of
  `H^{n+2}(U/N, C^N)` is the cup product of a class of degree `2` with a torsion class of
  `Hⁿ(U/N, ℤ)` (Tate's theorem `GroupCoh.exists_cupH_of_tate` applied to the fundamental class,
  with `ClassFormation.tate_hypotheses`).
- `trivialToInvariantsHom N`: the identification of the trivial module of `H ⧸ N` with the
  `N`-invariants of the trivial module of `H`; `rightUnitor_quotientToInvariants`: compatibility
  of right unitors with passage to invariants.
- `ClassFormation.subsingleton_cohomology_of_three_le F U hr`: `Hʳ(U, C) = 0` for every open
  subgroup `U` and `r ≥ 3`.
- `ClassFormation.subsingleton_cohomology_top_of_three_le F hr`: `Hʳ(G, C) = 0` for `r ≥ 3`.

## Source and licence

Ported from `src/GroundTheory/ProfiniteCohomology/ClassFormations/SubsingletonCohomologyTopOfThreeLeInt.lean`
of the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, with
`exists_openSubgroup_subgroupOf_eq` from
`src/GroundTheory/ProfiniteCohomology/LocalClassFormation/FiniteVanishing/FormationThree.lean`.
The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

The source proves the statements over `ℤ` for groups in universe `0`
(`subsingleton_cohomology_of_three_le_int`, `subsingleton_cohomology_top_of_three_le_int`) and
deduces those over `ULift ℤ` through its bridge between `ℤ` and `ULift ℤ`
(`ClassFormation.toInt`, `cohomologyULiftIntAddEquiv`, in its local class formation files).
Since the Library's Tate theorem is over `ULift ℤ`, the proof here is made directly over
`ULift.{u} ℤ`, for groups in any universe `u`, and its two theorems carry the source's names of
the `ULift` versions (`ClassFormation.subsingleton_cohomology_of_three_le`,
`ClassFormation.subsingleton_cohomology_top_of_three_le`). The versions over `ℤ` are not stated
here; they follow through the source's bridge, which belongs to the local theory.

## References

- E. Artin, J. Tate, *Class Field Theory* (AMS Chelsea 2009, reprint with corrections of the 1967
  edition), chapter XIV, §4, Theorem 1 (Main Theorem), p. 154 (cup product with the fundamental
  class of a layer `K/F` gives `H^q(G_{K/F}, ℤ) ≅ H^{q+2}(K/F)`), and Theorem 4 with its Corollary,
  pp. 156–157 (inflation from `K/F` to `L/F` is zero in dimensions `r > 2` when `[K : F]` divides
  `[L : K]`).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter III, §1, Theorem (3.1.4), p. 150, and Definition (3.1.8),
  p. 156.

The vanishing of `Hʳ(U, C)` for `r ≥ 3` itself is not stated in these sections; Artin and Tate state
the vanishing of inflation in dimensions `r > 2` on the finite layers.
