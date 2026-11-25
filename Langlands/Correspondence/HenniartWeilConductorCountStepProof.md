# Henniart's conductor-count step: proof

`Langlands.Henniart.weilConductorCountStep` proves `Langlands.Henniart.WeilConductorCountStepStatement.{uK, uW}` from `Langlands.Correspondence.HenniartWeilElementaryLayer`. The field universe `uK` and the representation-carrier universe `uW` are independent, and no hypothesis is added. For every prime `p`, p-adic field `K`, natural `r` and integer `l ≥ 1`, the extended-natural count `C_K(p^r, p^r l)` is `q_K` times `C_K(p^r, p^r l − 1)`, where `q_K` is the residue cardinality. This is Henniart's Corollaire 1.4 (Guy Henniart, *La conjecture de Langlands locale numérique pour GL(n)*, Ann. Sci. École Norm. Sup. (4) 21 (1988), p. 499, proved in §3.4, p. 509; registered source `henniart-1988-numerical`), stated as Corollary `cor:14` of the 16 November 2026 numerical LLC route note.

## Assembly

The final theorem takes a normalized common-closure reciprocity family from `commonClosureReciprocityExistence`. Its base component is a geometric local Weil reciprocity candidate (`geometric_baseReciprocityCandidate` with `commonClosureGeometricProof`). The checked reduction `weilConductorCountStep_of_scalarGradeDescent` (module `HenniartWeilTwistStep`) gives the equality from one input, `WeilScalarGradeDescent` at level `l`. That input is proved here as `Numerical.weilScalarGradeDescent`. The reduction itself builds, for each divisor rank `d = p^i` of `p^r`, an explicit bijection between the product of the dual of `U_K^l/U_K^(l+1)` with the torsion-one orbits of Swan exponent `< d l`, and those of Swan exponent `≤ d l`. Each character is represented by a chosen continuous Weil lift through upper-numbering reciprocity. The counting reduction in `HenniartWeilConductorCountStepReduction` then sums the extended cardinalities. No finiteness of the strata is assumed.

## Scalar descent (`weilScalarGradeDescent`)

Fix a continuous irreducible Weil representation `A` that acts by a scalar character on the upper group at the positive integer `l` and trivially on every upper group at a real index above `l`.

1. `exists_weilScalarField` supplies an actual finite Galois intermediate field `E` and a continuous character of the fixing Weil subgroup `W_E` by which `A` acts as scalars. The upper group at `l` lies in `W_E`.
2. Put `m = ⌈ψ_{E/K}(l)⌉`, which is positive. `exists_next_ceiling_levels` gives `b > l` with `⌈b⌉ = l + 1` and `⌈ψ_{E/K}(b)⌉ = m + 1`. The two norm image identities of `normToBaseUnits_map_unitFiltration` at `l` and `b` then give a surjective norm map on grades, from `U_E^m/U_E^(m+1)` to `U_K^l/U_K^(l+1)`.
3. Through the intermediate reciprocity component, the scalar character becomes a character of `E^×`. It is trivial on `U_E^(m+1)`: its image there comes from the carried upper group at `ψ_{E/K}(b)`, i.e. from the upper group of `K` at `b`, where `A` is trivial. Hence it induces a character of the source grade.
4. A Weil element is chosen whose restriction to `E` induces arithmetic Frobenius on the residue field of `E` (`exists_weil_residue_frobenius_lift`). Conjugation by it preserves the scalar character, because conjugating a scalar operator gives the same scalar. Through reciprocity this makes the induced field character invariant (`reciprocityUnits_conjugateWeil`). The norm is invariant under it as well, by the norm square into the abelian base units (`normToBaseUnits_weilRestriction`).
5. On the source grade the lift's fixed points number at most `q_K` (`card_unitGradeMap_fixed_le`), and the target grade has exactly `q_K` elements. Thus `exists_hom_factor_of_fixed_card_le` factors the invariant grade character through the surjective norm, giving a character `η` of the base grade.
6. For `w` in the upper group at `l`, its reciprocity image in `E` lies in `U_E^m`, and its norm is the base reciprocity image of `w` (norm square). Evaluating the factorization there shows `A(w) = η(rec_K(w)) · 1`, which is `WeilScalarGradeDescent`.

The proof uses `set_option maxHeartbeats 800000` for this declaration only.

## Relation to the literature

The route note's direct proof of `prop:H33`, its version of Henniart's Proposition 3.3 (pp. 508–509), makes the same reduction to the graded norm and its coinvariants (`numerical-LLC-route.tex`, lines 702–715). It gets the coinvariants by a separate trace computation on the unramified part and a step-by-step analysis on the totally ramified part (Serre, *Local Fields*, V §§2, 6). This proof replaces both by the fixed-point count of one Frobenius lift on the source grade. It also obtains norm surjectivity from the relative upper-group theorem and the reciprocity norm square, instead of a computation of `ψ_{E/K}`.

## Supporting modules

The proof imports, directly or through one another, the following supporting modules: `HenniartWeilConductorCountStepReduction`, `HenniartWeilSwanBreak`, `CyclicRestriction`, `HenniartWeilTorsionInertia`, `WildInertiaStructure`, `HenniartWeilUpperScalar`, `HenniartGradedWeilCharacters`, `HenniartWeilTwistStep`, `HenniartWeilScalarField`, `UpperGradeNorm`, `GradeCoinvariants` and `GradeReciprocity`.
