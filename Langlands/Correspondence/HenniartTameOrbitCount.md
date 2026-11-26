# Wild inertia orbits and the orbit formula

This module derives the orbit formula `WeilTameOrbitFormulaStatement`
(module `Langlands.Correspondence.HenniartTameOrbitFormula`) from the Frobenius
parametrization of tame fields, `TameWeilFrobeniusParametrizationStatement`
(module `Langlands.Correspondence.HenniartTameWeilFields`), as
`weilTameOrbitFormula_of_parametrization`. The parametrization is used only
through `exists_index_of_parametrization`: it supplies, for every `d` prime to
`p`, an open subgroup of inertia `I_K` containing wild inertia `P` of index `d`.

The count corresponds to H. Koch, *Bemerkungen zur numerischen lokalen
Langlands-Vermutung* (1984), registered as
`koch-1984-numerical-langlands-remarks`, §8, Lemmas 7 and 8 (PDF p. 6), where
representations with a fixed restriction to the first ramification group are
counted through characters of the tame quotient. Here inertia types are
counted through the inertia orbits of the irreducible representations of wild
inertia under them, with `q - 1` Frobenius-fixed types over each
Frobenius-stable orbit.

## Transport between the Weil group and inertia

`WildClasses K` are classes of representations of `weilWildInertia K` inside
the Weil group; the Clifford theory of `Langlands.Representation.Clifford` works
with `wildIn K`, the same group inside inertia (module
`Langlands.Correspondence.HenniartWildInertia`).

- `objMap e` and `classMap e` pull open-kernel irreducible objects and classes
  back along a continuous group isomorphism `e`; `classMap_mk`,
  `classMap_symm_classMap`, `classMap_classMap_symm` and `rank_classMap` show
  that pulling back is a rank-preserving bijection.
- `toW K = classMap (wildEquiv K).symm` and `ofW K = classMap (wildEquiv K)` are
  inverse (`toW_ofW`, `ofW_toW`, `toW_injective`).
- `toW_smul`: conjugation by `g ∈ I_K` commutes with `toW`.
  `toW_wildPullback`: pulling back along conjugation by `φ`
  (`TameTypes.frobConj K φ`) corresponds to the action of `φ⁻¹`.
  `wildClassTrivialAt_toW` reads `wildClassTrivialAt K v` on inertia, and
  `rank_toW` preserves ranks.

## Upper groups, breaks and the inertia subgroup `J`

- `upperGroup_le_weilWildInertia`: for `v > 0` the upper group of the Weil group
  lies in wild inertia, because the absolute upper group of index `v` lies in
  the closure of the union of the positive ones.
- `wildIn_le_of_isClosed`: a closed subgroup of inertia containing all upper
  groups of positive index contains wild inertia. Through `localInertiaEquiv`
  its image is closed in the absolute Galois group and contains the union of
  the positive absolute upper groups, hence its closure.
- `inertiaBreak_le_iff`: if some upper group of nonnegative index acts
  trivially, then for `b ≥ 0` the break is at most `b` exactly when every
  upper group of index greater than `b` acts trivially (the upper groups
  decrease, `upperGroup_antitone`).
- `wildIn_le_of_coprime`: an open normal subgroup `U` of inertia of index prime
  to `p` contains wild inertia: for `n ∈ P` both `n^(p^b)` (by the pro-`p`
  property `pPowerOpen_wildIn`) and `n^[I:U]` lie in `U`, and the two exponents
  are coprime.
- `exists_index_of_parametrization`: the kernel of a datum
  `TameWeilFrobeniusData K d φ` meets inertia in an open normal subgroup of
  index `d` (from `cosetEquiv`), which contains wild inertia.

## The trivial class and the rank-one count

- `Representation.isIrreducible_of_complex_finrank_eq_one`, `finrank_ulift`: one-dimensional
  representations are irreducible. `trivObj K` is the trivial representation of
  wild inertia on `ULift ℂ`; its class is fixed by all of inertia
  (`stabilizer_trivObj`), and `wildClass_eq_triv` identifies every irreducible
  representation on which wild inertia acts trivially with it (such a
  representation factors through the trivial group, hence has dimension one).
- `frobConj_mem_iff`: conjugation by a Weil element preserves wild inertia.
  `upperIn K v` is the upper group of index `v` inside inertia, and
  `upperIn_le_wildIn` holds for `v > 0`.
- `over_trivObj_iff`: a type with a triviality threshold lies over the trivial
  class exactly when it has rank one and break at most zero. One direction uses
  `finrank_of_over` and `trivial_iff_of_over`; for the other, the kernel of the
  type is closed and contains every upper group of positive index, so it
  contains wild inertia (`wildIn_le_of_isClosed`), and every class under the
  type is trivial.
- `encard_tameCharacters_fixed`: for `φ` of degree one, and given open
  subgroups of inertia containing wild inertia of every index prime to `p`, the
  characters of inertia trivial on wild inertia with open kernel and fixed by
  conjugation by `φ` are `q_K - 1` in number. By the fiber count `encard_fixed_liesOver`
  (module `Langlands.Representation.Clifford.Fiber`) at the trivial class they
  correspond to the fixed types of rank one and break at most zero, and by
  `TameTypes.weilConductorCount_eq` these are counted by `C_K(1, 0) = T_K(1, 0)`,
  which is `q_K - 1` by the published `weilRankOneCount`. The proof works with
  carriers in `Type`, as the statement does not involve carriers.

## The orbit formula

Fix `φ` of degree one, an open normal subgroup `J` of the Weil group inside
inertia of index `m` in inertia with `p ∤ m`, and `r, j`.

- `dvd_mul_iff_of_coprime`: for `u, m` prime to `p`,
  `u · p^a ∣ p^r · m ↔ u ∣ m ∧ p^a ∣ p^r`.
- `jFixed_iff`: a class is fixed by `J` exactly when the index of its stabilizer
  in inertia divides `[I_K : J]` (`le_iff_index_dvd`, as `J ∩ I_K` contains wild
  inertia).
- `break_iff`: for a type over a class `A` on which some upper group of
  nonnegative index acts trivially, the break is at most `b ≥ 0` exactly
  when the transported class is trivial at every index greater than `b`
  (`trivial_iff_of_over` on the normal subgroups `upperIn K v ≤ P`).
- `good_iff`: for a `φ`-fixed type over `A`, the conditions "rank divides
  `p^r m`" and "`p^r m · break ≤ j`" hold exactly when the transported class of
  `A` lies in `tameOrbitClasses K J r m j`. The rank of the type is
  `[I_K : Stab A] · p^a` with the index prime to `p`.
- `orbit_stable`: the inertia orbit of the classes under a `φ`-fixed type is
  stable under `φ`; `orbit_eq`: the classes under one type form one orbit
  (`exists_smul_eq_of_over`).
- `fiber_iff`: for a tame class `c'`, the counted types whose classes lie in
  the orbit of `c'` are exactly the `φ`-fixed types lying over `ofW K c'`.
- `orbitFormula`: in `ℕ∞`,
  `C_K(p^r m, j) = (q_K - 1) · #(frobeniusStableTameOrbits K J r m j φ)`,
  given open subgroups of every index prime to `p` containing wild inertia.
  By `TameTypes.weilConductorCount_eq` the left side counts `φ`-fixed types of
  rank dividing `p^r m` with `p^r m · break ≤ j`. The relation "some class under
  the type has the given orbit" is functional; its fibers over the stable
  orbits are the sets of `fiber_iff`, each of size `q_K - 1` by
  `encard_fixed_liesOver` and `encard_tameCharacters_fixed`. The published
  `encard_eq_mul_of_fibers` (module
  `Langlands.Correspondence.HenniartUnramified.Arith`) concludes.
- `weilTameOrbitFormula_of_parametrization`:
  `TameWeilFrobeniusParametrizationStatement.{uK}` implies
  `WeilTameOrbitFormulaStatement.{uK, uW}`.
