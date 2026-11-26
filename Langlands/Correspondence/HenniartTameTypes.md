# Frobenius-fixed inertia types and the conductor counts

For a p-adic field `F` and a Weil element `φ` of geometric degree one, this
module rewrites Henniart's conductor count `C_F(k + 1, j)`
(`Numerical.weilConductorCount F k j`) as a count of inertia types fixed by
conjugation by `φ`. Here a type is an isomorphism class of continuous
irreducible finite-dimensional complex representations of inertia
`I_F = localInertia F`, in the sense of `Clifford.TypeClasses`
(module `Langlands.Representation.Clifford.Classes`).

## Definitions

- `frobConj F φ` is conjugation `g ↦ φ g φ⁻¹` on inertia, as a continuous
  automorphism. `typePullback_frobConj`: pulling a type back along it is the
  Frobenius conjugation `(weilSplit F φ hφ).conjType 1` of the published split
  degree data (module `Langlands.Correspondence.HenniartUnramified.Concrete`);
  the two type quotients are the same.
- `typeRank F x` is the dimension of a representative and `typeBreak F x` its
  break, the published `inertiaBreak` (the infimum of the indices `v ≥ 0` whose
  upper group acts trivially); both are well defined on classes because
  dimension and break are invariant under equivalence (`inertiaBreak_equiv`),
  and `typeRank_mk`, `typeBreak_mk` compute them on representatives.
- `fixedStratum F φ d s` is the set of `φ`-fixed type classes of rank `d` with
  `d · break = s`.

## Results

- `exists_nat_of_fixed` and `exists_nat_of_fixed_class`: for a `φ`-fixed type
  `B`, `dim B · break B` is a natural number, and some upper group of
  nonnegative index acts trivially on `B`. A fixed type has minimal period one
  under Frobenius conjugation, so it extends to the Weil group by the published
  stage construction `typeCoind` for `weilStage F φ hφ 0`. The extension is
  continuous and irreducible of rank `dim B`, its last break is the break of `B`
  (`lastBreak_typeCoind`), and the published Swan label of its class
  (`weilSwanLabel`, `hasWeilSwan_weilClassOf`) equals rank times last break.
  Its triviality thresholds are nonempty
  (`HerbrandBridge.weilTrivialityThresholdsNonempty`), and
  `typeCoind_trivial_iff` passes the threshold to `B`.
- `weilTwistIrreducibleCount_eq`: for `d > 0`,
  `weilTwistIrreducibleCount F (d - 1) s`, Henniart's `T_F(d, s)`, equals the
  number of elements of `fixedStratum F φ d s`. This is the case of period one
  (`m = 0`) of the published `encard_period_goodTypes`
  (module `Langlands.Correspondence.HenniartUnramified.Strata`): minimal period
  one means being fixed.
- `encard_biUnion_finset`: the extended cardinality of a finite union of
  pairwise disjoint sets is the sum of the cardinalities.
- `weilConductorCount_eq`: in `ℕ∞`,
  `C_F(k + 1, j) = #{x : x is φ-fixed, rank x ∣ k + 1, (k + 1) · break x ≤ j}`.
  The defining double sum runs over divisors `d` of `k + 1` and
  `s ≤ ⌊d j / (k + 1)⌋`; the strata are pairwise disjoint, and a fixed type of
  rank `d` belongs to the stratum `s = d · break`, which is a natural number by
  `exists_nat_of_fixed_class`. The bound `s ≤ ⌊d j / (k + 1)⌋` is equivalent to
  `(k + 1) · break ≤ j`.

The module is internal: it supplies the inertia-type side of the orbit formula
`WeilTameOrbitFormulaStatement` (module
`Langlands.Correspondence.HenniartTameOrbitFormula`), whose remaining steps are
in `Langlands.Correspondence.HenniartTameOrbitCount`.
