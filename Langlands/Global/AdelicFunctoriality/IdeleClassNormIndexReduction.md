# Reduction of the idele-class norm index lemma to the finiteness of `C_K / C∞`

This module, in namespace `Langlands.Global.AdelicFunctoriality`, proves the
idele-class norm index lemma
[`IdeleClassNormIndexFinite`](IdeleClassNormIndexFiniteStatement.md)
under one hypothesis: the quotient of the idele class group by the integral
idele classes is finite,
[`IntegralIdeleClassQuotientFinite`](../../ClassField/Global/IntegralIdeleClassQuotientFiniteStatement.md).
Throughout, `K : Type u` and `L : Type v` are number fields in independent
universes with `Algebra K L`. The module imports
[IdeleNormLift](IdeleNormLift.md),
[UnramifiedUnitNorm](UnramifiedUnitNorm.md),
[LocalDegree](LocalDegree.md),
[LocalUnitPowers](../../ClassField/Global/LocalUnitPowers.md) and the two
statement modules above. It changes none of the imported definitions and
declares no global instances.

## Main theorem

- `ideleClassNormIndexFinite_of_integralIdeleClassQuotientFinite`
  `(h : IntegralIdeleClassQuotientFinite.{u}) : IdeleClassNormIndexFinite.{u, v}`.
  Suppose `C_E / C∞` is finite for every number field `E : Type u`. Then for
  every `L : Type v` over `K : Type u`, the range `H` of
  `(ideleClassNorm (K := K) (L := L)).toMonoidHom` has finite index, and that
  index divides `(Module.finrank K L) ^ r` for some natural number `r`.

The proof uses `h` only for the base field `K`. A proof of
`IntegralIdeleClassQuotientFinite.{u}` therefore gives
`IdeleClassNormIndexFinite.{u, v}` in one line.

## Chosen places and local degrees

The proof fixes one place of `L` above each place of `K`.

- `infinitePlace_liesOver_of_comap_eq h`: an infinite place `w` of `L` with
  `w.comap (algebraMap K L) = v` lies over `v`.
- `infinitePlaceAbove L v : InfinitePlacesAbove L v`: a chosen infinite place
  of `L` above `v`. It exists by Mathlib's `InfinitePlace.comap_surjective`.
  The finite analogue `placeAbove L p` is imported from
  [LocalDegree](LocalDegree.md).

The remaining definitions take arbitrary choice functions
`wf : ∀ p, FinitePlacesAbove L p` and `wi : ∀ v, InfinitePlacesAbove L v`.

- `chosenFiniteDegree wf p` is the local degree
  `Module.finrank (p.adicCompletion K) ((wf p).1.adicCompletion L)`.
  `chosenFiniteDegree_ne_zero` says it is nonzero, by the finiteness
  `FiniteExtension.local_finite`.
- `chosenInfiniteDegree wi v` is the local degree
  `Module.finrank v.Completion (wi v).1.Completion`.
  `chosenInfiniteDegree_eq` says it is `1`, or it is `2` and `v` is real.
  This follows from Mathlib's unramified/ramified dichotomy for infinite
  places.
- `infiniteUnitPowers_chosenInfiniteDegree_finiteIndex`: the subgroup
  `infiniteUnitPowers v (chosenInfiniteDegree wi v)` of `(v.Completion)ˣ` has
  finite index. For degree one it is the whole group (`infiniteUnitPowers_one`).
  For degree two `v` is real, and the squares have finite index
  (`infiniteUnitPowers_two_finiteIndex`).
- `ramifiedChosenPlaces wf` is the set of finite places `p` of `K` with
  `(wf p).1.asIdeal.ramificationIdx (𝓞 K) ≠ 1`.
  `finite_ramifiedChosenPlaces` says this set is finite, by
  `eventually_ramificationIdx_eq_one` from
  [UnramifiedUnitNorm](UnramifiedUnitNorm.md).

## Local power residues

- `integralUnitCoordinate K p : integralIdeles K →* localUnits p` is the
  coordinate at the finite place `p` of an integral idele, as a valuation
  unit. `coe_integralUnitCoordinate` computes its underlying element.
- `integralInfiniteCoordinate K v : integralIdeles K →* (v.Completion)ˣ` is
  the coordinate at the infinite place `v`.
  `coe_integralInfiniteCoordinate` computes its underlying element.
- `LocalPowerResidues wf wi` (an abbreviation) is the product group
  `(∀ p : ramifiedChosenPlaces wf, localUnits p ⧸ localUnitPowers p (chosenFiniteDegree wf p)) ×
  (∀ v, (v.Completion)ˣ ⧸ infiniteUnitPowers v (chosenInfiniteDegree wi v))`.
  Here `localUnitPowers p d` is the subgroup of `d`-th powers in `localUnits p`
  (see [LocalUnitPowers](../../ClassField/Global/LocalUnitPowers.md)).
- `localPowerResidue wf wi : integralIdeles K →* LocalPowerResidues wf wi`
  reduces each coordinate of an integral idele modulo local-degree powers:
  the unit coordinates at the finitely many places in `ramifiedChosenPlaces wf`,
  and the coordinates at all infinite places.
- `localPowerResidue_ker_finiteIndex`: the kernel of `localPowerResidue wf wi`
  has finite index in `integralIdeles K`. The codomain is finite. It is a
  finite product of quotients that are finite by `localUnitPowers_finiteIndex`
  (degree nonzero) and by
  `infiniteUnitPowers_chosenInfiniteDegree_finiteIndex`. Then Mathlib's
  `Subgroup.finiteIndex_ker` applies.

## Residue-free integral ideles are norms

- `mem_range_ideleNorm_of_localPowerResidue_eq_one wf wi x hx`: if an
  integral idele `x` has trivial local power residues, then it lies in the
  range of the idele norm `ideleNorm : J_L → J_K`. The proof applies the
  lifting criterion `mem_range_ideleNorm_of_local` from
  [IdeleNormLift](IdeleNormLift.md). It needs one local preimage at each
  chosen place, with unit preimages at almost all finite places.
  - At a finite `p` in `ramifiedChosenPlaces wf`, the coordinate is `y ^ d`
    for a local unit `y`, where `d` is the local degree. Its preimage is the
    image of `y` in `L_q`. Here `FiniteExtension.localNorm_algebraMap` says
    that the local norm of an element of `K_p` is its `d`-th power.
  - At any other finite `p`, the chosen place is unramified over `p`. The unit
    coordinate is the local norm of a valuation unit, by
    `FiniteExtension.exists_localNorm_eq_of_ramificationIdx_eq_one` from
    [UnramifiedUnitNorm](UnramifiedUnitNorm.md).
  - At an infinite `v`, the coordinate is a local-degree power `y ^ d`. Its
    preimage is the image of `y`, by `InfiniteExtension.localNorm_algebraMap`.

  Outside the finite set `ramifiedChosenPlaces wf` the chosen preimages are
  valuation units, so they and their inverses are integral.
- `residueFreeIdeleClasses wf wi : Subgroup (IdeleClassGroup (𝓞 K) K)` is the
  image in `C_K` of the kernel of `localPowerResidue wf wi`.
- `residueFreeIdeleClasses_le_range`: this subgroup lies in the range of the
  idele-class norm. It follows from the previous theorem and
  `ideleClassNorm_mk`.

## Index arguments

- `residueFreeIdeleClasses_finiteIndex wf wi hK`: if
  `Finite (IntegralIdeleClassQuotient K)`, then `residueFreeIdeleClasses wf wi`
  has finite index in `C_K`. Write `P = integralIdeleClasses K` and
  `π : integralIdeles K → P` for the surjective restriction of the quotient
  map. The image under `π` of the finite-index kernel has finite index in `P`
  (Mathlib's `Subgroup.index_map_dvd`). It is contained in the residue-free
  classes, so their relative index in `P` is finite. The index of `P` in `C_K`
  is finite by hypothesis. Then `Subgroup.relIndex_mul_index` multiplies the
  two.
- `ideleClassNorm_range_finiteIndex hK`: under the same hypothesis, the range
  of the idele-class norm has finite index. It contains
  `residueFreeIdeleClasses (placeAbove L) (infinitePlaceAbove L)`.
- `ideleClassNorm_range_index_dvd hH`: if the norm range `H` has finite
  index, then `H.index ∣ (Module.finrank K L) ^ r` for some `r`. The
  quotient `C_K ⧸ H` is a finite commutative group. Here its normality and
  commutative-group instances are supplied locally, since instance search does
  not find the generic ones. Every class `c` satisfies `c ^ [L : K] ∈ H`, by
  the norm-of-inclusion law `ideleClassNormInclusionPower` from
  [IdeleNormLift](IdeleNormLift.md). Mathlib's
  `card_dvd_exponent_pow_rank'` then shows that the order of the quotient
  divides `[L : K] ^ (Group.rank (C_K ⧸ H))`.

## Source and route

The statement is the first lemma of Emil Artin and John Tate, *Class Field
Theory*, AMS Chelsea edition (2009), Chapter VI §1, printed p.20 (PDF p.29).
Registered original: `artin-tate-2009-class-field-theory`. The second half of
the proof here follows the source exactly: the index divides a power of the
degree because every `m`-th power in `C_k` is a norm.

The finiteness half takes a different route from the source. Artin–Tate pass
to a normal overextension and compare `J_k^S` with its norm group. Here the
extension `L/K` is arbitrary and need not be normal; one chosen place of `L`
above each place of `K` suffices. A lower-field coordinate that is a
local-degree power is a local norm, and at unramified chosen places every unit
coordinate is a local norm. The integral ideles with trivial residues at the
finitely many remaining places therefore consist of norms and have finite
index in `J∞`. The finiteness of `C_K / C∞` is the class-group input that
replaces Artin–Tate's choice of `S` with `J_k = k^* J_k^S`. This module takes
it as the hypothesis `IntegralIdeleClassQuotientFinite`; its proof is
separate.
