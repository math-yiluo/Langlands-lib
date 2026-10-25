# Local unit norms at unramified finite places

This module, in namespace `Langlands.Global.AdelicFunctoriality`, proves that
at a finite place of `L` that is unramified over the place of `K` below it,
every valuation unit of the completion of `K` is the local norm of a
valuation unit of the completion of `L`. It also proves that only finitely
many finite places of `K` have a ramified place above them. Throughout,
`K : Type u` and `L : Type v` are number fields in independent universes with
`Algebra K L`, `p` is a finite place of `K`, and `q` is a finite place of `L`
with `q.asIdeal.LiesOver p.asIdeal`. The module imports
[UnitNormProof](../../ClassFieldTheory/Local/UnitNormProof.md),
[UnitFiltrationStructuralProof](../../ClassFieldTheory/Local/UnitFiltrationStructuralProof.md),
[CompletionPadic](../CompletionPadic.md) and
[CompletedRamification](CompletedRamification.md). It changes none of the
imported definitions and declares no global instances.

## Equal valuations from equal orders

For a field `R` and a finite extension `F` of `ℚ_p` with local-field data `T`:

- `valuation_eq_of_isEquiv_of_surjective h h₁ h₂`: two equivalent valuations
  of `R` with values in `ℤᵐ⁰`, both surjective, are equal. Both send a common
  element to `exp (-1)`, so they agree on all its integer powers. Every value
  is such a power, and equivalence transfers the equation `v₁ x = v₁ πᵏ` to
  `v₂`.
- `valuativeRel_valuation_isEquiv T v hv`: suppose the valuative relation of
  `T` is the order of a valuation `v`. Then the canonical valuation of that
  relation is equivalent to `v`.
- `discreteValuation_eq_of_vle T v hv hs`: under the same hypothesis, if `v`
  is surjective onto `ℤᵐ⁰`, the normalized discrete valuation
  `T.discreteValuation` equals `v`. Both are surjective onto `ℤᵐ⁰`
  (`T.discreteValuation_surjective`), and they are equivalent through
  Mathlib's order isomorphism `valueGroupWithZeroIsoInt`.
- `mem_unitSubgroup_iff_of_vle T v hv x`: under the same hypothesis, a unit
  `x` lies in `T.unitSubgroup` if and only if `v x = 1`.

## `L_q` as a finite extension of `ℚ_p`

Let `padicField p` and `topologicalData p` be the published realization of
`K_p = p.adicCompletion K` as a finite extension of `ℚ_p`, where `p` is the
residue characteristic `residuePrime p`, from [CompletionPadic](../CompletionPadic.md).
In namespace `FiniteExtension`, this module builds the corresponding
realization of `L_q = q.adicCompletion L` through `K_p`:

- `towerPadicMap p q`: the ring embedding `ℚ_p → K_p → L_q`, the composite of
  `padicMap p` and `completionMap p q`. `continuous_towerPadicMap` says it is
  continuous.
- `towerPadicAlgebra p q` (a definition, not an instance): the resulting
  `ℚ_p`-algebra structure on `L_q`. `towerPadicFinite p q` says `L_q` is
  finite-dimensional over `ℚ_p`, by the finiteness of `K_p` over `ℚ_p` and
  of `L_q` over `K_p` (`local_finite`).
- `towerPadicField p q : PadicField (residuePrime p)`: `L_q` with this algebra
  structure.
- `tower_isModuleTopology p q` and `tower_topology_eq p q`: the completion
  topology of `L_q` is the `ℚ_p`-module topology. Hence it equals the topology
  of `(towerPadicField p q).canonicalTopologicalData`.
- `tower_valued_lt_one_iff p q x` and `tower_valued_isEquiv p q`: the
  completion valuation `Valued.v` of `L_q` is less than one exactly where the
  canonical norm of the realization is less than one, so the two valuations
  are equivalent.
- `towerTopologicalData p q`: the local-field data of `towerPadicField p q`
  whose topology is the completion topology. Its valuative relation is the
  canonical one. `towerTopologicalData_vle p q x y` says this relation is the
  order of `Valued.v`.

These constructions copy, for `L_q` over `ℚ_p` through `K_p`, the constructions
`padicMap`, `padicAlgebra`, `padicField` and `topologicalData` that
[CompletionPadic](../CompletionPadic.md) makes for `K_p` over `ℚ_p`.

## The unramified unit norm theorem

- `topologicalData_discreteValuation p` and
  `towerTopologicalData_discreteValuation p q`: the normalized discrete
  valuations of `topologicalData p` and `towerTopologicalData p q` are the
  completion valuations `Valued.v` of `K_p` and `L_q`. Proof:
  `discreteValuation_eq_of_vle` with `topologicalData_vle`, resp.
  `towerTopologicalData_vle`, and Mathlib's surjectivity
  `valuedAdicCompletion_surjective`.
- `ramificationIndex_eq_of_ramificationIdx_eq_one p q he`: if
  `q.asIdeal.ramificationIdx (𝓞 K) = 1`, then the absolute ramification
  indices over `ℚ_p` agree:
  `(topologicalData p).ramificationIndex = (towerTopologicalData p q).ramificationIndex`.
  Each index is the order of the prime `p`. By the previous item that order
  is computed from `Valued.v`, and `valuation_completionMap` gives
  `Valued.v (completionMap p q x) = Valued.v x ^ e` with `e = 1`.
- `exists_localNorm_eq_of_ramificationIdx_eq_one p q he u hu`: if
  `q.asIdeal.ramificationIdx (𝓞 K) = 1` and `u` is a unit of `K_p` with
  `Valued.v u = 1`, then there is a unit `c` of `L_q` with `Valued.v c = 1`
  and `FiniteExtension.localNorm p q c = u`. The proof applies the published
  local theorem `Langlands.LocalClassField.unramifiedUnitNorms` at unit level
  `0` to `F = padicField p`, `E = towerPadicField p q`, `T = topologicalData p`
  and `S = towerTopologicalData p q`. The required instances are the
  `K_p`-algebra structure of `L_q` used by `FiniteExtension.localNorm`, its
  finiteness `local_finite p q`, and the scalar tower `ℚ_p → K_p → L_q`, which
  holds by definition of `towerPadicAlgebra`. These are introduced locally
  inside the proof. `unitFiltration_zero` identifies level `0` with
  `unitSubgroup`, and `mem_unitSubgroup_iff_of_vle` identifies `unitSubgroup`
  with the units of `Valued.v`-value one. `normUnits` of the local theorem is
  the determinant norm `Algebra.norm`, which is `FiniteExtension.localNorm`.

## Finitely many ramified places

- `finite_setOf_ramificationIdx_ne_one K L`: the finite places `q` of `L`
  with `q.asIdeal.ramificationIdx (𝓞 K) ≠ 1` form a finite set. A ramified
  place divides the different ideal of `𝓞 L` over `𝓞 K`
  (`not_dvd_differentIdeal_iff`), and this ideal is nonzero
  (`differentIdeal_ne_bot`), so it has finitely many prime factors. The
  Library already has `Langlands.ClassField.Global.finite_setOf_ramificationIdx_ne_one`
  with the same proof, but only for two fields in one universe. This
  module needs independent universes `u` and `v`.
- `eventually_ramificationIdx_eq_one K L`: for all but finitely many finite
  places `p` of `K`, every finite place `q` of `L` with
  `q.asIdeal.LiesOver p.asIdeal` has ramification index one. The exceptional
  set is contained in the image of the previous finite set under
  `q ↦ q.under (𝓞 K)`.

## Sources and provenance

Jean-Pierre Serre, *Local Fields*, GTM 67 (1979), Chapter V, Section 2,
Proposition 3 and its Corollary, printed pp.81–82 (PDF pp.88–89), registered
source `serre-1979-local-fields`. Proposition 3 b) and the Corollary with the
remark that condition (3) holds for finite residue fields give `U_K = N U_L`
for an unramified extension `L/K` of local fields. The closing exercise
extends this to unramified extensions that are not Galois. Worker 269 read
these pages in the retained original. The local statement is published as
`UnramifiedUnitNorms` and proved as `unramifiedUnitNorms`. This module only
transports that theorem to Mathlib's completions `K_p` and `L_q`.

Emil Artin and John Tate, *Class Field Theory*, AMS Chelsea edition (2009),
registered source `artin-tate-2009-class-field-theory`. The first lemma of
Chapter VI §1 (printed p.20, PDF p.29) bounds `(J^S_k : N J^S_K)` "by an
argument similar to that used in the first inequality (V, 3)". That argument
(printed pp.12–13, PDF pp.21–22) uses that the local unit groups have trivial
norm-residue groups at the unramified places (`e_p = 1` at almost all `p`).
`exists_localNorm_eq_of_ramificationIdx_eq_one` and
`eventually_ramificationIdx_eq_one` are the Lean forms of these two facts for
the Library's completions. The generic valuation lemmas and the tower
realization `towerPadicField` are internal infrastructure; the cited sources
do not state them.
