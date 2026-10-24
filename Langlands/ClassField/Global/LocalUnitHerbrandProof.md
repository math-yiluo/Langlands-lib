# The Herbrand quotient of the valuation units of a completion

Author: Worker 226.

This module proves the three statements of
`Langlands.ClassField.Global.LocalUnitHerbrandStatement` unconditionally:

- `cyclicCompletionUnitHerbrand : CyclicCompletionUnitHerbrand.{u}`;
- `unramifiedCompletionUnitVanishing : UnramifiedCompletionUnitVanishing.{u}`;
- `completionUnitHerbrandFromCohomologyExistence :
  CompletionUnitHerbrandFromCohomologyExistence.{u}`. Both conclusions are proved without
  any hypothesis, so the bridge implication ignores its premise.

It also exports `LocalUnitHerbrand.hasHerbrandQuotient_localUnits`. When `E/F` is Galois and
`Gal(E_w/F_v)` is cyclic, this gives
`HasHerbrandQuotient (localUnitsRepresentation v w) 1` in the sense of
`Langlands.Cohomology.HerbrandQuotient`.

Throughout, `F E : Type u` are number fields with `[Algebra F E]`, `v` and `w` are finite
places with `[w.asIdeal.LiesOver v.asIdeal]`, `K = v.adicCompletion F`,
`L = w.adicCompletion E` with the Library's local algebra, and
`G = L ≃ₐ[K] L = Gal(E_w/F_v)`. The norm on `L` is Mathlib's normed-field structure
`instNormedFieldValuedAdicCompletion` coming from the valuation. Instance search supplies
`IsUltrametricDist L` and `CompleteSpace L` for it.

## Local preliminaries

- `valued_localAut`, `norm_localAut`: local automorphisms preserve the valuation and the
  norm of `E_w`. Use the Library's `unitsExponent_localAut` and `valued_units`, then
  `Valued.toNormedField.norm_le_iff`.
- `exists_ϖ`: the image in `E_w` of a uniformizer of `F_v` has norm in `(0, 1)`. Its
  valuation is `exp(-1) ^ e` with `e = w.asIdeal.ramificationIdx (𝓞 F) > 0`, by the Library's
  `valuation_completionMap`.

## The open subgroup `V`

With `[FiniteDimensional K L]` and `D : LatticeData K L` from
`Langlands.ClassField.Global.LocalUnitLattice`:

- `unitFiltration_le_localUnits`: `D.unitFiltration 0` consists of valuation units.
- `openUnits v w D = (D.unitFiltration 0).subgroupOf (localUnits w)` is the subgroup `V` of
  `U_w`. It is `G`-stable (`smul_mem_openUnits`), carries the restricted action
  `openUnitsAction`, and gives the representation
  `openUnitsRepresentation v w D = coefficientRepresentation G (openUnits v w D)`. The
  inclusion `openUnitsInclusion v w D : openUnitsRepresentation v w D ⟶
  localUnitsRepresentation v w` is injective (`openUnitsInclusion_injective`).
- `subsingleton_H1_openUnits`, `subsingleton_H2_openUnits` (under `[CompleteSpace L]`):
  `H¹(G, V)` and `H²(G, V)` are trivial. Every class is `H1π` (resp. `H2π`) of a cocycle `x`.
  Its values, viewed in `Lˣ`, form a multiplicative cocycle with values in
  `D.unitFiltration 0`. `exists_coboundary1_eq_of_mem` (resp. `exists_coboundary2_eq_of_mem`)
  writes it as a coboundary of a cochain with values in `D.unitFiltration 0 ⊆ U_w`. So `x`
  lies in `coboundaries₁` (resp. `coboundaries₂`) and `H1π_eq_zero_iff`
  (resp. `H2π_eq_zero_iff`) applies.

## Finite index

- `exists_integer_approx`: every `x ∈ L` with `‖x‖ ≤ 1` lies within `‖ϖ‖ ^ n` of an
  algebraic integer of `E`. First approximate by `y ∈ E` (Mathlib's
  `denseRange_algebraMap`). Then `‖y‖ ≤ 1`, and Mathlib's
  `exists_valuation_sub_lt_of_integer` gives an integer close to `y`.
- `smallIdeal v w D n` is the ideal of `𝓞 E` of elements of norm `< ‖ϖ‖ ^ n` in `E_w`. It is
  nonzero (`smallIdeal_ne_bot`), since it contains a power of a nonzero element of `w`, so
  `𝓞 E ⧸ smallIdeal` is finite (`Ring.HasFiniteQuotients`).
- `finite_quotient_openUnits`: `U_w ⧸ V` is finite. Take `N = c + (c + 1)` and send a coset
  to the class of an integer approximation of its representative modulo `smallIdeal N`.
  This is injective: if the approximations of `u₁, u₂` agree modulo the ideal, then
  `‖u₂ - u₁‖ < ‖ϖ‖ ^ N`, so `‖u₁⁻¹ u₂ - 1‖ < ‖ϖ‖ ^ N` and `u₁⁻¹ u₂ ∈ V` by
  `mem_unitFiltration_zero_of_norm_le`.
- `finite_coker`: hence the cokernel of `openUnitsInclusion` (the quotient of
  `localUnitsRepresentation v w` by the range) is finite.

## Main results

- `hasHerbrandQuotient_localUnits`: with `[IsGalois F E]` and cyclic `G`, the Library
  instances give `FiniteDimensional K L` (`FiniteExtension.local_finite`) and
  `IsGalois K L` (`isGalois_adicCompletion`). `exists_ϖ` and `exists_latticeData` give
  `D`. `V` has Herbrand quotient `1` because both cohomology groups are trivial. Worker 269's
  `hasHerbrandQuotient_iff_of_injective` (finite cokernel) transfers this to `U_w`.
- `cyclicCompletionUnitHerbrand` unpacks the last result.
- `subsingleton_H1_localUnits_of_unramified`: if `e = 1`, the Library's
  `exists_fixed_uniformizer` gives a `G`-fixed unit `π` of exponent `-1`. A cocycle `f` with
  values in `U_w` is `g ↦ g • β / β` for some `β ∈ Lˣ` by Hilbert 90 (Mathlib's
  `isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`). Then `β π ^ k`, with `k` the exponent
  of `β`, is a valuation unit with the same coboundary. So `H¹(G, U_w) = 0`.
- `unramifiedCompletionUnitVanishing`: for `e = 1` the local group is cyclic (Library
  `isCyclic_localGal`). `H¹ = 0` has order `1`, so `H²` has order `1` by
  `cyclicCompletionUnitHerbrand`, and is therefore a subsingleton.

## Provenance

The theorem `h(U_L) = 1` for a cyclic extension of local fields is J. S. Milne,
*Class Field Theory* v4.03 (2020), source `milne-2020-class-field-theory`, Chapter III,
Lemma 2.5, printed p.104 (PDF p.113). Milne proves it from Lemma 2.4 (an open subgroup with
trivial cohomology) and the invariance of the Herbrand quotient under finite index. This
module follows that route, with Lemma 2.4 supplied by `LocalUnitLattice` through a
filtration argument. The unramified vanishing is the case `e_p = 1` of E. Artin and J. Tate,
*Class Field Theory* (2009), source `artin-tate-2009-class-field-theory`, Chapter V §2,
printed p.12 (PDF p.21). The argument for `H¹` given here (Hilbert 90 and a fixed
uniformizer), and the passage from `H¹ = 0` to `H² = 0` through `h(U_w) = 1`, are internal.
The finite-index argument through integer approximation is also internal.
