# Density over the classes of a block diagonal Levi subgroup

Lean module: `Langlands.Representation.Archimedean.RealLeviDensity`.

This module is part of the proof of `RealStandardLanglandsQuotientStatement` (module
`RealLargeLanglandsQuotientReduction`). It
states and proves `Langlands.Archimedean.RealLeviDensityStatement` (proof `realLeviDensity`). It
is the last of three modules (`RealLeviSlices`, `RealLeviProducts`, `RealLeviDensity`) for the
density step of the single-shot Langlands-quotient argument.

The statement concerns the standard module of a concatenation `ds = dss_0 ++ ⋯ ++ dss_{c-1}` of
lists of real blocks (in the application, the tie classes of a Langlands-ordered list). Assume
that each class standard module is irreducible. Then a proper `(𝔤𝔩_N, O(N))`-stable subspace `W`
of the global standard module has an annihilator `u` in the global dual principal series. On the
compact Levi subgroup `K_M = ∏_i O(sz_i)`, all jointly allowed iterated block Fourier
coefficients of `u` are those of an arbitrary prescribed product `⊗_i φ_i`. No literature
statement is claimed and nothing is cited; the provenance is internal ("derived"). Unprefixed
names below are in the namespace `Langlands.Archimedean.RealLeviDensity`.

## Notation

As in `RealLeviSlices.md` and `RealLeviProducts.md`. For `dss : Fin c → List RealBlock`:
`sz dss i = realRank (dss i)`, `N = ∑_i sz dss i`, `flat dss = dss 0 ++ ⋯ ++ dss (c-1)`,
`start_i = sz_0 + ⋯ + sz_{i-1}`, and `cl dss i = twist (shift dss i) (dss i)` is the class list
with all exponents increased by `s_i = start_i - (N - sz_i)/2`. `blockDiagGL (sz dss) κ` is
`diag(κ_0, …, κ_{c-1})`.

From earlier modules:

* `RealInducedStandardBound`: `slots ds N` is the list, in increasing order of `p`, of the slots
  of the induction blocks of `ds`. There is one slot at every position `p` where an induction
  block `d` starts (`realInducedBlockAt ds p = some d`, `p + 1 < N`), with weight `M = |d.weight|`
  and mode `0`.
* `RealInducedTorusCore`: `withModes L J` replaces the modes of the slots of `L` by the entries of
  `J` (up to the shorter length; `setMode s j`).
* `RealInducedBlockBound`: `coeffs L F` is the iterated block Fourier coefficient along `L` (see
  `RealLeviProducts.md`). It depends only on the positions `p` and modes `j` of the slots
  (`coeffs_congr_map` of `RealInducedTorusReduction`).
* `RealLeviModes`: `IsNull S v` means that `coeffs (withModes S J) v k = 0` for every `k ∈ O(N)`
  and every `J` of length `|S|` that is **jointly allowed**, i.e. `M ≤ |j|` at every slot of
  `withModes S J`. `isNull_of_annihilates`: if `realRank ds = N`, every element of `nullSpace N ds`
  (the annihilator of the standard module in the dual space, `RealLeviDuality`) is null along
  `slots ds N`. `integral_mul_eq_zero_of_mem_standard`: a null `O(N)`-finite element of the dual
  principal series pairs to zero with the standard module.
* `RealLeviDuality`: `DualSpace`, `StdSpace`, the pairing `⟨v, x⟩ = ∫_{O(N)} v x d(haarK N)`,
  `annihilator`, `nullSpace`, the quotient `Zq` with `zRep`, `zLie`, and `hyp_z`: if
  `realRank ds = N` and the standard module is irreducible, `GKModuleDensity.Hyp (zRep N ds)
  (zLie N ds)`. `exists_annihilator_not_null`: a proper `O(N)`-stable `W` has an annihilator in
  the dual space that pairs nontrivially with the standard module.

## The statement

`RealLeviDensityStatement`: for every `c` and `dss : Fin c → List RealBlock`, assume that for
every `i` the `O(sz_i)`-finite standard module of `cl dss i` is irreducible
(`IsIrreducibleGKModule (realStandardRep (sz dss i) (cl dss i)) (realStandardLie (sz dss i)
(cl dss i))`). Let `φ_i` be functions on `GL_{sz_i}(ℝ)` in
`kFiniteFunctions (principalSeries ℝ sz_i (dualChar (realPositionCharacter (cl dss i))))
(unitaryCompact ℝ sz_i)`. Let `W` be a subspace of
`kFiniteFunctions (realStandardModule N (flat dss)) (unitaryCompact ℝ N)` that is stable under
`realStandardRep N (flat dss) k` for all `k ∈ O(N)` and under `realStandardLie N (flat dss) X` for
all `X ∈ ℂ ⊗ 𝔤𝔩_N(ℝ)`, with `W ≠ ⊤`. Then there is
`u ∈ kFiniteFunctions (principalSeries ℝ N (dualChar (realPositionCharacter (flat dss))))
(unitaryCompact ℝ N)` such that:

1. `∫_{O(N)} u(k) w(k) d(haarK N)(k) = 0` for every `w ∈ W`;
2. for every family `Js : Fin c → List ℤ` with `(Js i).length = |slots (cl dss i) sz_i|` and
   `M ≤ |j|` at every slot of `withModes (slots (cl dss i) sz_i) (Js i)` (for all `i`), and every
   `κ` with `κ_i ∈ O(sz_i)`:

   `coeffs (withModes (slots (flat dss) N) (Js 0 ++ ⋯ ++ Js (c-1))) u (diag κ)
     = ∏_i coeffs (withModes (slots (cl dss i) sz_i) (Js i)) φ_i (κ_i)`.

The concatenated mode list is `(List.ofFn Js).flatten`. The slots of `flat dss` are, class by
class, the slots of the `cl dss i` moved to the global positions `start_i + p` with the same
weights (`map_key_flat` below). So the left side uses on the global slots the modes that the
right side uses on the class slots.

## Proof outline

1. `exists_annihilator_not_null` gives `u_0` annihilating `W` and pairing nontrivially with the
   standard module. By `integral_mul_eq_zero_of_mem_standard`, `u_0` is not null along
   `slots (flat dss) N`: some jointly allowed `J` and `k ∈ O(N)` have
   `coeffs (withModes (slots (flat dss) N) J) u_0 k ≠ 0`. Split `J` into class lists `Js`
   (`exists_split`). These are jointly allowed for every class (`allowed_of_map_key3`).
2. `u_1 = R(k) u_0` still annihilates `W`. Its coefficient at `1` along the lifted class slots
   with modes `Js` is nonzero.
3. `exists_isProdForm` (`RealLeviProducts`) writes `u_1` on `K_M` as `∑_a C_a ∏_j w_{a,j}(κ_j)`
   with `w_{a,j}` in the class dual spaces.
4. For each class `j`, `μ_j(v) = coeffs (withModes (slots (cl dss j) sz_j) (Js j)) v 1` vanishes on
   `nullSpace` of `cl dss j` (`isNull_of_annihilates`), so it descends to the quotient `Z_j`.
   Jacobson density in `Z_j` (Library `GKModuleDensity.exists_freeAlgebra_eq` with `hyp_z`)
   applied to the endomorphism `[v] ↦ μ_j(v)[φ_j]` and the finite set `{[w_{a,j}]}` gives
   `b_j` with `b_j · w_{a,j} - μ_j(w_{a,j}) φ_j ∈ nullSpace` for all `a`.
5. `u* = applyAll b (finRange c) u_1` annihilates `W` (the annihilator of `W` is stable under the
   generators) and has the product form with factors `b_j · w_{a,j}` (`isProdForm_applyAll`).
6. For every jointly allowed `Js'` and `κ ∈ K_M`, `coeffs_globalSlots` computes the coefficients of
   `u*` factor by factor. Each factor `b_j · w_{a,j}` agrees with `μ_j(w_{a,j}) φ_j` modulo
   `nullSpace`, whose jointly allowed coefficients vanish on `O(sz_j)`. Hence the coefficient is
   `C · ∏_j coeffs_{Js'_j} φ_j (κ_j)` with `C = ∑_a C_a ∏_j μ_j(w_{a,j})`. At `Js' = Js`, `κ = 1`
   the coefficient of `u_1` is `C` by `coeffs_globalSlots`, and it is nonzero by step 2. Then
   `u = C⁻¹ u*`.

## Results by section

**Modes along concatenated slot lists** (section `Modes`).

* `key s = (s.p, s.M)` and `key3 s = (s.p, s.M, s.j)`.
* `withModes_append`: `withModes (A ++ B) (J ++ J') = withModes A J ++ withModes B J'` when
  `|J| = |A|`.
* `map_key3_withModes`: slot lists with the same `key`s have the same `key3`s after setting the
  same modes.
* `allowed_of_map_key3`: joint allowedness transfers between lists with the same `key3`s.
* `coeffs_congr_key3`: lists with the same `key3`s have the same iterated coefficients
  (`coeffs_congr_map`).

**Lifted slot lists** (section `Lift`).

* `withModes_map_liftSlot`, `withModes_globalSlots`: setting modes commutes with lifting slots and
  with `globalSlots` (the mode list being the concatenation of the class mode lists).
* `length_globalSlots`, `liftSlot_mem_globalSlots`.
* `exists_split`: a list of length `∑_i ls_i` is `(List.ofFn Js).flatten` for lists `Js i` of
  lengths `ls_i` (induction on `c` with `take`/`drop`).

**Keys of a concatenated list** (section `Keys`).

* `map_key_slots`: `(slots ds N).map key` lists `(p, |d.weight|)` for the induction blocks `d` at
  the positions `p < N` (when `realRank ds ≤ N`; the Library `realInducedBlockAt_lt` gives `p + 1 < N`).
* `range_sum`: `List.range (∑_i sz_i)` is the concatenation of the shifted ranges
  `start_i + [0, sz_i)`.
* `map_key_flat`: `(slots (flat dss) N).map key =
  (globalSlots (fun i => slots (cl dss i) sz_i) (finRange c)).map key`, by `range_sum`,
  `realInducedBlockAt_flat` and `realInducedBlockAt_twist` (twisting preserves weights).
* `length_slots_flat`, and `map_key3_flat`: with modes `Js` the two lists have the same `key3`s.

**Coefficients of the dual space** (section `Coeffs`).

* `coeffs_add`: additivity of `coeffs` for continuous functions.
* `muC ds L`: the linear functional `v ↦ coeffs L v 1` on `DualSpace N ds` (`muC_apply`).
* `coeffs_eq_zero_of_mem_nullSpace`: if `realRank ds = N`, jointly allowed coefficients of
  elements of `nullSpace N ds` vanish on `O(N)` (`RealLeviModes.isNull_of_annihilates`).
* `coeffs_eq_mul_of_sub_mem`: if `v - r φ ∈ nullSpace`, the jointly allowed coefficients of `v` on
  `O(N)` are `r` times those of `φ`.

**Annihilators** (section `Ann`).

* `annW W`: the annihilator in `DualSpace N ds` of a subspace `W` of `StdSpace N ds`; `mem_annW`.
* `annW_rep`, `annW_lie`: if `W` is stable under `realStandardRep` (resp. `realStandardLie`),
  `annW W` is stable under `principalSeriesRep` (resp. `principalSeriesLie`) of the dual
  character. This uses the pairing identities `integral_rightTranslation_mul` and
  `integral_rightDerivative_mul` of `RealLeviDuality`. The signed-power property of the position
  characters comes from the Library `RealStrictCharacterLanglandsQuotient.isSignedPower`.

**Density in one class** (section `Class`).

* `exists_class_density`: if `realRank ds = N`, the standard module is irreducible, and `J` is
  jointly allowed for `slots ds N`, then for finitely many `w_a ∈ DualSpace N ds` and any `φ` there
  is a free algebra element `b` (generators `O(N) ⊕ ℂ ⊗ 𝔤𝔩_N(ℝ)`, acting through
  `GKModuleDensity.gens` of `principalSeriesRep`, `principalSeriesLie`) with
  `b · w_a - μ(w_a) φ ∈ nullSpace N ds`, where `μ = muC ds (withModes (slots ds N) J)`. Proof: step 4
  of the outline. The free algebra action commutes with the quotient map (`lift_intertwine`).

**Density over all classes** (section `Main`).

* `gensG_mem_annW`: `annW W` is stable under the class generators `gensG dss i x`.
* `coeffs_globalSlots_of_sub_mem`: if `u` has product form with factors `v_{a,j}` and
  `v_{a,j} - r_{a,j} φ_j ∈ nullSpace`, then for jointly allowed `Js` and `κ ∈ K_M` the coefficient
  of `u` along the lifted class slots at `diag κ` is
  `(∑_a C_a ∏_j r_{a,j}) · ∏_j coeffs_{Js_j} φ_j (κ_j)`.
* `exists_density`: the statement with `u ∈ annW W` (steps 1–6 of the outline).

`realLeviDensity` applies `exists_density` and unfolds `annW`.
