# Renard V.3.21–V.3.22: the sets `M^+`, `M^{++}`, `A^+_M`, `A^{++}_M` and `A^+(ε)`

This unit defines, on the actual group schemes, the sets that Renard introduces in V.3.21
and V.3.22. Every declaration is a definition or a proved theorem. The file contains no
statement left for a separate proof task.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version of
9 July 2026 (source id `renard-2026-representations-groupes-reductifs-padiques`):

- V.3.21, printed p. 116 / PDF p. 122. For a parabolic subgroup `P = MN`, `M^+` (resp.
  `M^{++}`) is the inverse image under `H_M` (V.2.3) of the closure of `^G_P[𝔞]^+` (resp.
  of `^G_P[𝔞]^+` itself), intersected with `X_*(M)`. For a subset `H` of `M`,
  `H^+ = H ∩ M^+` and `H^{++} = H ∩ M^{++}`. The source then says that it "follows directly
  from the definitions" that
  `A^+_M = {a ∈ A_M | v_F(α(a)) ≥ 0, α ∈ Δ(P)} = {a ∈ A_M | |α(a)|_F ≤ 1, α ∈ Δ(P)}`,
  and the same with strict inequalities for `A^{++}_M`.
- V.3.22, printed p. 117 / PDF p. 123, (V.3.22.1): for `ε > 0`,
  `A^+(ε) = {a ∈ A_M | |α(a)|_F < ε, α ∈ Δ(P)}`, and `Ω^+(ε) = Ω ∩ A^+(ε)` for `Ω ⊂ A`.
- V.3.15, printed p. 113 / PDF p. 119, for the chambers. `^G_P[𝔞]^+` and its closure are
  obtained from `^G_P[𝔞^*]^+` by exchanging roots and coroots. They are the `x ∈ 𝔞_M` with
  `⟨β, x⟩ > 0` (resp. `≥ 0`) for every `β ∈ Δ(P)`.
- V.3.23, printed p. 117 / PDF p. 123, uses these sets for the lattice cuts
  `C_A^+ = C_A ∩ M^+` and `C_A^+(ε) = C_A ∩ A^+(ε)`.

## Setting

The objects used are already in the Library.

- `F` is a nonarchimedean local field (`IsNonarchimedeanLocalField F`).
- `Δ(P)` is the published `restrictedSimpleRoots i ν J f`, a set of real characters of `A`.
  Its integral form is `restrictedSimpleCharacters i ν J f`, a set of integral characters
  of `A` (see [RestrictedSimpleRootCones](../../GroupScheme/Rational/RestrictedSimpleRootCones.md)).
  Here `i : T → G` is the maximal split torus `A_∅` of a minimal parabolic, `ν` is the
  cocharacter that selects its positive roots, `J` is the set `Δ_∅^M` of simple roots of
  `M`, and `f : A → A_∅` is the inclusion of the split component `A = A_M`.
- `𝔞_M` is the real cocharacter space `V(A)` of the split component.
- `H_M` is the published positive centralizer valuation `centralizerValuation s h` on the
  actual points of a group scheme `Z`, with values in `V(A)`. Here `s : A → Z` and `h` is the
  bijectivity of `restrictionEvaluation s`, the identification of `V(A)` with
  `Hom(X^*(Z), ℝ)` (see [CentralizerValuation](CentralizerValuation.md)). It satisfies
  `⟨χ|_A, H_M(z)⟩ = v_F(χ(z))` for every rational character `χ` of `Z`. This is the positive
  convention of V.2.3, matching the display `v_F(α(a)) ≥ 0` of V.3.21.
- `|α(a)|_F` is the published normalized norm `CocharacterUniformizer.characterNorm F A α a`.

To read `leviPlus` and `leviStrict` as Renard's `M^+` and `M^{++}`, `Z` must be the Levi
subgroup `M`, `A` its split component, `s` the inclusion, and `(i, ν, J, f)` the
minimal-parabolic data of `P`. Like the published `dominantCentralizer`, the definitions do
not impose these conditions. They make sense for any such data.

## Definitions

Namespace `Langlands.BruhatTits.Cartan.RenardLeviCones`.

- `chamber i ν J f : Set (V A)`: `^G_P[𝔞]^+`, the `x` with `0 < pair A β x` for every
  `β ∈ restrictedSimpleRoots i ν J f`.
- `closedChamber i ν J f`: the same condition with `0 ≤`. This is the source's closure of
  `^G_P[𝔞]^+`; see the qualifications below.
- `characterOrder A α a : ℤ`: the integer valuation `v_F(α(a))` of an integral character `α`
  of `A` at `a ∈ A(F)`. It is the coordinate of the published `rationalCharacterValuation`
  (the source's `H_G` of V.2.3 for `G = A`).
- `componentPlus F i ν J f`, `componentStrict F i ν J f`: `A^+_M` and `A^{++}_M`, the points
  `a ∈ A(F)` with `characterNorm F A α a ≤ 1` (resp. `< 1`) for every `α` in
  `restrictedSimpleCharacters i ν J f`. These are the norm forms displayed in V.3.21.
- `componentEpsilon F i ν J f ε`: `A^+(ε)` of (V.3.22.1), with `characterNorm F A α a < ε`.
- `leviPlus i ν J f s h`, `leviStrict i ν J f s h`: `M^+` and `M^{++}`, the points `m` of
  `Z(F)` with `(centralizerValuation s h m).toAdd` in `closedChamber` (resp. `chamber`).

## Theorems

All are proved in the file.

- Chambers: `chamber_subset_closedChamber`, `mem_closedChamber_iff_eval` and
  `mem_chamber_iff_eval` (the same conditions through the integral characters),
  `zero_mem_closedChamber`, `add_mem_closedChamber`, and `add_mem_chamber` (closed plus open
  lies in the open chamber).
- Norms and valuations: `ord_rationalCharacterEval` (`characterOrder` is the published order
  `FML.ord F` of `α(a)`), and `characterNorm_eq_rpow`: `|α(a)|_F = q^{-v_F(α(a))}`, with `q`
  the residue cardinality. It follows that `characterNorm_le_one_iff` gives
  `|α(a)|_F ≤ 1 ↔ v_F(α(a)) ≥ 0` and `characterNorm_lt_one_iff` gives
  `|α(a)|_F < 1 ↔ v_F(α(a)) > 0`. The file also proves `characterOrder_mul` and
  `characterOrder_one`.
- The valuation forms of V.3.21: `mem_componentPlus_iff_order` gives
  `A^+_M = {a | v_F(α(a)) ≥ 0, α ∈ Δ(P)}` and `mem_componentStrict_iff_order` gives
  `A^{++}_M = {a | v_F(α(a)) > 0, α ∈ Δ(P)}`.
- Inclusions in `A`: `componentStrict_subset_componentPlus`; `componentEpsilon_one`
  (`A^+(1) = A^{++}_M`); `componentEpsilon_mono`; `componentEpsilon_subset_componentStrict`
  for `ε ≤ 1`; and `componentEpsilon_eq_empty` for `ε ≤ 0` and nonempty `Δ(P)`.
- Monoid properties: `one_mem_componentPlus`, `mul_mem_componentPlus`,
  `mul_mem_componentStrict` (`A^+_M · A^{++}_M ⊂ A^{++}_M`), and the same for the Levi:
  `one_mem_leviPlus`, `mul_mem_leviPlus`, `mul_mem_leviStrict`, `leviStrict_subset_leviPlus`.
  Also `rationalCommonNormKernel_subset_leviPlus` (`⁰M ⊂ M^+`).
- **The source's definition of `A^+_M` agrees with the norm form.** If `A` is a split torus,
  then `map_mem_leviPlus_iff` gives `s(a) ∈ M^+ ↔ a ∈ A^+_M`, and `map_mem_leviStrict_iff`
  gives `s(a) ∈ M^{++} ↔ a ∈ A^{++}_M`. The preimage forms are `preimage_leviPlus` and
  `preimage_leviStrict`. Their common input is `eval_centralizerValuation_map`:
  `⟨α, H_M(s(a))⟩ = v_F(α(a))` for every integral character `α` of `A`, including characters
  that are not restrictions of characters of `Z`. Its proof uses the published
  `torusValuationRestriction_eq_id` and `restrictionEvaluation_id_bijective`.
- Lattice cuts of V.3.23: `CAplus_eq_inter`, `CAstrict_eq_inter` and `CAepsilon_eq_inter`
  identify the published `CocharacterUniformizer.CAplus`, `CAstrict` and `CAepsilon` for
  `R = restrictedSimpleCharacters i ν J f` with `C_A ∩ A^+_M`, `C_A ∩ A^{++}_M` and
  `C_A ∩ A^+(ε)` (by `rfl`). For split `A`, `CAplus_eq_preimage_leviPlus` and
  `CAstrict_eq_preimage_leviStrict` give the source's forms `C_A^+ = C_A ∩ M^+` and
  `C_A^{++} = C_A ∩ M^{++}`.
- Minimal parabolic: `restrictedSimpleCharacters_minimal` (for `J = ∅` and `f = 𝟙`, `Δ(P)`
  is the set of simple roots), and `leviPlus_minimal`: `M_∅^+` equals the published
  `dominantCentralizer i ν s h`. That set is defined with all positive roots. The proof uses
  the published `isDominantVector_of_simple`, which says that nonnegativity on simple roots
  implies nonnegativity on positive roots.

The monoid lemmas, `⁰M ⊂ M^+`, the `characterOrder` lemmas and the minimal-parabolic
comparison are not stated in the source. They are elementary consequences recorded for later
use.

## Source issue I1: (V.3.21.1) is not formalized

After V.3.21 the book writes `A^+_M = ⊔_Q A^{++}_L`, over the standard parabolic subgroups
`Q = LU ⊇ P`. As an equality of subsets of `A_M` this is false. In `GL_2` with `P = B`, `M`
the diagonal torus and a unit `u ∈ 𝔒_F^×` with `u ≠ 1`, the element `diag(1, u)` has
`|α(diag(1, u))|_F = 1`. It therefore lies in `A^+_M` but not in `A^{++}_M`. It is not
central, so it is not in `A_G` either. The decomposition holds on the valuation side (the
chambers in `𝔞_M`, V.3.16), modulo `⁰A_M`, and for the lattice parts `C_A`. This issue is
recorded as I1 in the Chapter V item ledger (`notes/renard/item-ledger-v.md`). This unit
does not state (V.3.21.1) in any form.

## Dependence on `P`

As the source remarks, the notations `A^+_M` and `A^{++}_M` do not show the parabolic `P`,
but the sets depend on it. Here the dependence is explicit: every set takes the data
`(i, ν, J, f)` that determine `Δ(P)`.

## Choices and qualifications

- **Closure.** `closedChamber` is defined by the nonstrict inequalities, as is the
  Library's `restrictedClosedCorootChamber` on the `𝔞^*` side. It equals the topological
  closure of `chamber` when `chamber` is nonempty (for example when `Δ(P)` is linearly
  independent). That equality is not stated here, and `V(A)` carries no topology in this
  file.
- **`∩ X_*(M)`.** The source intersects the chambers with the lattice `X_*(M)` before taking
  the inverse image. `H_M` already takes values in its image lattice, so this intersection
  does not change the inverse image and is omitted.
- **Which definition of `A^+_M` is primary.** In the source, `A^+_M = A_M ∩ M^+`, and the norm
  and valuation forms are consequences. Here `componentPlus` is defined by the norm form,
  which does not depend on `Z`, `s` or `h`. `map_mem_leviPlus_iff` proves agreement with the
  source's definition, assuming `A` is a split torus as `A_M` is. The same holds for
  `A^{++}_M`. `A^+(ε)` is defined by norms in the source as well.
- **`ε`.** The source takes `ε > 0`. `componentEpsilon` accepts any real `ε`. For `ε ≤ 0`
  and nonempty `Δ(P)` it is empty (`componentEpsilon_eq_empty`).
- **Notation `H^+`, `Ω^+(ε)`.** The intersections `H ∩ M^+`, `H ∩ M^{++}` and `Ω ∩ A^+(ε)`
  are ordinary set intersections and receive no separate names.
- **`A_M` as a subset of `M`.** The source's `A_M ∩ M^+` is read through the point map of
  `s` as the preimage `rationalPoints.map s ⁻¹' leviPlus …` in `A(F)`.
