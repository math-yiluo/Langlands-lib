# The dual quotient of a real standard module

Lean module: `Langlands.Representation.Archimedean.RealLeviDuality`.

Worker 5220 wrote this module for Task 6749 (`5dd3db87-6f14-4d0f-b9a7-3d0065415fd8`), the proof
of `RealStandardLanglandsQuotientStatement` (module `RealLargeLanglandsQuotientReduction`). It
states and proves `Langlands.Archimedean.RealLeviDualityStatement` (proof `realLeviDuality`).

This is internal infrastructure for the density step of the single-shot Langlands-quotient
argument. The module forms the quotient `Z` of the dual principal series by the annihilator of
a standard module. It shows that `Z` satisfies the hypotheses of the Library density theorem
when the standard module is irreducible. It also produces relative annihilators of proper
`O(N)`-stable subspaces. The method is the usual duality between a principal series and the
principal series of the inverse characters under the `O(N)`-integral pairing. No literature
statement is claimed and nothing is cited; the provenance is internal ("derived"). Unprefixed
names below are in the namespace `Langlands.Archimedean.RealLeviDuality`.

## Notation

`GL_N(ℝ)` is `Langlands.GeneralLinear N ℝ` and `O(N)` is the Library's `unitaryCompact ℝ N`, with
Haar probability measure `haarK N` (Library `RealPrincipalSeriesDuality`). For a list of real
blocks `ds`:

* `χ = realPositionCharacter ds` are its position characters, and `dualChar χ = χ⁻¹`
  (`PartialJacquet`).
* `X = StdSpace N ds` is `kFiniteFunctions (realStandardModule N ds) (unitaryCompact ℝ N)`: the
  right `O(N)`-finite functions of the standard module. Its `(𝔤𝔩_N(ℝ), O(N))`-module structure
  is the Library's `realStandardRep N ds` (right translation) and `realStandardLie N ds` (right
  derivatives).
* `Y^∨ = DualSpace N ds` is
  `kFiniteFunctions (principalSeries ℝ N (dualChar χ)) (unitaryCompact ℝ N)`, with the Library's
  `principalSeriesRep` and `principalSeriesLie`.
* The pairing of `v ∈ Y^∨` and `x ∈ X` is `⟨v, x⟩ = ∫_{O(N)} v(k) x(k) d(haarK N)(k)`.

From the earlier module `RealLeviModes` of this task this module uses `exists_ext_conj`,
`mem_kFin_standard_of_annihilates`, `integral_mul_eq_zero_of_mem_standard`,
`eq_zero_of_integral_norm_sq_eq_zero` and `integrable_of_continuous`. In the module these are
combined into a double annihilator theorem.

## The statement

`RealLeviDualityStatement`: for every `N` and every list of real blocks `ds` with
`realRank ds = N`:

1. if `X` is an irreducible `(𝔤𝔩_N(ℝ), O(N))`-module (`IsIrreducibleGKModule (realStandardRep N ds)
   (realStandardLie N ds)`), then `GKModuleDensity.Hyp (zRep N ds) (zLie N ds)` holds;
2. for every subspace `W` of `X` that is stable under `realStandardRep N ds` (right translation
   by `O(N)`) and is not all of `X`, there is `u ∈ Y^∨` with `⟨u, w⟩ = 0` for every `w ∈ W` and
   `⟨u, x⟩ ≠ 0` for some `x ∈ X`.

Here `nullSpace N ds = {v ∈ Y^∨ | ⟨v, x⟩ = 0 for all x ∈ X}` and `Z = Zq N ds` is the quotient
`Y^∨ / nullSpace N ds`. `zRep N ds` is the quotient of `principalSeriesRep ℝ N (dualChar χ)`
(Mathlib `Representation.quotient`). `zLie N ds` is the induced action `quotLie` of
`principalSeriesLie ℝ N (dualChar χ)`. The Library structure `GKModuleDensity.Hyp ρ π`
(hypotheses of Schur's lemma and Jacobson density in `GKModuleDensity`) consists of: `(ρ, π)` is
irreducible; `ρ` is admissible (`IsAdmissibleGKModule`: for every continuous matrix
representation `τ` of `O(N)` the space of `O(N)`-intertwiners from `τ` to `ρ` is
finite-dimensional); every vector lies in a finite-dimensional `ρ`-stable subspace; and
`k ↦ ℓ(ρ(k) v)` is continuous for every vector `v` and every linear form `ℓ`.

Part 2 does not use the rank hypothesis or irreducibility.

## Proof outline

Right translation by `k ∈ O(N)` moves across the pairing as right translation by `k⁻¹`. A right
derivative moves across with a sign change, because the product `v x` is modulus-equivariant and
right derivatives of such products integrate to zero over `O(N)`. So `nullSpace` is a
`(𝔤, K)`-submodule and `Z` is a `(𝔤, K)`-module.

Irreducibility of `Z`: let `S' ⊋ nullSpace` be the preimage of a proper submodule. An
orthogonal vector of the Library (`principalSeriesOrthogonalVector`) gives `w₀ ∈ Y^∨`, nonzero
on `O(N)` and `L²(O(N))`-orthogonal to `S'`. Its conjugate on `O(N)` extends to `x₀` in the
`O(N)`-finite principal series of `χ`, and `x₀` annihilates `S'`. The double annihilator
theorem puts `x₀` in `X`. The annihilator of `S'` in `X` is a nonzero `(𝔤, K)`-submodule, hence
all of `X` by irreducibility of `X`, so `S' ⊆ nullSpace`.

Admissibility of `Z` follows from an abstract lifting lemma. Intertwiners from `τ` to a quotient
of a unitary representation with finite-dimensional orbit spans lift to intertwiners into the
representation. Apply it to the `L²(O(N))` inner product on `Y^∨`. The other two hypotheses pass
to quotients directly.

Part 2: let `X'`, `W'` be `X`, `W` inside the `O(N)`-finite principal series of `χ`. Since
`W ≠ X`, some `x₁ ∈ X` lies outside `W' + X'^⊥`. The Library gives a nonzero `v` orthogonal to
`W' + X'^⊥`. It is not orthogonal to `X'`. Then `u` is the extension of `conj v` from `O(N)` to
`Y^∨`.

## Results by section

**Quotients of `(𝔤, K)`-modules** (section `Quotient`, general `K`, `L`, `V`).

* `quotLie π W h`: for a Lie algebra map `π : L → End V` and a subspace `W` stable under every
  `π X`, the induced Lie algebra map `L → End (V ⧸ W)`; `quotLie_mk` computes it on classes.
* `quotient_finite`: if every vector of `V` is `ρ`-finite (`FiniteVectors.IsFiniteVector`), every
  vector of `V ⧸ W` lies in a finite-dimensional subspace stable under `ρ.quotient W h`: the image
  of the orbit span.
* `quotient_continuous`: if `k ↦ ℓ(ρ(k) v)` is continuous for all `v` and linear forms `ℓ` on
  `V`, the same holds on `V ⧸ W` (compose `ℓ` with the quotient map).

**Lifting `K`-intertwiners** (section `Lift`, `E` a complex inner product space, `ρ` a
representation of a group `G` on `E` preserving the inner product, all orbit spans
finite-dimensional, `W` a `ρ`-stable subspace).

* `exists_lift_of_mem_gkIntertwiners`: every `T ∈ gkIntertwiners (ρ.quotient W hW) d τ` has the
  form `mkQ ∘ S` with `S ∈ gkIntertwiners ρ d τ`. Proof: choose lifts `v_i` of the images
  `T(e_i)` of the standard basis vectors. Let `F` be the sum of their orbit spans
  (finite-dimensional and stable) and `P = F ⊓ W`. Replace `v_i` by `u_i = v_i − proj_P v_i`,
  and let `S` be the linear map with `S(e_i) = u_i`. For `g ∈ G` and `x`, the defect
  `S(τ(g) x) − ρ(g) S(x)` lies in `F`, in `W` (since `T` is an intertwiner) and in `P^⊥` (`P^⊥`
  is stable because `ρ` preserves the inner product, Library `isStable_orthogonal`). So it lies
  in `P ⊓ P^⊥ = 0`.
* `isAdmissible_quotient`: if `ρ` is admissible, so is `ρ.quotient W hW`: composition with the
  quotient map is a linear surjection
  `gkIntertwiners ρ d τ → gkIntertwiners (ρ.quotient W hW) d τ`.

**The pairing** (section `Pairing`, general signed-power characters `χ`).

* `toUnits_mk`: coercion bookkeeping between `O(N)` as a subgroup and as `unitaryGroup`.
* `integral_rightTranslation_mul`: `∫_{O(N)} (R(k) v) x = ∫_{O(N)} v (R(k⁻¹) x)` for
  `k ∈ O(N)` (right invariance of Haar measure).
* `integral_rightDerivative_mul`: for `v` in the principal series of `χ⁻¹`, `x` in that of `χ`
  and `X ∈ 𝔤𝔩_N(ℝ)`: `∫_{O(N)} (R(X) v) x = −∫_{O(N)} v (R(X) x)`. Library
  `integral_rightDerivative_eq_zero` (for the modulus-equivariant product `v x`) and the Leibniz
  rule `rightDerivative_mul_fun` give this.
* `exists_conj_mem_dual` / `exists_conj_mem_of_dual`: an `O(N)`-finite function of the principal
  series of `χ` (resp. `χ⁻¹`) has a conjugate on `O(N)` that extends to an `O(N)`-finite function
  of the principal series of `χ⁻¹` (resp. `χ`). These apply `RealLeviModes.exists_ext_conj`. The
  sign condition holds because `|χ_i(−1)| = 1`.
* `integral_conj_mul_self_ne_zero`: for continuous `x` with `x(k₀) ≠ 0` at some `k₀ ∈ O(N)`,
  `∫_{O(N)} conj(x) x ≠ 0`.

**The annihilator and the quotient** (section `Null`).

* `DualSpace N ds`, `StdSpace N ds`: the spaces `Y^∨`, `X` above, with continuity lemmas and
  `mem_kFin_of_mem_stdSpace` (elements of `X` are `O(N)`-finite elements of the principal series
  of `χ`).
* `annihilator N ds A hA`: the subspace of `Y^∨` pairing to zero with every element of a set `A`
  of continuous functions. `nullSpace N ds` is the annihilator of `X`; `mem_nullSpace` unfolds it.
* `nullSpace_le_comap_rep`, `nullSpace_le_comap_lie`: `nullSpace` is stable under right
  translation by `O(N)` and under `principalSeriesLie` (by the two pairing identities and the
  Library stability of `X`: `rightTranslation_mem_kFiniteFunctions_realStandardModule`,
  `rightDerivative_mem_kFiniteFunctions_realStandardModule`). `coe_principalSeriesLie_tmul`
  computes `principalSeriesLie` on pure tensors `z ⊗ X` as `z · R(X)`.
* `Zq N ds`, `zRep N ds`, `zLie N ds` as above, with `zRep_mk`, `zLie_mk`.

**The density hypotheses** (section `Hyp`).

* `integral_mul_congr_left/right`: the pairing only depends on values on `O(N)`.
  `integral_mul_rightTranslation`: `∫ v (R(k) x) = ∫ (R(k⁻¹) v) x`.
* `eq_zero_of_mem_stdSpace`: an element of `X` vanishing on `O(N)` is zero (Library
  `eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact`).
* `mem_stdSpace_of_annihilates` (**double annihilator**): if `realRank ds = N` and an
  `O(N)`-finite `x` in the principal series of `χ` pairs to zero with every `v ∈ nullSpace`, then
  `x ∈ X`. By `RealLeviModes`, every `O(N)`-finite null `v` (`IsNull`) lies in `nullSpace`
  (`integral_mul_eq_zero_of_mem_standard`), and `mem_kFin_standard_of_annihilates` concludes.
* `coe_realStandardLie_tmul`: `realStandardLie` on pure tensors.
* `stdAnnihilator N ds B`: the subspace of `X` pairing to zero with every element of a subspace
  `B` of `Y^∨`. `stdAnnihilator_stable_rep` / `stdAnnihilator_stable_lie`: if `B` is stable
  under `O(N)` (resp. `principalSeriesLie`), its annihilator is stable under `realStandardRep`
  (resp. `realStandardLie`).
* `exists_not_mem_nullSpace`: a nonzero `x ∈ X` gives some `v ∉ nullSpace`, namely the extension
  of `conj x` from `O(N)` (`⟨v, x⟩ = ∫ |x|² ≠ 0`).
* `isIrreducible_z`: if `realRank ds = N` and `X` is irreducible, `Z` is irreducible.
  Nontriviality comes from `exists_not_mem_nullSpace`. For a stable proper `S`, the argument of
  the outline applies to `S' = S.comap mkQ`. The orthogonal vector `w₀` is nonzero at some
  `k₁ ∈ O(N)`, so `x₀(k₁) = conj(w₀(k₁)) ≠ 0` and the annihilator of `S'` is not `⊥`.
* `admissible_z`: `Z` is admissible. The representation `rho` on the Library type
  `PrincipalSeriesAnnihilator.KFin N χ⁻¹` (the same space `Y^∨` with the `L²(O(N))` inner
  product) preserves the inner product (`rho_isometry`) and has finite-dimensional orbit spans
  (`finiteDimensional_orbit`). The Library `isAdmissibleGKModule_kFiniteRep` gives admissibility
  of `principalSeriesRep`, and `isAdmissible_quotient` transfers it to `Z`.
* `hyp_z`: `GKModuleDensity.Hyp (zRep N ds) (zLie N ds)` from `isIrreducible_z`, `admissible_z`,
  `quotient_finite` (with the Library `kFiniteRep_isFiniteVector`) and `quotient_continuous`
  (with the Library `kFiniteRep_continuous`).

**Relative annihilators** (section `Relative`).

* `exists_annihilator_not_null`: part 2 of the statement. In `KFin N χ` let `X'` and `W'` be the
  preimages of `X` and `W`, and `W₁ = W' ⊔ X'^⊥`. All three are `rho`-stable (`isStable_orthogonal`
  for `X'^⊥`). For `x₁ ∈ X ∖ W`: if `x₁ = a + b` with `a ∈ W'` and `b ∈ X'^⊥`, then
  `b = x₁ − a ∈ X' ⊓ X'^⊥ = 0`, so `x₁ ∈ W`, a contradiction; hence `x₁ ∉ W₁`. The Library
  `exists_ne_zero_inner_eq_zero_kfin` gives `v ≠ 0` orthogonal to `W₁`. Since `v ∉ X'^⊥`, some
  `x ∈ X'` has `⟪v, x⟫ ≠ 0`. With `u` the extension of `conj v` (`exists_conj_mem_dual`),
  `⟨u, w⟩ = ⟪v, w⟫ = 0` for `w ∈ W` and `⟨u, x⟩ = ⟪v, x⟫ ≠ 0`.

`realLeviDuality` combines `hyp_z` and `exists_annihilator_not_null`.
