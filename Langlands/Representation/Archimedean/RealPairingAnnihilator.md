# Annihilators for the `O(n)`-integration pairing

Module `Langlands.Representation.Archimedean.RealPairingAnnihilator`, namespace
`Langlands.Archimedean.RealPairingAnnihilator`.

## Purpose and provenance

Let `ds` be a list of real blocks of rank `n` (module `StandardModule`). Write

- `X = kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)`, the `O(n)`-finite
  functions of the real standard module of `ds`;
- `Y = kFiniteFunctions (principalSeries ℝ n (dualChar (realPositionCharacter ds)))
  (unitaryCompact ℝ n)`, the `O(n)`-finite functions of the principal series of the inverse
  position characters of `ds`;

paired by `⟨z, h⟩ = ∫_{O(n)} z(κ) h(κ) dκ` (Haar probability measure `haarK n`). For a
subspace `V` of `Y` the module defines the orthogonal `perp ds V ⊆ X` and proves two facts:

- if `V` is a `(𝔤, K)`-submodule of `Y`, then `perp ds V` is a `(𝔤, K)`-submodule of `X`;
- if `V` is stable under `O(n)`, then every `u ∈ Y` that vanishes on `perp ds V` agrees on `X`
  with some member of `V`. In other words, the annihilator of `perp ds V` in `Y` is `V` plus
  the annihilator of `X` in `Y`.

This is internal infrastructure for the reverse-intertwiner step of the proof of
`RealStandardIrreducibleCriterionStatement` (`RealReverseIntertwinerKernelStatement`, module `RealStandardIrreducibleCriterionReduction`)
for lists with induction blocks: a proper `(𝔤, K)`-submodule `V` of `Y` gives the
`(𝔤, K)`-submodule `perp ds V` of `X`, and the second fact identifies the functionals of `Y`
that vanish on it. The statements are standard finite-dimensional duality applied blockwise
(isotypic component by isotypic component, each finite-dimensional by admissibility). They have
no specific literature source. The relative separation lemma `mem_of_vanishing` generalizes
`KFiniteDual.mem_of_separating` (Library module `KFiniteDual`), the case where the common
kernel is `0`, and its proof follows that proof.

## Statements

### Relative separation

Context: `K` a group, `ρ` a complex representation of `K` on `V` that is semisimple as a module
over the group algebra `ℂ[K]`, with every block (isotypic component, `KFiniteDual.Block ρ`)
finite-dimensional (`hblock`).

- `exists_mem_comp_proj_eq_of_vanishing hblock G c hvan`: let `G` be a subspace of the
  algebraic dual of `V`, `c` a block and `ℓ` a functional with `ℓ v = 0` for every `v` on which
  every `w ∈ G` vanishes. Then some `w ∈ G` satisfies `w ∘ proj c = ℓ ∘ proj c`, where `proj c`
  is the projection onto the block `c` along the other blocks.
- `mem_of_vanishing hblock G hG hℓ hvan`: let `G` be a subrepresentation of the dual
  representation `ρ.dual` consisting of finite vectors (`hG`), and `ℓ` a finite vector of
  `ρ.dual` (`hℓ`) with `ℓ v = 0` for every `v` on which every `w ∈ G` vanishes (`hvan`). Then
  `ℓ ∈ G`.

### The pairing of the standard module with the dual principal series

- `perp ds V` (definition), for `V` a complex subspace of `Y`: the subspace of `X` of the `h`
  with `⟨z, h⟩ = 0` for all `z ∈ V`. It is defined as the dual coannihilator of the image of
  `V` under the pairing map `intPairing` (module `RealReverseTransfer`).
- `mem_perp h`: `h ∈ perp ds V ↔ ∀ z ∈ V, ∫ z(κ) h(κ) dκ = 0`.
- `integral_rightDerivative_mul_add ds Y hz hh hzc hhc`: for a matrix `Y`, `z` in the dual
  principal series of `ds` and `h` in the real standard module of `ds` whose right derivatives
  `R_Y z`, `R_Y h` along `Y` are continuous,
  `∫ (R_Y z)(κ) h(κ) dκ + ∫ z(κ) (R_Y h)(κ) dκ = 0`.
- `isGKSubmodule_perp ds hV`: if `V` is a `(𝔤, K)`-submodule of `Y` for
  `principalSeriesRep`/`principalSeriesLie` (predicate `IsGKSubmodule`, Library module
  `RealLargeLanglandsQuotientReduction`), then `perp ds V` is a `(𝔤, K)`-submodule of `X` for
  `realStandardRep n ds`/`realStandardLie n ds`.
- `exists_eq_of_vanishing ds hVK u hu`: let `V ⊆ Y` be stable under the action
  `principalSeriesRep` of every `k ∈ O(n)` (`hVK`), and `u ∈ Y` with `∫ u(κ) h(κ) dκ = 0` for
  every `h ∈ perp ds V` (`hu`). Then there is `z ∈ V` with
  `∫ u(κ) h(κ) dκ = ∫ z(κ) h(κ) dκ` for every `h ∈ X`.

## Proofs

`exists_mem_comp_proj_eq_of_vanishing`. Let `r` be restriction of functionals to the
finite-dimensional block `c` and `D = r(G)`. By finite-dimensional duality
(`Subspace.dualCoannihilator_dualAnnihilator_eq`), `D` is the annihilator of its common kernel
in the block. A vector `x` of the block in that common kernel is killed by every `w ∈ G`, so
`ℓ x = 0` by `hvan`; hence `r ℓ ∈ D`, i.e. `r ℓ = r w` for some `w ∈ G`. Evaluating at
`projTo c v` gives `w (proj c v) = ℓ (proj c v)`.

`mem_of_vanishing`. As in `KFiniteDual.mem_of_separating`: a finite vector `ℓ` of the dual is
the finite sum of its block parts `ℓ ∘ proj c` (`eq_sum_comp_proj`). Each part equals
`w ∘ proj c` for some `w ∈ G` by the previous lemma, and `w ∘ proj c` lies in the orbit span of
the finite vector `w` (`comp_proj_mem_orbitSpan`), hence in the subrepresentation `G`
(`FiniteVectors.orbitSpan_le`).

`mem_perp`: unfolding `Submodule.mem_dualCoannihilator` and `intPairing`.

`integral_rightDerivative_mul_add`. The product `z h` is smooth (`contMDiff_mul_fun`) and,
since the characters of `z` are the inverses of those of `h`, it is left-equivariant for the
modulus character (`isModulusEquivariant_mul`, with `(isSignedPower ds).ne_zero` for the
character values). For such functions the `O(n)`-integral of a right derivative is zero
(`integral_rightDerivative_eq_zero`, Library module `RealJacquetMatrixCoefficient`), and the
right derivative of a product obeys the Leibniz rule (`rightDerivative_mul_fun`). The two
integrands are products of continuous functions on the compact group, hence integrable
(`integrable_mul_of_continuous`), so the integral of the sum splits.

`isGKSubmodule_perp`.

- `O(n)`-stability: let `h ∈ perp ds V`, `k ∈ O(n)` and `z ∈ V`. Then `k⁻¹ · z ∈ V`, so
  `∫ z(κ k⁻¹) h(κ) dκ = 0`. By right invariance of Haar measure (`integral_translate_mul`,
  module `RealReverseTransfer`), `∫ z(κ) h(κ k) dκ = ∫ h(κ k) z(κ) dκ = ∫ h(κ) z(κ k⁻¹) dκ = 0`,
  i.e. `⟨z, k · h⟩ = 0`.
- `𝔤`-stability: for a real matrix `Y` and `z ∈ V`, the action of `1 ⊗ Y` is the right
  derivative on both sides (`principalSeriesLie_one_tmul_apply_coe`,
  `realStandardLie_one_tmul_apply_coe`). Since `(1 ⊗ Y) · z ∈ V`, `⟨R_Y z, h⟩ = 0`, and
  `integral_rightDerivative_mul_add` gives `⟨z, R_Y h⟩ = 0`. A general element of
  `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)` is handled by induction on tensors (`TensorProduct.inductionOn`):
  `c ⊗ Y = c • (1 ⊗ Y)` and the action is linear, and sums split by linearity of the integral.

`exists_eq_of_vanishing`. Let `Qd = intPairing : Y → X*`, `Qd z = ⟨z, ·⟩`. It is
`O(n)`-equivariant from `principalSeriesRep` to the dual of `realStandardRep n ds` (right
invariance of Haar measure, `integral_translate_mul`). The image `G = Qd(V)` is then a
subrepresentation of the dual, because `V` is `O(n)`-stable. Every element of `Y` is an
`O(n)`-finite vector (`isRealGKModule_principalSeries`), so its image is a finite vector of the
dual (`isFiniteVector_dual_of_equivariant`, module `RealReverseTransfer`); this applies to `G`
and to `Qd u`. The representation `realStandardRep n ds` on `X` is semisimple
(`KFiniteDual.isSemisimpleModule`, using `isRealGKModule_realStandardModule`) with
finite-dimensional blocks (`KFiniteDual.finiteDimensional_block`, admissibility
`realStandardAdmissible`). The common kernel of `G` in `X` is `perp ds V` (`mem_perp`), and
`Qd u` vanishes on it by `hu`. So `mem_of_vanishing` gives `Qd u ∈ G`, i.e. `Qd u = Qd z` for
some `z ∈ V`; evaluating at `h` (`intPairing_apply`) gives the claimed identity of integrals.
