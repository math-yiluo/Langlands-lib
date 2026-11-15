# Proof of `RealJacquetNonvanishingSubquotientReductionStatement`

Module: `Langlands.Representation.Archimedean.RealJacquetNonvanishingProof` (namespace
`Langlands.Archimedean.RealJacquetNonvanishing`).

Main theorem:
`Langlands.Archimedean.RealJacquetNonvanishing.realJacquetNonvanishingSubquotientReduction :
Langlands.Archimedean.RealJacquetNonvanishingSubquotientReductionStatement.{uV}`. The theorem
uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## What is proved

`RealJacquetNonvanishingSubquotientReductionStatement` is stated in the Library module
`Langlands.Representation.Archimedean.RealJacquetSubquotientReduction`. It says that
`RealPrincipalSeriesSubquotientStatement` (Harish-Chandra's subquotient theorem for `GL_n(ℝ)` in
the form "every irreducible admissible `(𝔤𝔩_n(ℝ), O(n))`-module is `W / ker T` for a
`(𝔤, K)`-stable space `W` of `O(n)`-finite functions of a principal series
`realStandardModule n (cs.map RealBlock.character)` and a surjective intertwiner `T : W → V`")
implies `RealJacquetNonvanishingStatement` (`realJacquetSubspace n π ≠ ⊤`, i.e. `𝔫V ≠ V`).

The proof follows the route indicated by Wallach (1979, 4.13): the subquotient theorem plus
Casselman's matrix-coefficient technique. In place of asymptotic expansions it uses the decay
and Gronwall estimates of `RealJacquetGronwall`.

## Helper modules

The proof uses four helper modules, submitted with it:

- `RealJacquetRadialFiniteness`: radial finiteness (`radial_finiteness`).
- `RealJacquetMatrixCoefficient`: the matrix coefficient `mc w ψ g = ∫_{O(n)} w(k g) ψ(k) dk`.
  It provides vanishing on orthogonal subspaces, the adjoint law, the ray derivative, and the
  growth bound.
- `RealJacquetSeparation`: a dual vector separating a vector from a subrepresentation.
- `RealJacquetGronwall`: the abstract vanishing theorem `eq_zero`.

Each has its own Markdown file.

## Declarations of this module

**Matrix units** (top level). `expDiagonal_inv` gives `exp(sH)⁻¹ = exp(-sH)`, and
`expDiagonal_conj_E` gives `exp(sH) E_{ab} exp(sH)⁻¹ = e^{s (h_a - h_b)} E_{ab}`.

**Kernel** (section `Kernel`). `kerFun T` is the kernel of `T`, viewed as a space of functions.
It is contained in `W` (`kerFun_le`) and stable under `R(k)`, `k ∈ O(n)`
(`rightTranslation_mem_kerFun`), and under `R(X)` (`rightDerivative_mem_kerFun`). Both follow
from the two clauses of `IsRealSubquotientMap`.

**Orthogonal space** (section `Orthogonal`). Fix `ds = cs.map character` and the list `ds'`
with pointwise inverse position characters (`hχ`).

- `orthSub T ds' hW`: the functions `ψ ∈ KF n ds'` with `mc w ψ 1 = 0` for all `w ∈ kerFun T`.
  It is stable under right translation by `O(n)` (`rep_mem_orthSub`, by
  `mc_one_rightTranslation`) and under right derivatives (`lie_mem_orthSub`, by the adjoint law
  `mc_rightDerivative` at `g = 1`).
- `Rop hW hT hχ a b`: `R(E_{ab})` restricted to `orthSub`, with `Rop_coe`.
- `mcForm T ds' hW h s : orthSub →ₗ W →ₗ ℂ`, `(ψ, w) ↦ mc w ψ (exp(s H))`, for `H = diag(h)`.
  `ellForm T ds' hW g h s = (mcForm …).compl₂ g` for a linear right inverse `g` of `T`
  (`ellForm_apply`).
- `ellForm_T`: `ellForm … s ψ (T w) = mc w ψ (exp(sH))`. The difference `g(T w) - w` lies in the
  kernel, and `mc_eq_zero_of_orthogonal` kills it.
- `ellForm_op_E` (hypothesis `hadj` of `eq_zero`):
  `ellForm … s ψ (op π (E a b) v) = -e^{s (h_a - h_b)} · ellForm … s (Rop a b ψ) v`. Proof:
  `π(1 ⊗ E_{ab}) T = T R(E_{ab})` (`IsRealSubquotientMap`), `ellForm_T`, `mc_rightDerivative`,
  `expDiagonal_conj_E`, and real-linearity of `R` in the direction (`rightDerivative_smul_left`).
- `ellForm_hasDerivAt` (hypothesis `hderiv`): from `hasDerivAt_mc` and `ellForm_T`.
- `ellForm_growth` (hypothesis `hgrowth`): from `exists_growth`.
- `exists_spanning_family`: for `ψ₀ ∈ orthSub`, the `O(n)`-orbit span `O` of `ψ₀` in `KF n ds'`
  is finite-dimensional (first clause of `isRealGKModule_realStandardModule`) and contained in
  `orthSub`. A finite generating family of `O` (`Submodule.fg_iff_exists_fin_generating_family`)
  gives `bΨ : Fin p → orthSub`. Its span contains `⟨ψ₀, _⟩`, and it is stable under
  `Rop a b - Rop b a = R(E_{ab} - E_{ba})`, because `O` is stable under the antisymmetric
  derivatives (`apply_skew_mem_of_rho_stable` for the `(𝔤, K)`-module `realStandardRep`,
  `realStandardLie`).

**Separation** (section `Separation`). `exists_orthogonal_ne_zero`: for `w ∈ W` with `T w ≠ 0`
there is `ψ₀ ∈ orthSub` with `pairing ⟨w, _⟩ ψ₀ ≠ 0`. The kernel is a subrepresentation `N` of
`realStandardRep n ds` not containing `w`. The pairing separates the points of `KF n ds`: this
is `RealPrincipalSeriesDuality.exists_pairing_ne_zero` with the roles of `cs` and the inverse
list exchanged (`realPositionCharacter_map_inverse_mul`), and with the factors of the integrand
commuted. Then `RealJacquetSeparation.exists_orthogonal_pairing_ne_zero` applies.

**Reduction** (section `Reduction`).

- `rayWeights n i = i`, so `rayWeights a - rayWeights b ≤ -1` for `a < b`
  (`rayWeights_sub_le`, hypothesis `hh`).
- `ellForm_eq_zero_of_pos`: if `𝔫V = V`, then `ellForm … s₀ ψ₀ v₀ = 0` for every `s₀ > 0`, every
  `ψ₀` in the span of a family `bΨ` as above, and every `v₀ ∈ V`. Apply `eq_zero` with
  `F = FiniteVectors.orbitSpan ρ v₀`. `F` is finite-dimensional by the first clause of
  `IsRealGKModule`, and stable under antisymmetric `Y` by `apply_skew_mem_of_rho_stable`.
- `mc_one_eq_zero`: if `ellForm … s₀ ψ₀ v₀ = 0` for all `s₀ > 0`, then
  `mc (g v₀) ψ₀ 1 = 0`. The function `s ↦ ellForm … s ψ₀ v₀` is continuous
  (`ellForm_hasDerivAt`). It vanishes on `(0, ∞)`, so its value at `0` is the limit from the
  right, which is `0` (`tendsto_nhds_unique`). At `s = 0`, `exp(0 · H) = 1`.

## Proof of the main theorem

Assume `RealPrincipalSeriesSubquotientStatement`, and let `(ρ, π)` be an irreducible admissible
module with `realJacquetSubspace n π = ⊤`. Take `cs`, `W`, `T` from the subquotient theorem.
`π` has an infinitesimal character (`realGKModuleInfinitesimalCharacter`). Choose a linear
right inverse `g` of `T` (`LinearMap.exists_rightInverse_of_surjective`) and `v₀ ≠ 0`. Then
`T (g v₀) = v₀ ≠ 0`.

1. `exists_orthogonal_ne_zero` gives `ψ₀ ∈ orthSub` with `∫_{O(n)} (g v₀) ψ₀ ≠ 0`.
2. `exists_spanning_family` gives `bΨ`.
3. `ellForm_eq_zero_of_pos` and `mc_one_eq_zero` give `mc (g v₀) ψ₀ 1 = 0`. This integral equals
   `∫_{O(n)} (g v₀) ψ₀`, a contradiction.
