import Langlands.Representation.Archimedean.ComplexLinkedLanglandsQuotientGrowth

/-!
# Tools for small growth bounds on principal series

`SmallGrowth n χ` is the conclusion of `ComplexLinkedSmallGrowthStatement` for the principal series
of `χ`: a nonzero finite-dimensional `U(n)`-stable subspace `E` of the `U(n)`-finite functions
with `dim U_d(𝔤) · E ≤ C (d + 1)^{n(n-1)-1}`.

* `coe_mem_of_mem_filtrationSpan`, `finrank_filtrationSpan_le`: if subspaces `W_N` of functions
  increase with `N`, right derivatives map `W_N` to `W_{N+1}`, and `E ⊆ W_0`, then
  `U_d(𝔤) · E ⊆ W_d`, so `dim U_d(𝔤) · E ≤ dim W_d`.
* `smallGrowth_of_intertwine`: `SmallGrowth` transports along injective intertwining maps (using
  the Library's `envelopingAction_intertwine`).
-/

noncomputable section

open scoped TensorProduct Matrix Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Algebra.UniversalEnveloping ComplexLinkedLanglandsQuotientGrowth

set_option backward.isDefEq.respectTransparency false

namespace SmallGrowthTools

/-- The conclusion of `ComplexLinkedSmallGrowthStatement` for the principal series of `χ`. -/
def SmallGrowth (n : ℕ) (χ : ℕ → ℂˣ → ℂ) : Prop :=
  ∃ E : Submodule ℂ (kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)),
    E ≠ ⊥ ∧ FiniteDimensional ℂ E ∧
      (∀ (k : Matrix.unitaryGroup (Fin n) ℂ), ∀ e ∈ E, principalSeriesRep ℂ n χ k e ∈ E) ∧
      ∃ C : ℝ, ∀ d : ℕ,
        (Module.finrank ℂ (filtrationSpan (principalSeriesLie ℂ n χ) d E) : ℝ) ≤
          C * ((d : ℝ) + 1) ^ (n * (n - 1) - 1)

variable {n : ℕ} {χ : ℕ → ℂˣ → ℂ}

/-! ## Filtrations by levels -/

section Levels

variable (W : ℕ → Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ))
  (hmono : ∀ N, W N ≤ W (N + 1))
  (hstep : ∀ N (f : Langlands.GeneralLinear n ℂ → ℂ), f ∈ W N →
    ∀ X : Matrix (Fin n) (Fin n) ℂ, rightDerivative (matrixModel ℂ n) X f ∈ W (N + 1))

/-- The level `N` inside the `U(n)`-finite functions. -/
abbrev levelIn (N : ℕ) :
    Submodule ℂ (kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)) :=
  (W N).comap (kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)).subtype

include hstep in
theorem lie_mem_levelIn (x : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) {N : ℕ}
    {f : kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)}
    (hf : f ∈ levelIn (χ := χ) W N) : principalSeriesLie ℂ n χ x f ∈ levelIn W (N + 1) := by
  induction x using TensorProduct.inductionOn with
  | tmul c X =>
    rw [tmul_eq_smul, map_smul, LinearMap.smul_apply]
    refine Submodule.smul_mem _ c ?_
    change ((principalSeriesLie ℂ n χ (1 ⊗ₜ X) f :
      kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)) :
        Langlands.GeneralLinear n ℂ → ℂ) ∈ W (N + 1)
    rw [principalSeriesLie_one_tmul_apply_coe]
    exact hstep N _ hf X
  | add x y hx hy =>
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ hx hy

include hmono hstep in
theorem degreeOne_mem_levelIn {a : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ)}
    (ha : a ∈ degreeOne ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ)) {N : ℕ}
    {f : kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)}
    (hf : f ∈ levelIn (χ := χ) W N) :
    envelopingAction (principalSeriesLie ℂ n χ) a f ∈ levelIn W (N + 1) := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 ha
  rw [map_add, LinearMap.add_apply]
  refine Submodule.add_mem _ ?_ ?_
  · obtain ⟨r, rfl⟩ := Submodule.mem_one.1 hy
    rw [AlgHom.commutes, Module.algebraMap_end_apply]
    exact Submodule.smul_mem _ r (hmono N hf)
  · obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 hz
    change envelopingAction (principalSeriesLie ℂ n χ) (UniversalEnvelopingAlgebra.ι ℂ x) f ∈ _
    rw [UniversalEnvelopingAlgebra.lift_ι_apply]
    exact lie_mem_levelIn W hstep x hf

include hmono hstep in
theorem degreeFiltration_mem_levelIn (d : ℕ)
    {a : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ)}
    (ha : a ∈ degreeFiltration ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) d) {N : ℕ}
    {f : kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)}
    (hf : f ∈ levelIn (χ := χ) W N) :
    envelopingAction (principalSeriesLie ℂ n χ) a f ∈ levelIn W (N + d) := by
  induction d generalizing a N f with
  | zero =>
    rw [degreeFiltration_zero] at ha
    obtain ⟨r, rfl⟩ := Submodule.mem_one.1 ha
    rw [AlgHom.commutes, Module.algebraMap_end_apply]
    exact Submodule.smul_mem _ r hf
  | succ d ih =>
    rw [degreeFiltration, pow_succ] at ha
    induction ha using Submodule.mul_induction_on' with
    | mem_mul_mem x hx y hy =>
      rw [map_mul, Module.End.mul_apply]
      have h1 := degreeOne_mem_levelIn W hmono hstep hy hf
      have h2 := ih hx h1
      rwa [show N + 1 + d = N + (d + 1) by omega] at h2
    | add x _ y _ hx hy =>
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ hx hy

include hmono hstep in
/-- **`U_d(𝔤) · E ⊆ W_d`.** -/
theorem filtrationSpan_le_levelIn
    (E : Submodule ℂ (kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)))
    (hE : E ≤ levelIn W 0) (d : ℕ) :
    filtrationSpan (principalSeriesLie ℂ n χ) d E ≤ levelIn W d := by
  refine Submodule.map₂_le.2 fun a ha e he => ?_
  have := degreeFiltration_mem_levelIn W hmono hstep d ha (hE he)
  rwa [zero_add] at this

include hmono hstep in
/-- **`dim U_d(𝔤) · E ≤ dim W_d`.** -/
theorem finrank_filtrationSpan_le
    (E : Submodule ℂ (kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)))
    (hE : E ≤ levelIn W 0) (d : ℕ) [FiniteDimensional ℂ (W d)] :
    Module.finrank ℂ (filtrationSpan (principalSeriesLie ℂ n χ) d E) ≤
      Module.finrank ℂ (W d) := by
  have hle := filtrationSpan_le_levelIn W hmono hstep E hE d
  let Φ : filtrationSpan (principalSeriesLie ℂ n χ) d E →ₗ[ℂ] W d :=
    LinearMap.codRestrict (W d)
      ((kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)).subtype.comp
        (filtrationSpan (principalSeriesLie ℂ n χ) d E).subtype) fun x => hle x.2
  have hinj : Function.Injective Φ := by
    intro x y hxy
    have := congrArg (fun z : W d => (z : Langlands.GeneralLinear n ℂ → ℂ)) hxy
    exact Subtype.ext (Subtype.ext this)
  exact LinearMap.finrank_le_finrank_of_injective hinj

end Levels

/-! ## Transport along intertwining maps -/

/-- **Small growth transports along injective intertwining maps.** -/
theorem smallGrowth_of_intertwine {χ₁ χ₂ : ℕ → ℂˣ → ℂ}
    (A : kFiniteFunctions (principalSeries ℂ n χ₁) (unitaryCompact ℂ n) →ₗ[ℂ]
      kFiniteFunctions (principalSeries ℂ n χ₂) (unitaryCompact ℂ n))
    (hinj : Function.Injective A)
    (hK : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) f,
      A (principalSeriesRep ℂ n χ₁ k f) = principalSeriesRep ℂ n χ₂ k (A f))
    (hL : ∀ x f, A (principalSeriesLie ℂ n χ₁ x f) = principalSeriesLie ℂ n χ₂ x (A f))
    (h : SmallGrowth n χ₁) : SmallGrowth n χ₂ := by
  obtain ⟨E, hE0, hEfin, hEK, C, hC⟩ := h
  refine ⟨E.map A, ?_, inferInstance, ?_, C, fun d => ?_⟩
  · intro hbot
    apply hE0
    rw [eq_bot_iff]
    intro e he
    have : A e ∈ E.map A := Submodule.mem_map_of_mem he
    rw [hbot, Submodule.mem_bot] at this
    rw [Submodule.mem_bot]
    exact hinj (this.trans (map_zero A).symm)
  · rintro k _ ⟨e, he, rfl⟩
    rw [← hK]
    exact Submodule.mem_map_of_mem (hEK k e he)
  · have hfd : FiniteDimensional ℂ (filtrationSpan (principalSeriesLie ℂ n χ₁) d E) :=
      Module.Finite.iff_fg.2 ((degreeFiltration_fg ℂ _ d).map₂ _ (Module.Finite.iff_fg.1 hEfin))
    have hle : filtrationSpan (principalSeriesLie ℂ n χ₂) d (E.map A) ≤
        (filtrationSpan (principalSeriesLie ℂ n χ₁) d E).map A := by
      refine Submodule.map₂_le.2 fun a ha y hy => ?_
      obtain ⟨e, he, rfl⟩ := hy
      change envelopingAction (principalSeriesLie ℂ n χ₂) a (A e) ∈ _
      rw [← Langlands.Archimedean.envelopingAction_intertwine _ _ A hL]
      exact Submodule.mem_map_of_mem (Submodule.apply_mem_map₂ _ ha he)
    have h1 := Submodule.finrank_mono hle
    have h2 : Module.finrank ℂ ((filtrationSpan (principalSeriesLie ℂ n χ₁) d E).map A) =
        Module.finrank ℂ (filtrationSpan (principalSeriesLie ℂ n χ₁) d E) :=
      (Submodule.equivMapOfInjective A hinj _).finrank_eq.symm
    calc (Module.finrank ℂ (filtrationSpan (principalSeriesLie ℂ n χ₂) d (E.map A)) : ℝ)
        ≤ Module.finrank ℂ (filtrationSpan (principalSeriesLie ℂ n χ₁) d E) := by
          exact_mod_cast h1.trans h2.le
      _ ≤ _ := hC d

end SmallGrowthTools

end Langlands.Archimedean
