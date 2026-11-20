import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # A holomorphic determinant witnessing the generic span of a holomorphic family

Let `a : Λ → E → F` be a family of maps holomorphic on a nonempty set `U`, with `F`
finite-dimensional. Then there are a point `z₁ ∈ U`, a finite set `s₁ ⊆ Λ` and a function
`h : E → ℂ` holomorphic on `U` with `h z₁ ≠ 0` such that at every `z ∈ U` with `h z ≠ 0` all
vectors `a l z` lie in the span of the `a μ z`, `μ ∈ s₁`.

`z₁` is chosen where the dimension of the span of all `a l z` is maximal; `s₁` indexes a basis
of that span at `z₁`; and `h` is the determinant of the matrix of coordinates
`(φ_μ (a l z))_{μ, l ∈ s₁}` for linear forms `φ_μ` dual to that basis. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.SeveralComplex

open Set Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F] {Λ : Type*}

/-- A finite product of holomorphic functions is holomorphic. -/
theorem differentiableOn_finset_prod_apply {ι : Type*} (s : Finset ι) {f : ι → E → ℂ}
    {U : Set E} (h : ∀ i ∈ s, DifferentiableOn ℂ (f i) U) :
    DifferentiableOn ℂ (fun z => ∏ i ∈ s, f i z) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp_rw [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- **Determinant witness for the generic span.** For a family `a` of maps holomorphic on a
nonempty set `U` with values in a finite-dimensional space, there are `z₁ ∈ U`, a finite set
`s₁` of indices and `h` holomorphic on `U` with `h z₁ ≠ 0`, such that wherever `h z ≠ 0` on `U`,
every `a l z` lies in the span of `{a μ z | μ ∈ s₁}`. -/
theorem exists_det_witness {U : Set E} (hU : U.Nonempty) {a : Λ → E → F}
    (ha : ∀ l, DifferentiableOn ℂ (a l) U) :
    ∃ z₁ ∈ U, ∃ s₁ : Finset Λ, ∃ h : E → ℂ, DifferentiableOn ℂ h U ∧ h z₁ ≠ 0 ∧
      ∀ z ∈ U, h z ≠ 0 → ∀ l, a l z ∈ Submodule.span ℂ ((fun μ => a μ z) '' s₁) := by
  classical
  -- the rank of the family at `z`
  set rk : E → ℕ := fun z => finrank ℂ (Submodule.span ℂ (range fun l => a l z)) with hrk
  have hbdd : BddAbove (rk '' U) := ⟨finrank ℂ F, by
    rintro _ ⟨z, -, rfl⟩
    exact Submodule.finrank_le _⟩
  obtain ⟨z₁, hz₁, hz₁max⟩ : ∃ z₁ ∈ U, ∀ z ∈ U, rk z ≤ rk z₁ := by
    obtain ⟨z₁, hz₁, hr⟩ := Nat.sSup_mem (hU.image rk) hbdd
    exact ⟨z₁, hz₁, fun z hz => hr ▸ le_csSup hbdd ⟨z, hz, rfl⟩⟩
  -- a basis of the span at `z₁` taken from the family
  obtain ⟨κ, ι, hιinj, hιspan, hli⟩ := exists_linearIndependent' ℂ (fun l => a l z₁)
  have hκfin : Finite κ := hli.finite
  have : Fintype κ := Fintype.ofFinite κ
  set W₁ := Submodule.span ℂ (range ((fun l => a l z₁) ∘ ι)) with hW₁
  set b : Basis κ ℂ W₁ := Basis.span hli with hb
  -- dual linear forms on `F`
  have hext : ∀ μ : κ, ∃ φ : F →ₗ[ℂ] ℂ, φ.comp W₁.subtype = b.coord μ :=
    fun μ => LinearMap.exists_extend (b.coord μ)
  choose φ hφ using hext
  have hφz₁ : ∀ μ l : κ, φ μ (a (ι l) z₁) = if l = μ then 1 else 0 := by
    intro μ l
    have h1 : a (ι l) z₁ = (b l : F) := by rw [hb, Basis.span_apply]; rfl
    rw [h1]
    have := congrArg (fun g : W₁ →ₗ[ℂ] ℂ => g (b l)) (hφ μ)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  -- the determinant
  set M : E → Matrix κ κ ℂ := fun z => Matrix.of fun μ l => φ μ (a (ι l) z) with hM
  set h : E → ℂ := fun z => (M z).det with hh
  have hMz₁ : M z₁ = 1 := by
    ext μ l
    simp only [hM, Matrix.of_apply, hφz₁, Matrix.one_apply]
    by_cases hlμ : l = μ
    · simp [hlμ]
    · simp [hlμ, Ne.symm hlμ]
  refine ⟨z₁, hz₁, Finset.univ.image ι, h, ?_, ?_, ?_⟩
  · -- holomorphy of the determinant
    have hent : ∀ μ l : κ, DifferentiableOn ℂ (fun z => φ μ (a (ι l) z)) U := by
      intro μ l
      exact (LinearMap.toContinuousLinearMap (φ μ)).differentiable.comp_differentiableOn (ha _)
    have : h = fun z => ∑ σ : Equiv.Perm κ,
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, φ (σ i) (a (ι i) z) := by
      funext z
      simp only [hh, Matrix.det_apply', hM, Matrix.of_apply]
    rw [this]
    refine DifferentiableOn.fun_sum fun σ _ => DifferentiableOn.const_mul ?_ _
    exact differentiableOn_finset_prod_apply _ fun i _ => hent _ _
  · simp [hh, hMz₁]
  · intro z hz hhz l
    -- linear independence of the chosen vectors at `z`
    set Φ : F →ₗ[ℂ] (κ → ℂ) := LinearMap.pi φ with hΦ
    have hcols : LinearIndependent ℂ (M z).col := Matrix.linearIndependent_cols_of_det_ne_zero hhz
    have hcomp : (M z).col = Φ ∘ fun l => a (ι l) z := by
      funext l μ
      simp [hM, hΦ, Matrix.col]
    rw [hcomp] at hcols
    have hliz : LinearIndependent ℂ (fun l => a (ι l) z) := hcols.of_comp
    have hle : Submodule.span ℂ (range fun l => a (ι l) z) ≤
        Submodule.span ℂ (range fun l => a l z) := by
      refine Submodule.span_mono ?_
      rintro _ ⟨l, rfl⟩
      exact ⟨ι l, rfl⟩
    have hrank : finrank ℂ (Submodule.span ℂ (range fun l => a l z)) ≤
        finrank ℂ (Submodule.span ℂ (range fun l => a (ι l) z)) := by
      rw [finrank_span_eq_card hliz]
      have h1 : finrank ℂ W₁ = Fintype.card κ := finrank_span_eq_card hli
      have h2 : rk z₁ = finrank ℂ W₁ := by
        simp only [hrk]
        rw [hιspan]
      calc _ = rk z := rfl
        _ ≤ rk z₁ := hz₁max z hz
        _ = Fintype.card κ := by rw [h2, h1]
    have heq := Submodule.eq_of_le_of_finrank_le hle hrank
    have himg : (fun μ => a μ z) '' ↑(Finset.univ.image ι) = range fun l => a (ι l) z := by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, ← Set.range_comp]
      rfl
    rw [himg, heq]
    exact Submodule.subset_span ⟨l, rfl⟩

end Langlands.Analysis.SeveralComplex
