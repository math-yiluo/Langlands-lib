import Langlands.Representation.Archimedean.OrthogonalFinitePolynomial

/-!
# Finiteness of right translates under sums, products and polynomials
-/

noncomputable section

namespace Langlands.Archimedean

set_option autoImplicit false

namespace TranslateFinite

variable {G : Type*} [Group G] {ι : Type*} (s : ι → G)

/-- The right translates `f(· s_i)` of `f` span a finite-dimensional space. -/
def IsTranslateFinite (f : G → ℂ) : Prop :=
  FiniteDimensional ℂ
    (Submodule.span ℂ (Set.range fun i => Whittaker.rightTranslation ℂ G (s i) f))

theorem rightTranslation_apply (g : G) (f : G → ℂ) (x : G) :
    Whittaker.rightTranslation ℂ G g f x = f (x * g) := rfl

theorem isTranslateFinite_const (c : ℂ) : IsTranslateFinite s (fun _ => c) := by
  unfold IsTranslateFinite
  have h : Set.range (fun i => Whittaker.rightTranslation ℂ G (s i) (fun _ : G => c)) ⊆
      {fun _ => c} := by
    rintro _ ⟨i, rfl⟩
    rfl
  have : FiniteDimensional ℂ (Submodule.span ℂ ({fun _ => c} : Set (G → ℂ))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_singleton _)
  exact Submodule.finiteDimensional_of_le (Submodule.span_mono h)

variable {s}

theorem isTranslateFinite_add {f g : G → ℂ} (hf : IsTranslateFinite s f)
    (hg : IsTranslateFinite s g) : IsTranslateFinite s (fun x => f x + g x) := by
  unfold IsTranslateFinite at *
  have hle : Submodule.span ℂ (Set.range fun i =>
      Whittaker.rightTranslation ℂ G (s i) (fun x => f x + g x)) ≤
      Submodule.span ℂ (Set.range fun i => Whittaker.rightTranslation ℂ G (s i) f) ⊔
        Submodule.span ℂ (Set.range fun i => Whittaker.rightTranslation ℂ G (s i) g) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    have : Whittaker.rightTranslation ℂ G (s i) (fun x => f x + g x) =
        Whittaker.rightTranslation ℂ G (s i) f + Whittaker.rightTranslation ℂ G (s i) g := rfl
    change Whittaker.rightTranslation ℂ G (s i) (fun x => f x + g x) ∈ _
    rw [this]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨i, rfl⟩) (Submodule.subset_span ⟨i, rfl⟩)
  exact Submodule.finiteDimensional_of_le hle

theorem isTranslateFinite_mul {f g : G → ℂ} (hf : IsTranslateFinite s f)
    (hg : IsTranslateFinite s g) : IsTranslateFinite s (fun x => f x * g x) := by
  unfold IsTranslateFinite at *
  set A := Submodule.span ℂ (Set.range fun i => Whittaker.rightTranslation ℂ G (s i) f)
  set B := Submodule.span ℂ (Set.range fun i => Whittaker.rightTranslation ℂ G (s i) g)
  have hle : Submodule.span ℂ (Set.range fun i =>
      Whittaker.rightTranslation ℂ G (s i) (fun x => f x * g x)) ≤ A * B := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    have : Whittaker.rightTranslation ℂ G (s i) (fun x => f x * g x) =
        Whittaker.rightTranslation ℂ G (s i) f * Whittaker.rightTranslation ℂ G (s i) g := rfl
    change Whittaker.rightTranslation ℂ G (s i) (fun x => f x * g x) ∈ _
    rw [this]
    exact Submodule.mul_mem_mul (Submodule.subset_span ⟨i, rfl⟩) (Submodule.subset_span ⟨i, rfl⟩)
  have hAB : (A * B).FG := (Submodule.fg_iff_finiteDimensional A).mpr hf |>.mul
    ((Submodule.fg_iff_finiteDimensional B).mpr hg)
  have : FiniteDimensional ℂ (A * B) := (Submodule.fg_iff_finiteDimensional _).mp hAB
  exact Submodule.finiteDimensional_of_le hle

theorem isTranslateFinite_pow {f : G → ℂ} (hf : IsTranslateFinite s f) (N : ℕ) :
    IsTranslateFinite s (fun x => f x ^ N) := by
  induction N with
  | zero => simpa using isTranslateFinite_const s 1
  | succ N ih => simpa [pow_succ] using isTranslateFinite_mul ih hf

theorem isTranslateFinite_smul {f : G → ℂ} (hf : IsTranslateFinite s f) (c : ℂ) :
    IsTranslateFinite s (fun x => c * f x) := by
  simpa using isTranslateFinite_mul (isTranslateFinite_const s c) hf

/-! ## Polynomial functions on `O(n)` -/

variable {n : ℕ}

theorem isTranslateFinite_entry (ij : Fin n × Fin n) :
    IsTranslateFinite (id : Matrix.unitaryGroup (Fin n) ℝ → Matrix.unitaryGroup (Fin n) ℝ)
      (fun κ => (((κ : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2 : ℝ) : ℂ)) := by
  unfold IsTranslateFinite
  set S := Submodule.span ℂ (Set.range fun l : Fin n =>
    fun κ : Matrix.unitaryGroup (Fin n) ℝ => (((κ : Matrix (Fin n) (Fin n) ℝ) ij.1 l : ℝ) : ℂ))
  have : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  suffices hle : Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ =>
      Whittaker.rightTranslation ℂ (Matrix.unitaryGroup (Fin n) ℝ) (id k)
        (fun κ => (((κ : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2 : ℝ) : ℂ))) ≤ S from
    Submodule.finiteDimensional_of_le hle
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  have h : Whittaker.rightTranslation ℂ (Matrix.unitaryGroup (Fin n) ℝ) (id k)
      (fun κ => (((κ : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2 : ℝ) : ℂ)) =
      ∑ l : Fin n, (((k : Matrix (Fin n) (Fin n) ℝ) l ij.2 : ℝ) : ℂ) •
        fun κ : Matrix.unitaryGroup (Fin n) ℝ =>
          (((κ : Matrix (Fin n) (Fin n) ℝ) ij.1 l : ℝ) : ℂ) := by
    funext κ
    rw [rightTranslation_apply, Finset.sum_apply]
    simp only [id, Pi.smul_apply, smul_eq_mul]
    change ((((κ : Matrix (Fin n) (Fin n) ℝ) * (k : Matrix (Fin n) (Fin n) ℝ)) ij.1 ij.2 : ℝ) : ℂ) = _
    rw [Matrix.mul_apply]
    push_cast
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  change Whittaker.rightTranslation ℂ (Matrix.unitaryGroup (Fin n) ℝ) (id k)
      (fun κ => (((κ : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2 : ℝ) : ℂ)) ∈ S
  rw [h]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

/-- **Polynomial functions on `O(n)` are `O(n)`-finite.** -/
theorem finiteDimensional_span_eval (P : MvPolynomial (Fin n × Fin n) ℂ) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ =>
      fun x : Matrix.unitaryGroup (Fin n) ℝ =>
        MvPolynomial.eval (fun ij => (((x * k : Matrix.unitaryGroup (Fin n) ℝ) :
          Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2 : ℂ)) P)) := by
  have h : IsTranslateFinite (id : Matrix.unitaryGroup (Fin n) ℝ → Matrix.unitaryGroup (Fin n) ℝ)
      (fun κ => MvPolynomial.eval (fun ij => (((κ : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2 : ℝ) : ℂ))
        P) := by
    induction P using MvPolynomial.induction_on with
    | C a => simpa using isTranslateFinite_const id a
    | add p q hp hq => simpa using isTranslateFinite_add hp hq
    | mul_X p ij hp => simpa using isTranslateFinite_mul hp (isTranslateFinite_entry ij)
  exact h

end TranslateFinite

end Langlands.Archimedean
