import Langlands.Representation.Filtration.FiniteFilteredExactness

/-! The cokernel of a finitely filtered map computed from one surviving step. -/

noncomputable section

namespace Langlands.FiniteFiltered

universe uR uA uB uC

variable {R : Type uR} [CommRing R]
variable {A : Type uA} [AddCommGroup A] [Module R A]
variable {B : Type uB} [AddCommGroup B] [Module R B]
variable {C : Type uC} [AddCommGroup C] [Module R C]

/-- Surjectivity in one grade lifts a vector to an image modulo the lower step. -/
theorem reduction_of_graded_surjective
    (g : B →ₗ[R] C) (T : ℕ → Submodule R B) (U : ℕ → Submodule R C)
    (hg : Preserves g T U) (i : ℕ) (hsurj : Function.Surjective (gradedMap g T U hg i))
    (c : C) (hc : c ∈ U (i + 1)) :
    ∃ b ∈ T (i + 1), c - g b ∈ U i := by
  obtain ⟨qb, hqb⟩ := hsurj ((denominator U i).mkQ ⟨c, hc⟩)
  obtain ⟨b, rfl⟩ := (denominator T i).mkQ_surjective qb
  refine ⟨b, b.property, ?_⟩
  rw [gradedMap_mk] at hqb
  have hzero : (denominator U i).mkQ (⟨c, hc⟩ - stepMap g T U hg i b) = 0 := by
    rw [map_sub, ← hqb, sub_self]
  exact (Submodule.Quotient.mk_eq_zero (denominator U i)).mp hzero

/-- Surjectivity in every grade above `i₀` moves each vector into `U (i₀ + 1)`
modulo the range. -/
theorem exists_sub_mem_of_graded_surjective
    (g : B →ₗ[R] C) (T : ℕ → Submodule R B) (U : ℕ → Submodule R C)
    (hg : Preserves g T U) (hU : Monotone U) (i₀ n : ℕ)
    (hsurj : ∀ i, i₀ < i → i < n → Function.Surjective (gradedMap g T U hg i)) :
    ∀ j ≤ n, ∀ c ∈ U j, ∃ b, c - g b ∈ U (i₀ + 1) := by
  intro j
  induction j with
  | zero =>
    intro _ c hc
    exact ⟨0, by simpa using hU (Nat.zero_le _) hc⟩
  | succ j ih =>
    intro hj c hc
    by_cases hji : j + 1 ≤ i₀ + 1
    · exact ⟨0, by simpa using hU hji hc⟩
    · obtain ⟨b, -, hb⟩ := reduction_of_graded_surjective g T U hg j
        (hsurj j (by omega) (by omega)) c hc
      obtain ⟨b', hb'⟩ := ih (by omega) (c - g b) hb
      exact ⟨b + b', by rw [map_add, ← sub_sub]; exact hb'⟩

/-- Exactness in every grade above `i₀` shows that an image lying in
`U (i₀ + 1)` vanishes when `T (i₀ + 1) = ⊥`. -/
theorem map_eq_zero_of_graded_exact
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (S : ℕ → Submodule R A) (T : ℕ → Submodule R B) (U : ℕ → Submodule R C)
    (hf : Preserves f S T) (hg : Preserves g T U)
    (hT : Monotone T) (hU : Monotone U) (hcomp : ∀ a, g (f a) = 0) (i₀ n : ℕ)
    (hTbot : T (i₀ + 1) = ⊥)
    (hex : ∀ i, i₀ < i → i < n → LinearMap.range (gradedMap f S T hf i) =
      LinearMap.ker (gradedMap g T U hg i)) :
    ∀ j ≤ n, ∀ b ∈ T j, g b ∈ U (i₀ + 1) → g b = 0 := by
  intro j
  induction j with
  | zero =>
    intro _ b hb _
    have hb0 : b ∈ T (i₀ + 1) := hT (Nat.zero_le _) hb
    rw [hTbot, Submodule.mem_bot] at hb0
    rw [hb0, map_zero]
  | succ j ih =>
    intro hj b hb hgb
    by_cases hji : j + 1 ≤ i₀ + 1
    · have hb0 : b ∈ T (i₀ + 1) := hT hji hb
      rw [hTbot, Submodule.mem_bot] at hb0
      rw [hb0, map_zero]
    · obtain ⟨a, -, hrem⟩ := reduction_of_graded_exact f g S T U hf hg j
        (hex j (by omega) (by omega)) b hb (hU (by omega) hgb)
      have hga : g (b - f a) = g b := by rw [map_sub, hcomp, sub_zero]
      rw [← hga]
      exact ih (by omega) (b - f a) hrem (by rw [hga]; exact hgb)

/-- The surviving step `U (i₀ + 1)` maps bijectively onto the actual cokernel
`C ⧸ range g`, provided `T (i₀ + 1) = ⊥`, the filtrations are exhaustive at `n`,
the graded maps of `g` are surjective and the graded complexes are exact at `B`
in every grade `i₀ < i < n`. -/
theorem bijective_cokernel_of_graded
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (S : ℕ → Submodule R A) (T : ℕ → Submodule R B) (U : ℕ → Submodule R C)
    (hf : Preserves f S T) (hg : Preserves g T U)
    (hT : Monotone T) (hU : Monotone U) (hcomp : ∀ a, g (f a) = 0) (i₀ n : ℕ)
    (hTn : T n = ⊤) (hUn : U n = ⊤) (hTbot : T (i₀ + 1) = ⊥)
    (hsurj : ∀ i, i₀ < i → i < n → Function.Surjective (gradedMap g T U hg i))
    (hex : ∀ i, i₀ < i → i < n → LinearMap.range (gradedMap f S T hf i) =
      LinearMap.ker (gradedMap g T U hg i)) :
    Function.Bijective ((LinearMap.range g).mkQ ∘ₗ (U (i₀ + 1)).subtype) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hxr : (x : C) ∈ LinearMap.range g :=
      (Submodule.Quotient.mk_eq_zero (LinearMap.range g)).mp hx
    obtain ⟨b, hb⟩ := hxr
    have hgb := map_eq_zero_of_graded_exact f g S T U hf hg hT hU hcomp i₀ n hTbot hex n
      le_rfl b (by rw [hTn]; trivial) (by rw [hb]; exact x.property)
    exact Subtype.ext (hb.symm.trans hgb)
  · intro q
    obtain ⟨c, rfl⟩ := (LinearMap.range g).mkQ_surjective q
    obtain ⟨b, hb⟩ := exists_sub_mem_of_graded_surjective g T U hg hU i₀ n hsurj n le_rfl c
      (by rw [hUn]; trivial)
    refine ⟨⟨c - g b, hb⟩, ?_⟩
    change (LinearMap.range g).mkQ (c - g b) = (LinearMap.range g).mkQ c
    rw [map_sub, sub_eq_self, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self g b

/-- The linear equivalence of `bijective_cokernel_of_graded`: inclusion of the
surviving step followed by the actual cokernel quotient. -/
def cokernelEquiv
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (S : ℕ → Submodule R A) (T : ℕ → Submodule R B) (U : ℕ → Submodule R C)
    (hf : Preserves f S T) (hg : Preserves g T U)
    (hT : Monotone T) (hU : Monotone U) (hcomp : ∀ a, g (f a) = 0) (i₀ n : ℕ)
    (hTn : T n = ⊤) (hUn : U n = ⊤) (hTbot : T (i₀ + 1) = ⊥)
    (hsurj : ∀ i, i₀ < i → i < n → Function.Surjective (gradedMap g T U hg i))
    (hex : ∀ i, i₀ < i → i < n → LinearMap.range (gradedMap f S T hf i) =
      LinearMap.ker (gradedMap g T U hg i)) :
    U (i₀ + 1) ≃ₗ[R] C ⧸ LinearMap.range g :=
  LinearEquiv.ofBijective _
    (bijective_cokernel_of_graded f g S T U hf hg hT hU hcomp i₀ n hTn hUn hTbot hsurj hex)

@[simp] theorem cokernelEquiv_apply
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (S : ℕ → Submodule R A) (T : ℕ → Submodule R B) (U : ℕ → Submodule R C)
    (hf : Preserves f S T) (hg : Preserves g T U)
    (hT : Monotone T) (hU : Monotone U) (hcomp : ∀ a, g (f a) = 0) (i₀ n : ℕ)
    (hTn : T n = ⊤) (hUn : U n = ⊤) (hTbot : T (i₀ + 1) = ⊥)
    (hsurj : ∀ i, i₀ < i → i < n → Function.Surjective (gradedMap g T U hg i))
    (hex : ∀ i, i₀ < i → i < n → LinearMap.range (gradedMap f S T hf i) =
      LinearMap.ker (gradedMap g T U hg i)) (x : U (i₀ + 1)) :
    cokernelEquiv f g S T U hf hg hT hU hcomp i₀ n hTn hUn hTbot hsurj hex x =
      (LinearMap.range g).mkQ (x : C) := rfl

end Langlands.FiniteFiltered
