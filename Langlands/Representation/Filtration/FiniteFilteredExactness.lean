import Mathlib.LinearAlgebra.Quotient.Basic

/-! Exactness and injectivity lifted from finite associated graded modules. -/

namespace Langlands.FiniteFiltered

universe uR uA uB uC

variable {R : Type uR} [CommRing R]
variable {A : Type uA} [AddCommGroup A] [Module R A]
variable {B : Type uB} [AddCommGroup B] [Module R B]
variable {C : Type uC} [AddCommGroup C] [Module R C]

/-- The lower step regarded as a submodule of the next step. -/
def denominator (S : ℕ → Submodule R A) (i : ℕ) : Submodule R (S (i + 1)) :=
  (S i).comap (S (i + 1)).subtype

/-- The actual adjacent quotient of two filtration steps. -/
abbrev Graded (S : ℕ → Submodule R A) (i : ℕ) :=
  S (i + 1) ⧸ denominator S i

/-- A linear map preserves each filtration step. -/
def Preserves (f : A →ₗ[R] B) (S : ℕ → Submodule R A)
    (T : ℕ → Submodule R B) : Prop :=
  ∀ i x, x ∈ S i → f x ∈ T i

/-- Restrict a filtration-preserving linear map to the next steps. -/
def stepMap (f : A →ₗ[R] B) (S : ℕ → Submodule R A)
    (T : ℕ → Submodule R B) (hf : Preserves f S T) (i : ℕ) :
    S (i + 1) →ₗ[R] T (i + 1) :=
  f.restrict (hf (i + 1))

/-- The induced map of actual adjacent quotients. -/
def gradedMap (f : A →ₗ[R] B) (S : ℕ → Submodule R A)
    (T : ℕ → Submodule R B) (hf : Preserves f S T) (i : ℕ) :
    Graded S i →ₗ[R] Graded T i :=
  (denominator S i).mapQ (denominator T i) (stepMap f S T hf i)
    (fun x hx => hf i x hx)

@[simp] theorem gradedMap_mk (f : A →ₗ[R] B) (S : ℕ → Submodule R A)
    (T : ℕ → Submodule R B) (hf : Preserves f S T) (i : ℕ) (a : S (i + 1)) :
    gradedMap f S T hf i ((denominator S i).mkQ a) =
      (denominator T i).mkQ (stepMap f S T hf i a) := rfl

/-- Exactness in one grade lifts a cycle to a boundary modulo the lower step. -/
theorem reduction_of_graded_exact
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (S : ℕ → Submodule R A) (T : ℕ → Submodule R B) (U : ℕ → Submodule R C)
    (hf : Preserves f S T) (hg : Preserves g T U) (i : ℕ)
    (hex : LinearMap.range (gradedMap f S T hf i) =
      LinearMap.ker (gradedMap g T U hg i))
    (b : B) (hb : b ∈ T (i + 1)) (hgb : g b ∈ U i) :
    ∃ a ∈ S (i + 1), b - f a ∈ T i := by
  let bT : T (i + 1) := ⟨b, hb⟩
  have hcycle : (denominator T i).mkQ bT ∈
      LinearMap.ker (gradedMap g T U hg i) := by
    rw [LinearMap.mem_ker, gradedMap_mk]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hgb
  rw [← hex] at hcycle
  obtain ⟨qa, hqa⟩ := hcycle
  obtain ⟨a, rfl⟩ := (denominator S i).mkQ_surjective qa
  refine ⟨a, a.property, ?_⟩
  have hzero : (denominator T i).mkQ (bT - stepMap f S T hf i a) = 0 := by
    rw [map_sub, ← gradedMap_mk, hqa, sub_self]
  exact (Submodule.Quotient.mk_eq_zero (denominator T i)).mp hzero

/-- Exact associated graded maps imply exactness on any finite upper step. -/
theorem lift_cycle_by_induction
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (S : ℕ → Submodule R A) (T : ℕ → Submodule R B) (U : ℕ → Submodule R C)
    (hf : Preserves f S T) (hg : Preserves g T U)
    (hS : Monotone S) (hT0 : T 0 = ⊥) (hcomp : ∀ a, g (f a) = 0)
    (n : ℕ)
    (hex : ∀ i < n, LinearMap.range (gradedMap f S T hf i) =
      LinearMap.ker (gradedMap g T U hg i)) :
    ∀ i ≤ n, ∀ b ∈ T i, g b = 0 → ∃ a ∈ S i, f a = b := by
  intro i
  induction i with
  | zero =>
    intro _ b hb _
    have hb0 : b = 0 := by simpa [hT0] using hb
    exact ⟨0, (S 0).zero_mem, by simp [hb0]⟩
  | succ i ih =>
    intro hin b hb hgb
    obtain ⟨a, ha, hrem⟩ := reduction_of_graded_exact f g S T U hf hg i
      (hex i (by omega)) b hb (by rw [hgb]; exact (U i).zero_mem)
    have hz : g (b - f a) = 0 := by rw [map_sub, hgb, hcomp, sub_self]
    obtain ⟨a', ha', hfa'⟩ := ih (by omega) (b - f a) hrem hz
    refine ⟨a + a', (S (i + 1)).add_mem ha (hS (Nat.le_succ i) ha'), ?_⟩
    rw [map_add, hfa', add_sub_cancel]

/-- Finite graded exactness gives equality of the actual range and kernel. -/
theorem range_eq_ker_of_graded_exact
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (S : ℕ → Submodule R A) (T : ℕ → Submodule R B) (U : ℕ → Submodule R C)
    (hf : Preserves f S T) (hg : Preserves g T U)
    (hS : Monotone S) (hT0 : T 0 = ⊥) (hcomp : ∀ a, g (f a) = 0)
    (n : ℕ) (hTn : T n = ⊤)
    (hex : ∀ i < n, LinearMap.range (gradedMap f S T hf i) =
      LinearMap.ker (gradedMap g T U hg i)) :
    LinearMap.range f = LinearMap.ker g := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    exact hcomp a
  · intro hb
    obtain ⟨a, _, ha⟩ := lift_cycle_by_induction f g S T U hf hg hS hT0 hcomp n hex
      n (Nat.le_refl n) b (by rw [hTn]; trivial) hb
    exact ⟨a, ha⟩

/-- Graded injectivity pushes a zero vector into the preceding step. -/
theorem lower_step_of_graded_injective
    (f : A →ₗ[R] B) (S : ℕ → Submodule R A) (T : ℕ → Submodule R B)
    (hf : Preserves f S T) (i : ℕ)
    (hinj : Function.Injective (gradedMap f S T hf i))
    (a : A) (ha : a ∈ S (i + 1)) (hfa : f a = 0) : a ∈ S i := by
  have hq : gradedMap f S T hf i ((denominator S i).mkQ ⟨a, ha⟩) = 0 := by
    rw [gradedMap_mk]
    have hz : stepMap f S T hf i ⟨a, ha⟩ = 0 := Subtype.ext hfa
    rw [hz, map_zero]
  have hqa := hinj (hq.trans (map_zero _).symm)
  exact (Submodule.Quotient.mk_eq_zero (denominator S i)).mp hqa

/-- Finite graded injectivity gives injectivity of the actual map. -/
theorem injective_of_graded_injective
    (f : A →ₗ[R] B) (S : ℕ → Submodule R A) (T : ℕ → Submodule R B)
    (hf : Preserves f S T) (hS0 : S 0 = ⊥)
    (n : ℕ) (hSn : S n = ⊤)
    (hinj : ∀ i < n, Function.Injective (gradedMap f S T hf i)) :
    Function.Injective f := by
  have hzero : ∀ i ≤ n, ∀ a ∈ S i, f a = 0 → a = 0 := by
    intro i
    induction i with
    | zero =>
      intro _ a ha _
      simpa [hS0] using ha
    | succ i ih =>
      intro hin a ha hfa
      exact ih (by omega) a
        (lower_step_of_graded_injective f S T hf i (hinj i (by omega)) a ha hfa) hfa
  intro a b hab
  apply sub_eq_zero.mp
  apply hzero n (Nat.le_refl n) (a - b) (by rw [hSn]; trivial)
  rw [map_sub, hab, sub_self]

end Langlands.FiniteFiltered
