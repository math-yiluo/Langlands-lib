import Langlands.Geometry.Analytic.StrictTestDomain.SpectralDisplacement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.Definitions
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! # Uniform control of algebraic expressions by finite spectral tests -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

open BanachSpectrum

variable {K : Type u} {R : Type v} {A : Type w} {ι : Type z}
  [NormedField K] [IsUltrametricDist K]
  [NormedCommRing R] [NormedAlgebra K R] [NormedCommRing A] [NormedAlgebra K A]

/-- An expression has spectral control at a reference coefficient map and tuple if
finitely many coefficient tests and tests on the arguments suffice for every
requested bound, uniformly after pulling back the reference data. -/
def HasSpectralControlAt (a : BoundedAlgHom K R A) (x : ι → A) (value : A)
    (F : (C : PresentedAffinoidAlgebra K) → BoundedAlgHom K A C → BoundedAlgHom K R C →
      (ι → C) → C) : Prop :=
  ∀ ε > 0, ∃ (D : Finset R) (δ : ℝ), 0 < δ ∧
    ∀ (C : PresentedAffinoidAlgebra K) (l : BoundedAlgHom K A C)
      (b : BoundedAlgHom K R C) (y : ι → C),
      (∀ t ∈ D, SpectralBound (b t - l (a t)) δ) →
      (∀ i, SpectralBound (y i - l (x i)) δ) →
        SpectralBound (F C l b y - l value) ε

namespace HasSpectralControlAt

variable {a : BoundedAlgHom K R A} {x : ι → A} {vF vG : A}
  {F G : (C : PresentedAffinoidAlgebra K) → BoundedAlgHom K A C → BoundedAlgHom K R C →
    (ι → C) → C}

theorem const (c : A) : HasSpectralControlAt a x c (fun _ l _ _ => l c) := by
  intro ε hε
  refine ⟨∅, ε, hε, fun _ _ _ _ _ _ => ?_⟩
  rw [sub_self]
  exact spectralBound_zero hε.le

theorem coeff (t : R) : HasSpectralControlAt a x (a t) (fun _ _ b _ => b t) :=
  fun ε hε => ⟨{t}, ε, hε, fun _ _ _ _ h _ => h t (Finset.mem_singleton_self t)⟩

theorem argument (i : ι) : HasSpectralControlAt a x (x i) (fun _ _ _ y => y i) :=
  fun ε hε => ⟨∅, ε, hε, fun _ _ _ _ _ hy => hy i⟩

private theorem joint (hF : HasSpectralControlAt a x vF F) (hG : HasSpectralControlAt a x vG G)
    {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε') :
    ∃ (D : Finset R) (δ : ℝ), 0 < δ ∧
      ∀ (C : PresentedAffinoidAlgebra K) (l : BoundedAlgHom K A C)
        (b : BoundedAlgHom K R C) (y : ι → C),
        (∀ t ∈ D, SpectralBound (b t - l (a t)) δ) →
        (∀ i, SpectralBound (y i - l (x i)) δ) →
          SpectralBound (F C l b y - l vF) ε ∧ SpectralBound (G C l b y - l vG) ε' := by
  classical
  obtain ⟨D, δ, hδ, hhF⟩ := hF ε hε
  obtain ⟨D', δ', hδ', hhG⟩ := hG ε' hε'
  refine ⟨D ∪ D', min δ δ', lt_min hδ hδ', fun C l b y h hy => ⟨?_, ?_⟩⟩
  · exact hhF C l b y (fun t ht => (h t (Finset.mem_union_left _ ht)).mono (min_le_left _ _))
      (fun i => (hy i).mono (min_le_left _ _))
  · exact hhG C l b y (fun t ht => (h t (Finset.mem_union_right _ ht)).mono (min_le_right _ _))
      (fun i => (hy i).mono (min_le_right _ _))

theorem add (hF : HasSpectralControlAt a x vF F) (hG : HasSpectralControlAt a x vG G) :
    HasSpectralControlAt a x (vF + vG) (fun C l b y => F C l b y + G C l b y) := by
  intro ε hε
  obtain ⟨D, δ, hδ, h⟩ := hF.joint hG hε hε
  refine ⟨D, δ, hδ, fun C l b y hb hy => ?_⟩
  obtain ⟨hf, hg⟩ := h C l b y hb hy
  change SpectralBound (F C l b y + G C l b y - l.toAlgHom (vF + vG)) ε
  rw [map_add, show F C l b y + G C l b y - (l vF + l vG) =
    (F C l b y - l vF) + (G C l b y - l vG) by abel]
  exact hf.add (K := K) hg

theorem neg (hF : HasSpectralControlAt a x vF F) :
    HasSpectralControlAt a x (-vF) (fun C l b y => -F C l b y) := by
  intro ε hε
  obtain ⟨D, δ, hδ, h⟩ := hF ε hε
  refine ⟨D, δ, hδ, fun C l b y hb hy => ?_⟩
  change SpectralBound (-F C l b y - l.toAlgHom (-vF)) ε
  rw [map_neg, show -F C l b y - -l vF = -(F C l b y - l vF) by abel]
  exact (h C l b y hb hy).neg

theorem sub (hF : HasSpectralControlAt a x vF F) (hG : HasSpectralControlAt a x vG G) :
    HasSpectralControlAt a x (vF - vG) (fun C l b y => F C l b y - G C l b y) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

theorem mul (hF : HasSpectralControlAt a x vF F) (hG : HasSpectralControlAt a x vG G) :
    HasSpectralControlAt a x (vF * vG) (fun C l b y => F C l b y * G C l b y) := by
  intro ε hε
  let M := max 1 (max ‖vF‖ ‖vG‖)
  have hM : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
  let η := min 1 (ε / M)
  have hη : 0 < η := lt_min zero_lt_one (div_pos hε hM)
  have hηM : η ≤ M := (min_le_left _ _).trans (le_max_left _ _)
  have hMη : M * η ≤ ε := by
    rw [mul_comm, ← le_div_iff₀ hM]
    exact min_le_right _ _
  obtain ⟨D, δ, hδ, h⟩ := hF.joint hG hη hη
  refine ⟨D, δ, hδ, fun C l b y hb hy p => ?_⟩
  let p₀ := BanachSpectrum.comap l.toBoundedRingHom p
  have h₁ : p (l vF) ≤ M := (p₀.le_norm _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have h₂ : p (l vG) ≤ M := (p₀.le_norm _).trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨hf, hg⟩ := h C l b y hb hy
  have h₃ : p (F C l b y) ≤ M := by
    have hsum := p.isNonarchimedean (K := K) (F C l b y - l vF) (l vF)
    rw [sub_add_cancel] at hsum
    exact hsum.trans (max_le ((hf p).trans hηM) h₁)
  change p (F C l b y * G C l b y - l.toAlgHom (vF * vG)) ≤ ε
  rw [map_mul, show F C l b y * G C l b y - l vF * l vG =
    F C l b y * (G C l b y - l vG) + (F C l b y - l vF) * l vG by ring]
  apply (p.isNonarchimedean (K := K) _ _).trans
  apply max_le
  · rw [map_mul]
    exact (mul_le_mul h₃ (hg p) (apply_nonneg _ _) hM.le).trans hMη
  · rw [map_mul]
    exact (mul_le_mul (hf p) h₂ (apply_nonneg _ _) hη.le).trans
      ((mul_comm η M).le.trans hMη)

theorem pow (hF : HasSpectralControlAt a x vF F) (n : ℕ) :
    HasSpectralControlAt a x (vF ^ n) (fun C l b y => F C l b y ^ n) := by
  induction n with
  | zero => simpa only [pow_zero, show ∀ (C : PresentedAffinoidAlgebra K)
      (l : BoundedAlgHom K A C), l (1 : A) = 1 from fun _ l => l.toAlgHom.map_one]
      using (const (a := a) (x := x) (1 : A))
  | succ n ih => simpa only [pow_succ] using ih.mul hF

/-- Evaluating a polynomial uses finitely many coefficient tests and control of its argument. -/
theorem eval₂ (P : Polynomial R) (hF : HasSpectralControlAt a x vF F) :
    HasSpectralControlAt a x (P.eval₂ a.toAlgHom.toRingHom vF)
      (fun C l b y => P.eval₂ b.toAlgHom.toRingHom (F C l b y)) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval₂_add] using hp.add hq
  | monomial n t =>
    simp only [Polynomial.eval₂_monomial]
    change HasSpectralControlAt a x (a t * vF ^ n) (fun C l b y => b t * F C l b y ^ n)
    exact (coeff t).mul (hF.pow n)

/-- Finitely many estimates can be met with the same finite coefficient tests and tolerance. -/
theorem finite {κ : Type*} (I : Finset κ) (ε : κ → ℝ) (V : κ → A)
    (F : κ → (C : PresentedAffinoidAlgebra K) → BoundedAlgHom K A C → BoundedAlgHom K R C →
      (ι → C) → C)
    (hε : ∀ i ∈ I, 0 < ε i) (hF : ∀ i ∈ I, HasSpectralControlAt a x (V i) (F i)) :
    ∃ (D : Finset R) (δ : ℝ), 0 < δ ∧
      ∀ (C : PresentedAffinoidAlgebra K) (l : BoundedAlgHom K A C)
        (b : BoundedAlgHom K R C) (y : ι → C),
        (∀ t ∈ D, SpectralBound (b t - l (a t)) δ) →
        (∀ i, SpectralBound (y i - l (x i)) δ) →
        ∀ i ∈ I, SpectralBound (F i C l b y - l (V i)) (ε i) := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨∅, 1, zero_lt_one, fun _ _ _ _ _ _ _ h => (Finset.notMem_empty _ h).elim⟩
  | insert i I _ ih =>
    obtain ⟨D, δ, hδ, h⟩ := ih (fun j hj => hε j (Finset.mem_insert_of_mem hj))
      (fun j hj => hF j (Finset.mem_insert_of_mem hj))
    have hi' := Finset.mem_insert_self i I
    obtain ⟨D', δ', hδ', h'⟩ := hF i hi' (ε i) (hε i hi')
    refine ⟨D ∪ D', min δ δ', lt_min hδ hδ', fun C l b y hb hy j hj => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact h' C l b y (fun t ht => (hb t (Finset.mem_union_right _ ht)).mono (min_le_right _ _))
        (fun k => (hy k).mono (min_le_right _ _))
    · exact h C l b y (fun t ht => (hb t (Finset.mem_union_left _ ht)).mono (min_le_left _ _))
        (fun k => (hy k).mono (min_le_left _ _)) j hj

end HasSpectralControlAt

end Langlands.Analytic
