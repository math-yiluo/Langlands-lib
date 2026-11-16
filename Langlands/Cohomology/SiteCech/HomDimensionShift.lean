import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Dimension shifting in coefficient Hom complexes -/

noncomputable section

namespace Langlands.Cohomology.SiteCech

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {D : Type u} [Category.{v} D] [Abelian D]
variable (R : Type w) [Ring R] [Linear R D]
variable (P : ChainComplex D ℕ) (S : ShortComplex D)

/-- Exactness of a coefficient short complex shifts Hom-complex exactness by
one, provided the cocycle in the quotient coefficient has a lift. -/
theorem exactAt_linearYonedaObj_quotient (hS : S.Exact) [Mono S.f] (n : ℕ)
    (hLift : ∀ x : P.X (n + 1) ⟶ S.X₃, ∃ y : P.X (n + 1) ⟶ S.X₂, y ≫ S.g = x)
    (hF : (P.linearYonedaObj R S.X₁).ExactAt (n + 2))
    (hI : (P.linearYonedaObj R S.X₂).ExactAt (n + 1)) :
    (P.linearYonedaObj R S.X₃).ExactAt (n + 1) := by
  apply (HomologicalComplex.exactAt_iff'
    (P.linearYonedaObj R S.X₃) n (n + 1) (n + 2) (by simp) (by simp)).2
  apply (ShortComplex.moduleCat_exact_iff _).2
  intro x hx
  change P.X (n + 1) ⟶ S.X₃ at x
  change P.d (n + 2) (n + 1) ≫ x = 0 at hx
  obtain ⟨y, hy⟩ := hLift x
  let c := hS.lift (P.d (n + 2) (n + 1) ≫ y) (by
    rw [Category.assoc, hy, hx])
  have hc : c ≫ S.f = P.d (n + 2) (n + 1) ≫ y := hS.lift_f _ _
  have hdc : P.d (n + 3) (n + 2) ≫ c = 0 := by
    apply (cancel_mono S.f).1
    rw [Category.assoc, hc, ← Category.assoc, P.d_comp_d, zero_comp, zero_comp]
  have hF' := (HomologicalComplex.exactAt_iff'
    (P.linearYonedaObj R S.X₁) (n + 1) (n + 2) (n + 3) (by simp) (by simp)).1 hF
  obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff _).1 hF' c hdc
  change P.X (n + 1) ⟶ S.X₁ at b
  change P.d (n + 2) (n + 1) ≫ b = c at hb
  have hdy : P.d (n + 2) (n + 1) ≫ (y - b ≫ S.f) = 0 := by
    rw [Preadditive.comp_sub, ← Category.assoc, hb, hc, sub_self]
  have hI' := (HomologicalComplex.exactAt_iff'
    (P.linearYonedaObj R S.X₂) n (n + 1) (n + 2) (by simp) (by simp)).1 hI
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 hI' (y - b ≫ S.f) hdy
  change P.X n ⟶ S.X₂ at z
  change P.d (n + 1) n ≫ z = y - b ≫ S.f at hz
  refine ⟨z ≫ S.g, ?_⟩
  change P.d (n + 1) n ≫ z ≫ S.g = x
  rw [← Category.assoc, hz, Preadditive.sub_comp, Category.assoc, S.zero,
    comp_zero, sub_zero, hy]

/-- Positive Hom exactness passes to the quotient coefficient when both
earlier coefficients are positively exact and quotient maps lift in every
positive chain degree. -/
theorem exactAt_linearYonedaObj_quotient_all (hS : S.Exact) [Mono S.f]
    (hLift : ∀ n : ℕ, ∀ x : P.X (n + 1) ⟶ S.X₃,
      ∃ y : P.X (n + 1) ⟶ S.X₂, y ≫ S.g = x)
    (hF : ∀ n : ℕ, (P.linearYonedaObj R S.X₁).ExactAt (n + 1))
    (hI : ∀ n : ℕ, (P.linearYonedaObj R S.X₂).ExactAt (n + 1)) :
    ∀ n : ℕ, (P.linearYonedaObj R S.X₃).ExactAt (n + 1) :=
  fun n => exactAt_linearYonedaObj_quotient R P S hS n (hLift n) (hF (n + 1)) (hI n)

/-- A chosen primitive of a quotient-coefficient cocycle, under the explicit
lifting and adjacent coefficient-exactness hypotheses. -/
def quotientCocycleBoundary (hS : S.Exact) [Mono S.f] (n : ℕ)
    (hLift : ∀ x : P.X (n + 1) ⟶ S.X₃, ∃ y : P.X (n + 1) ⟶ S.X₂, y ≫ S.g = x)
    (hF : (P.linearYonedaObj R S.X₁).ExactAt (n + 2))
    (hI : (P.linearYonedaObj R S.X₂).ExactAt (n + 1))
    (x : P.X (n + 1) ⟶ S.X₃) (hx : P.d (n + 2) (n + 1) ≫ x = 0) :
    {z : P.X n ⟶ S.X₃ // P.d (n + 1) n ≫ z = x} := by
  have h := (HomologicalComplex.exactAt_iff'
    (P.linearYonedaObj R S.X₃) n (n + 1) (n + 2) (by simp) (by simp)).1
      (exactAt_linearYonedaObj_quotient R P S hS n hLift hF hI)
  have he : ∃ z : P.X n ⟶ S.X₃, P.d (n + 1) n ≫ z = x :=
    (ShortComplex.moduleCat_exact_iff _).1 h x hx
  exact ⟨Classical.choose he, Classical.choose_spec he⟩

end Langlands.Cohomology.SiteCech
