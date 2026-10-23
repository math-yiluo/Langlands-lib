import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group

/-! # Inner conjugation on ordinary degree-two cohomology -/

noncomputable section

namespace Langlands.OrdinaryCohomology

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

/-- Conjugation by `a`, used contravariantly on cochains. -/
def innerConjugation (a : G) : G →* G where
  toFun g := a * g * a⁻¹
  map_one' := by simp
  map_mul' g h := by simp [mul_assoc]

/-- The inverse action on coefficients intertwines the conjugated action. -/
def innerConjugationCoefficient (a : G) : Rep.res (innerConjugation a) A ⟶ A :=
  Rep.ofHom
    { toLinearMap := A.ρ a⁻¹
      isIntertwining' g := by
        ext x
        change A.ρ a⁻¹ (A.ρ (a * g * a⁻¹) x) = A.ρ g (A.ρ a⁻¹ x)
        simp only [← Module.End.mul_apply, ← map_mul]
        congr 2
        group }

/-- The actual ordinary cohomology map for inner conjugation and inverse coefficient action. -/
abbrev innerConjugationMap (a : G) (n : ℕ) :
    groupCohomology A n ⟶ groupCohomology A n :=
  groupCohomology.map (innerConjugation a) (innerConjugationCoefficient A a) n

/-- An explicit one-cochain measuring inner conjugation of a two-cocycle. -/
def innerConjugationBoundary (a : G) (f : groupCohomology.cocycles₂ A) : G → A :=
  fun g => A.ρ a⁻¹ (f (a * g * a⁻¹, a) - f (a, g))

/-- The conjugated two-cocycle differs from the original by this coboundary. -/
theorem innerConjugationBoundary_d (a : G) (f : groupCohomology.cocycles₂ A) :
    groupCohomology.d₁₂ A (innerConjugationBoundary A a f) =
      (groupCohomology.mapCocycles₂ (innerConjugation a)
        (innerConjugationCoefficient A a) f : G × G → A) - f := by
  ext ⟨g, h⟩
  change A.ρ g (A.ρ a⁻¹ (f (a * h * a⁻¹, a) - f (a, h))) -
      A.ρ a⁻¹ (f (a * (g * h) * a⁻¹, a) - f (a, g * h)) +
      A.ρ a⁻¹ (f (a * g * a⁻¹, a) - f (a, g)) =
    A.ρ a⁻¹ (f (a * g * a⁻¹, a * h * a⁻¹)) - f (g, h)
  have hc (x y : G) (z : A) : A.ρ x (A.ρ y z) = A.ρ (x*y) z := by
    rw [map_mul, Module.End.mul_apply]
  have hg : g * a⁻¹ = a⁻¹ * (a * g * a⁻¹) := by group
  have hi : f (g,h) = A.ρ a⁻¹ (A.ρ a (f (g,h))) := by simp [hc]
  rw [hc, hg, ← hc, hi, ← map_sub (A.ρ a⁻¹), ← map_add (A.ρ a⁻¹),
    ← map_sub (A.ρ a⁻¹)]
  congr 1
  have h₁ := (groupCohomology.mem_cocycles₂_def f).mp f.property a g h
  have h₂ := (groupCohomology.mem_cocycles₂_def f).mp f.property (a*g*a⁻¹) a h
  have h₃ := (groupCohomology.mem_cocycles₂_def f).mp f.property
    (a*g*a⁻¹) (a*h*a⁻¹) a
  have e₁ : a*g*a⁻¹*a = a*g := by group
  have e₂ : a*h*a⁻¹*a = a*h := by group
  have e₃ : a*g*a⁻¹*(a*h*a⁻¹) = a*(g*h)*a⁻¹ := by group
  rw [e₁] at h₂
  rw [e₂, e₃] at h₃
  simp only [map_sub]
  calc
    _ = (f (a*g*a⁻¹, a*h*a⁻¹) - A.ρ a (f (g,h))) +
        (A.ρ (a*g*a⁻¹) (f (a*h*a⁻¹,a)) - f (a*(g*h)*a⁻¹,a) +
          f (a*g*a⁻¹,a*h) - f (a*g*a⁻¹,a*h*a⁻¹)) -
        (A.ρ (a*g*a⁻¹) (f (a,h)) - f (a*g,h) + f (a*g*a⁻¹,a*h) - f (a*g*a⁻¹,a)) +
        (A.ρ a (f (g,h)) - f (a*g,h) + f (a,g*h) - f (a,g)) := by abel
    _ = _ := by rw [h₃, h₂, h₁]; abel

/-- Inner conjugation with the inverse coefficient action is the identity on actual ordinary H². -/
theorem innerConjugationMap_two (a : G) : innerConjugationMap A a 2 = 𝟙 _ := by
  rw [← cancel_epi (groupCohomology.H2π A), Category.comp_id,
    groupCohomology.H2π_comp_map]
  ext f
  change groupCohomology.H2π A
    (groupCohomology.mapCocycles₂ (innerConjugation a)
      (innerConjugationCoefficient A a) f) = groupCohomology.H2π A f
  apply (groupCohomology.H2π_eq_iff _ _).mpr
  exact ⟨innerConjugationBoundary A a f, innerConjugationBoundary_d A a f⟩

/-- Evaluation form of degree-two triviality. -/
theorem innerConjugationMap_two_apply (a : G) (x : groupCohomology A 2) :
    innerConjugationMap A a 2 x = x := by
  rw [innerConjugationMap_two]
  rfl

end Langlands.OrdinaryCohomology
