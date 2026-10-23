import Langlands.Representation.Hecke.TestFunction
import Mathlib.LinearAlgebra.Dual.Defs

/-! # Algebraic distributions and transport by homeomorphisms -/

noncomputable section

namespace Langlands.HarmonicAnalysis

universe uX uY uZ uG

/-- Algebraic distributions on the actual Schwartz--Bruhat test-function space. -/
abbrev Distribution (X : Type uX) [TopologicalSpace X] :=
  Module.Dual ℂ (SchwartzBruhat X)

namespace Distribution

variable {X : Type uX} {Y : Type uY} {Z : Type uZ}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Pushforward: `(e_* D)(f) = D(f ∘ e)`, with no measure factor. -/
def pushforward (e : X ≃ₜ Y) : Distribution X ≃ₗ[ℂ] Distribution Y where
  toFun D := D.comp (Hecke.TestFunction.pullback e).toLinearMap
  invFun D := D.comp (Hecke.TestFunction.pullback e.symm).toLinearMap
  left_inv D := by
    ext f
    change D (Hecke.TestFunction.pullback e
      (Hecke.TestFunction.pullback e.symm f)) = D f
    congr 1
    ext x
    simp only [Hecke.TestFunction.pullback_apply, e.symm_apply_apply]
  right_inv D := by
    ext f
    change D (Hecke.TestFunction.pullback e.symm
      (Hecke.TestFunction.pullback e f)) = D f
    congr 1
    ext x
    simp only [Hecke.TestFunction.pullback_apply, e.apply_symm_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem pushforward_apply (e : X ≃ₜ Y) (D : Distribution X) (f : SchwartzBruhat Y) :
    pushforward e D f = D (Hecke.TestFunction.pullback e f) := rfl

@[simp]
theorem pushforward_refl (D : Distribution X) :
    pushforward (Homeomorph.refl X) D = D := by
  ext f
  change D (Hecke.TestFunction.pullback (Homeomorph.refl X) f) = D f
  congr 1

/-- Composition is covariant for distributions. -/
theorem pushforward_trans (e : X ≃ₜ Y) (h : Y ≃ₜ Z) (D : Distribution X) :
    pushforward (e.trans h) D = pushforward h (pushforward e D) := by
  ext f
  change D (Hecke.TestFunction.pullback (e.trans h) f) =
    D (Hecke.TestFunction.pullback e (Hecke.TestFunction.pullback h f))
  congr 1

@[simp]
theorem pushforward_symm (e : X ≃ₜ Y) :
    (pushforward e).symm = pushforward e.symm := rfl

@[simp]
theorem pushforward_symm_apply (e : X ≃ₜ Y) (D : Distribution X) :
    pushforward e.symm (pushforward e D) = D :=
  (pushforward e).symm_apply_apply D

@[simp]
theorem pushforward_apply_symm (e : X ≃ₜ Y) (D : Distribution Y) :
    pushforward e (pushforward e.symm D) = D :=
  (pushforward e).apply_symm_apply D

section Group

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The actual inner automorphism, viewed as a homeomorphism. -/
def conjugationHomeomorph (a : G) : G ≃ₜ G :=
  (Homeomorph.mulLeft a).trans (Homeomorph.mulRight a⁻¹)

@[simp]
theorem conjugationHomeomorph_apply (a x : G) :
    conjugationHomeomorph a x = a * x * a⁻¹ := rfl

/-- Invariance under every actual inner automorphism. -/
def IsConjugationInvariant (D : Distribution G) : Prop :=
  ∀ a : G, pushforward (conjugationHomeomorph a) D = D

theorem isConjugationInvariant_iff (D : Distribution G) :
    IsConjugationInvariant D ↔
      ∀ (a : G) (f : SchwartzBruhat G),
        D (Hecke.TestFunction.pullback (conjugationHomeomorph a) f) = D f := by
  constructor
  · intro h a f
    exact congrArg (fun E : Distribution G => E f) (h a)
  · intro h a
    ext f
    exact h a f

end Group
end Distribution
end Langlands.HarmonicAnalysis
