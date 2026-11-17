import Langlands.AlgebraicGeometry.AdicAffinePoints
import Langlands.GroupScheme.HomScheme.ConjugationMap

/-! # Compatible homomorphisms over adic thickenings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.AdicAffinePoints

namespace Langlands.GroupScheme.HomScheme.Adic

variable {A : Type u} [CommRing A] (I : Ideal A)
    (H G : GroupScheme (Spec (CommRingCat.of A)))

/-- Actual group-scheme homomorphisms on the adic quotients, compatible under pullback. -/
structure System where
  hom (n : ℕ) : RelativeHom H G (Over.mk (quotientMap I n))
  compatible (n : ℕ) : evaluate (transitionOver I n) (hom (n + 1)) = hom n

namespace System

variable {I H G}

@[ext]
theorem ext {f g : System I H G} (h : ∀ n, f.hom n = g.hom n) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have : f = g := funext h
      subst g
      rfl

variable (I H G)

/-- Restrict a global group-scheme homomorphism to every adic thickening. -/
def restrict (f : H ⟶ G) : System I H G where
  hom n := (baseChange (quotientMap I n)).map f
  compatible n := evaluate_baseChange (transitionOver I n) f

@[simp]
theorem restrict_hom (f : H ⟶ G) (n : ℕ) :
    (restrict I H G f).hom n = (baseChange (quotientMap I n)).map f := rfl

/-- Injectivity of restriction is exactly equality detection on all quotient powers. -/
theorem restrict_injective_iff :
    Function.Injective (restrict I H G) ↔
      ∀ f g : H ⟶ G,
        (∀ n : ℕ, (baseChange (quotientMap I n)).map f =
          (baseChange (quotientMap I n)).map g) → f = g := by
  constructor
  · intro h f g hfg
    exact h (ext hfg)
  · intro h f g hfg
    exact h f g (fun n ↦ congrArg (fun s : System I H G ↦ s.hom n) hfg)

/-- Surjective successive restriction maps extend any first homomorphism to a compatible
formal family. -/
theorem exists_system_of_step_surjective
    (hstep : ∀ n : ℕ,
      Function.Surjective (evaluate (H := H) (G := G) (transitionOver I n)))
    (f₀ : RelativeHom H G (Over.mk (quotientMap I 0))) :
    ∃ f : System I H G, f.hom 0 = f₀ := by
  let f : ∀ n : ℕ, RelativeHom H G (Over.mk (quotientMap I n)) :=
    Nat.rec (motive := fun n ↦ RelativeHom H G (Over.mk (quotientMap I n))) f₀
      (fun n f ↦ Classical.choose (hstep n f))
  have hf : ∀ n : ℕ, evaluate (transitionOver I n) (f (n + 1)) = f n :=
    fun n ↦ Classical.choose_spec (hstep n (f n))
  exact ⟨⟨f, hf⟩, rfl⟩

/-- Stepwise lifting and effectivity of formal homomorphisms imply lifting from the first
quotient. -/
theorem exists_lift_of_step_surjective
    (heff : Function.Surjective (restrict I H G))
    (hstep : ∀ n : ℕ,
      Function.Surjective (evaluate (H := H) (G := G) (transitionOver I n)))
    (f₀ : RelativeHom H G (Over.mk (quotientMap I 0))) :
    ∃ f : H ⟶ G, (baseChange (quotientMap I 0)).map f = f₀ := by
  obtain ⟨s, hs⟩ := exists_system_of_step_surjective I H G hstep f₀
  obtain ⟨f, hf⟩ := heff s
  exact ⟨f, (congrArg (fun s : System I H G ↦ s.hom 0) hf).trans hs⟩

end System

end Langlands.GroupScheme.HomScheme.Adic
