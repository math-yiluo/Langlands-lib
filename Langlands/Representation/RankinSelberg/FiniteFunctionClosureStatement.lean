import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Elementary closure properties of continuous translation-finite functions. -/

namespace Langlands.RankinSelberg

universe uG uH

/-- Continuous complex functions with finite-dimensional left-translation span
are closed under pointwise products and continuous monoid-homomorphism pullback.
Continuous complex-valued multiplicative characters are such functions. -/
def FiniteFunctionClosureStatement (G : Type uG) (H : Type uH)
    [Monoid G] [Monoid H] [TopologicalSpace G] [TopologicalSpace H] : Prop :=
  let finiteG := fun f : G → ℂ => Continuous f ∧
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun b : G => fun a : G => f (b * a)))
  let finiteH := fun f : H → ℂ => Continuous f ∧
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun b : H => fun a : H => f (b * a)))
  (∀ f g : G → ℂ, finiteG f → finiteG g → finiteG (fun a => f a * g a)) ∧
    (∀ h : H →* G, Continuous h → ∀ f : G → ℂ,
      finiteG f → finiteH (fun a => f (h a))) ∧
    (∀ χ : G →* ℂ, Continuous χ → finiteG χ)

end Langlands.RankinSelberg
