import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-! # A fibrewise criterion for equalizers of smooth algebras -/

universe u

open scoped TensorProduct

namespace Langlands.Algebra

/-- If the equalizer of two maps between smooth algebras consists of scalars
on every residue-field fibre, and the source is faithfully flat, then the
equalizer over the base ring consists of scalars. -/
def SmoothEqualizerFibreCriterion : Prop :=
  ∀ (A C₀ C₁ : Type u) [CommRing A] [CommRing C₀] [CommRing C₁]
    [Algebra A C₀] [Algebra A C₁] (δ₁ δ₂ : C₀ →ₐ[A] C₁),
    _root_.Algebra.Smooth A C₀ →
    _root_.Algebra.Smooth A C₁ →
    Module.FaithfullyFlat A C₀ →
    (∀ (P : Ideal A) [P.IsPrime] (x : P.ResidueField ⊗[A] C₀),
      _root_.Algebra.TensorProduct.map (AlgHom.id A P.ResidueField) δ₁ x =
        _root_.Algebra.TensorProduct.map (AlgHom.id A P.ResidueField) δ₂ x →
      x ∈ Set.range (algebraMap P.ResidueField (P.ResidueField ⊗[A] C₀))) →
    ∀ c : C₀, δ₁ c = δ₂ c → c ∈ Set.range (algebraMap A C₀)

end Langlands.Algebra
