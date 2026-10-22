import Langlands.CategoryTheory.Picard.TensorEquivalenceStatement

universe v u

open CategoryTheory MonoidalCategory

namespace Langlands.CategoryTheory.Picard

/-- The categorical characterization of invertibility by a tensor inverse. -/
theorem tensorInvertibilityEquivalence
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] :
    TensorInvertibilityEquivalenceStatement C := by
  intro L
  constructor
  · rintro ⟨N, ⟨e⟩⟩
    let e' : N ⊗ L ≅ 𝟙_ C := (β_ N L) ≪≫ e
    let η : 𝟭 C ≅ tensorLeft L ⋙ tensorLeft N :=
      (leftUnitorNatIso C).symm ≪≫
        (tensoringLeft C).mapIso e'.symm ≪≫ tensorLeftTensor N L
    let ε : tensorLeft N ⋙ tensorLeft L ≅ 𝟭 C :=
      (tensorLeftTensor L N).symm ≪≫
        (tensoringLeft C).mapIso e ≪≫ leftUnitorNatIso C
    exact Functor.IsEquivalence.mk' (tensorLeft N) η ε
  · intro h
    let := h
    exact ⟨(tensorLeft L).objPreimage (𝟙_ C),
      ⟨(tensorLeft L).objObjPreimageIso (𝟙_ C)⟩⟩

end Langlands.CategoryTheory.Picard
