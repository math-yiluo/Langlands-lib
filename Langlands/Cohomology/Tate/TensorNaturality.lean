import Langlands.Cohomology.Tate.TensorShifts

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory TensorProduct

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G]

/-- Tensor a map of short complexes with a coefficient map on the right. -/
def tensorSequenceMapRight {S T : ShortComplex (Rep.{u} R G)}
    (f : S ⟶ T) {B B' : Rep.{u} R G} (g : B ⟶ B') :
    S.map (MonoidalCategory.tensorRight B) ⟶
      T.map (MonoidalCategory.tensorRight B') where
  τ₁ := f.τ₁ ⊗ₘ g
  τ₂ := f.τ₂ ⊗ₘ g
  τ₃ := f.τ₃ ⊗ₘ g
  comm₁₂ := by
    change (f.τ₁ ⊗ₘ g) ≫ (T.f ⊗ₘ 𝟙 B') = (S.f ⊗ₘ 𝟙 B) ≫ (f.τ₂ ⊗ₘ g)
    simp only [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id,
      Category.id_comp, f.comm₁₂]
  comm₂₃ := by
    change (f.τ₂ ⊗ₘ g) ≫ (T.g ⊗ₘ 𝟙 B') = (S.g ⊗ₘ 𝟙 B) ≫ (f.τ₃ ⊗ₘ g)
    simp only [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id,
      Category.id_comp, f.comm₂₃]

/-- Tensor a map of short complexes with a coefficient map on the left. -/
def tensorSequenceMapLeft {S T : ShortComplex (Rep.{u} R G)}
    (g : S ⟶ T) {A A' : Rep.{u} R G} (f : A ⟶ A') :
    S.map (MonoidalCategory.tensorLeft A) ⟶
      T.map (MonoidalCategory.tensorLeft A') where
  τ₁ := f ⊗ₘ g.τ₁
  τ₂ := f ⊗ₘ g.τ₂
  τ₃ := f ⊗ₘ g.τ₃
  comm₁₂ := by
    change (f ⊗ₘ g.τ₁) ≫ (𝟙 A' ⊗ₘ T.f) = (𝟙 A ⊗ₘ S.f) ≫ (f ⊗ₘ g.τ₂)
    simp only [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id,
      Category.id_comp, g.comm₁₂]
  comm₂₃ := by
    change (f ⊗ₘ g.τ₂) ≫ (𝟙 A' ⊗ₘ T.g) = (𝟙 A ⊗ₘ S.g) ≫ (f ⊗ₘ g.τ₃)
    simp only [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id,
      Category.id_comp, g.comm₂₃]

variable [Fintype G] {A A' B B' : Rep.{u} R G}

lemma tensorShiftUpLeftIso_naturality (f : A ⟶ A') (g : B ⟶ B') (n : ℤ) :
    (tensorShiftUpLeftIso A B n).hom ≫ (tateCohomologyFunctor (n + 1)).map (f ⊗ₘ g) =
      (tateCohomologyFunctor n).map (shiftUpMap f ⊗ₘ g) ≫
        (tensorShiftUpLeftIso A' B' n).hom :=
  TateCohomology.δ_naturality
    (scalarSplit_tensorRight_shortExact _ (shiftUpSequence_scalarSplitting A) B)
    (scalarSplit_tensorRight_shortExact _ (shiftUpSequence_scalarSplitting A') B')
    (tensorSequenceMapRight (shiftUpSequenceMap f) g) n

lemma tensorShiftUpRightIso_naturality (f : A ⟶ A') (g : B ⟶ B') (n : ℤ) :
    (tensorShiftUpRightIso A B n).hom ≫ (tateCohomologyFunctor (n + 1)).map (f ⊗ₘ g) =
      (tateCohomologyFunctor n).map (f ⊗ₘ shiftUpMap g) ≫
        (tensorShiftUpRightIso A' B' n).hom :=
  TateCohomology.δ_naturality
    (scalarSplit_tensorLeft_shortExact _ (shiftUpSequence_scalarSplitting B) A)
    (scalarSplit_tensorLeft_shortExact _ (shiftUpSequence_scalarSplitting B') A')
    (tensorSequenceMapLeft (shiftUpSequenceMap g) f) n

lemma tensorShiftDownLeftIso_naturality (f : A ⟶ A') (g : B ⟶ B') (n : ℤ) :
    (tensorShiftDownLeftIso A B n).hom ≫
        (tateCohomologyFunctor (n + 1)).map (shiftDownMap f ⊗ₘ g) =
      (tateCohomologyFunctor n).map (f ⊗ₘ g) ≫
        (tensorShiftDownLeftIso A' B' n).hom :=
  TateCohomology.δ_naturality
    (scalarSplit_tensorRight_shortExact _ (shiftDownSequence_scalarSplitting A) B)
    (scalarSplit_tensorRight_shortExact _ (shiftDownSequence_scalarSplitting A') B')
    (tensorSequenceMapRight (shiftDownSequenceMap f) g) n

lemma tensorShiftDownRightIso_naturality (f : A ⟶ A') (g : B ⟶ B') (n : ℤ) :
    (tensorShiftDownRightIso A B n).hom ≫
        (tateCohomologyFunctor (n + 1)).map (f ⊗ₘ shiftDownMap g) =
      (tateCohomologyFunctor n).map (f ⊗ₘ g) ≫
        (tensorShiftDownRightIso A' B' n).hom :=
  TateCohomology.δ_naturality
    (scalarSplit_tensorLeft_shortExact _ (shiftDownSequence_scalarSplitting B) A)
    (scalarSplit_tensorLeft_shortExact _ (shiftDownSequence_scalarSplitting B') A')
    (tensorSequenceMapLeft (shiftDownSequenceMap g) f) n

end Langlands.Tate
