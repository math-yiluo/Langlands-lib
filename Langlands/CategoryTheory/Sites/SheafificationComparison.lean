import Mathlib.CategoryTheory.Sites.Sheafification

/-! # Comparing sheafifications for two ordered topologies -/

universe v v' u u'

open CategoryTheory

noncomputable section

namespace Langlands.CategoryTheory.SheafificationComparison

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  (J K : GrothendieckTopology C) [HasWeakSheafify J A] [HasWeakSheafify K A]
  (hJK : J ≤ K)

/-- The canonical map from sheafification for a smaller topology to a larger one. -/
def comparison (F : Cᵒᵖ ⥤ A) : sheafify J F ⟶ sheafify K F :=
  sheafifyLift J (toSheafify K F)
    (((presheafToSheaf K A).obj F).property.of_le hJK)

@[reassoc (attr := simp)]
lemma toSheafify_comparison (F : Cᵒᵖ ⥤ A) :
    toSheafify J F ≫ comparison J K hJK F = toSheafify K F :=
  toSheafify_sheafifyLift _ _ _

/-- The canonical comparison is natural in the original presheaf. -/
@[reassoc]
lemma comparison_naturality {F G : Cᵒᵖ ⥤ A} (η : F ⟶ G) :
    sheafifyMap J η ≫ comparison J K hJK G =
      comparison J K hJK F ≫ sheafifyMap K η := by
  apply sheafify_hom_ext J _ _
    (((presheafToSheaf K A).obj G).property.of_le hJK)
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    toSheafify_comparison, ← Category.assoc, toSheafify_comparison,
    ← toSheafify_naturality]

/-- If the smaller-topology sheafification is already a sheaf for the larger
 topology, the canonical comparison is an isomorphism. -/
def comparisonIso (F : Cᵒᵖ ⥤ A) (hF : Presheaf.IsSheaf K (sheafify J F)) :
    sheafify J F ≅ sheafify K F where
  hom := comparison J K hJK F
  inv := sheafifyLift K (toSheafify J F) hF
  hom_inv_id := by
    apply sheafify_hom_ext J _ _ ((presheafToSheaf J A).obj F).property
    simp [← Category.assoc]
  inv_hom_id := by
    apply sheafify_hom_ext K _ _ ((presheafToSheaf K A).obj F).property
    simp [← Category.assoc]

@[reassoc (attr := simp)]
lemma toSheafify_comparisonIso_hom (F : Cᵒᵖ ⥤ A)
    (hF : Presheaf.IsSheaf K (sheafify J F)) :
    toSheafify J F ≫ (comparisonIso J K hJK F hF).hom = toSheafify K F :=
  toSheafify_comparison J K hJK F

@[reassoc (attr := simp)]
lemma toSheafify_comparisonIso_inv (F : Cᵒᵖ ⥤ A)
    (hF : Presheaf.IsSheaf K (sheafify J F)) :
    toSheafify K F ≫ (comparisonIso J K hJK F hF).inv = toSheafify J F :=
  toSheafify_sheafifyLift _ _ _

end Langlands.CategoryTheory.SheafificationComparison
