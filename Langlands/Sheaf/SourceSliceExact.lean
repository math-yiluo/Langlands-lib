import Langlands.Sheaf.SourceSlice
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.Algebra.Homology.Additive

/-! # Exact source changes for diagrams on slice sites -/

noncomputable section

universe uC vC uA vA uI vI uN

namespace Langlands.Sheaf

open CategoryTheory CategoryTheory.Limits

variable {C : Type uC} [Category.{vC} C]
variable (J : GrothendieckTopology C) (A : Type uA) [Category.{vA} A]
variable {I : Type uI} [Category.{vI} I] (Y : I ⥤ C)

instance overMapPullback_additive [Preadditive A] {X Z : C} (f : X ⟶ Z) :
    (J.overMapPullback A f).Additive where
  map_add := by
    intro F G f g
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    rfl

instance overPullback_additive [Preadditive A] (V : C) :
    (J.overPullback A V).Additive where
  map_add := by
    intro F G f g
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    rfl

instance sourceSliceRestriction_additive [Preadditive A] {k l : I} (f : k ⟶ l) :
    (sourceSliceRestriction J A Y f).Additive := by
  unfold sourceSliceRestriction
  infer_instance

instance sourceSliceReindex_additive [Preadditive A] {k l : I} (f : k ⟶ l) :
    (sourceSliceReindex J A Y f).Additive := by
  unfold sourceSliceReindex
  infer_instance

instance sourceSliceDiagramFunctor_additive [Preadditive A] (k : I) :
    (sourceSliceDiagramFunctor J A Y k).Additive := by
  unfold sourceSliceDiagramFunctor
  infer_instance

instance sourceSliceRestriction_preservesFiniteLimits [HasFiniteLimits A]
    {k l : I} (f : k ⟶ l) :
    PreservesFiniteLimits (sourceSliceRestriction J A Y f) where
  preservesFiniteLimits K _ _ := by
    unfold sourceSliceRestriction
    infer_instance

/-- Colimit preservation of restriction uses pullbacks in the site category;
existence of the finite colimits on its input slice is explicit. -/
instance sourceSliceRestriction_preservesFiniteColimits [HasPullbacks C]
    {k l : I} (f : k ⟶ l) [HasFiniteColimits (Sheaf (J.over (Y.obj l)) A)] :
    PreservesFiniteColimits (sourceSliceRestriction J A Y f) where
  preservesFiniteColimits K _ _ := by
    unfold sourceSliceRestriction
    infer_instance

instance sourceSliceReindex_preservesFiniteLimits [HasFiniteLimits A]
    {k l : I} (f : k ⟶ l) :
    PreservesFiniteLimits (sourceSliceReindex J A Y f) := by
  unfold sourceSliceReindex
  infer_instance

instance sourceSliceReindex_preservesFiniteColimits
    {k l : I} (f : k ⟶ l) [HasFiniteColimits (Sheaf (J.over (Y.obj k)) A)] :
    PreservesFiniteColimits (sourceSliceReindex J A Y f) := by
  unfold sourceSliceReindex
  infer_instance

instance sourceSliceDiagramFunctor_preservesFiniteLimits
    [HasBinaryProducts C] [HasFiniteLimits A] (k : I) :
    PreservesFiniteLimits (sourceSliceDiagramFunctor J A Y k) where
  preservesFiniteLimits K _ _ := by
    unfold sourceSliceDiagramFunctor
    infer_instance

instance sourceSliceDiagramFunctor_preservesFiniteColimits
    [HasBinaryProducts C] [HasFiniteColimits (Sheaf J A)] (k : I) :
    PreservesFiniteColimits (sourceSliceDiagramFunctor J A Y k) where
  preservesFiniteColimits K _ _ := by
    unfold sourceSliceDiagramFunctor
    infer_instance

section Complexes

variable [Preadditive A] {ι : Type uN} (c : ComplexShape ι)

/-- The actual source-change comparison acts termwise on whole diagram complexes. -/
def sourceSliceComplexChangeIso {k l : I} (f : k ⟶ l) :
    (sourceSliceDiagramFunctor J A Y l).mapHomologicalComplex c ⋙
        (sourceSliceRestriction J A Y f).mapHomologicalComplex c ≅
      (sourceSliceDiagramFunctor J A Y k).mapHomologicalComplex c ⋙
        (sourceSliceReindex J A Y f).mapHomologicalComplex c :=
  NatIso.mapHomologicalComplex (sourceSliceChangeFunctorIso J A Y f) c

@[simp] theorem sourceSliceComplexChangeIso_hom_app_f
    {k l : I} (f : k ⟶ l) (K : HomologicalComplex (I ⥤ Sheaf J A) c) (q : ι) :
    ((sourceSliceComplexChangeIso J A Y c f).hom.app K).f q =
      (sourceSliceChangeIso J A Y f (K.X q)).hom := rfl

@[simp] theorem sourceSliceComplexChangeIso_hom_app_f_app_hom_app
    {k l : I} (f : k ⟶ l) (K : HomologicalComplex (I ⥤ Sheaf J A) c)
    (q : ι) (i : Under l) (U : (Over (Y.obj k))ᵒᵖ) :
    ((((sourceSliceComplexChangeIso J A Y c f).hom.app K).f q).app i).hom.app U =
      𝟙 _ := rfl

end Complexes

end Langlands.Sheaf
