/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import WeilConjectures.CategoryTheory.CanonicalFiltration
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianEvaluationColimits
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.Algebra.Homology.ComplexExtensionColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # Abelian total sections of a pro-etale hypercover -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex₂
open scoped Simplicial
namespace AlgebraicGeometry.Scheme.ProEt
noncomputable section

instance : Preadditive (CosimplicialObject AddCommGrpCat.{u + 1}) :=
  inferInstanceAs (Preadditive (SimplexCategory ⥤ AddCommGrpCat.{u + 1}))

/-- Underlying abelian sections on a simplicial object over W.
Source: Stacks Project, Tag 09A2.
(auxiliary; not a blueprint node). -/
def abelianHypercoverSections (X : Scheme.{u}) (W : X.ProEt)
    (U : SimplicialObject (Over W)) :
    Sheaf (topology X) AddCommGrpCat.{u + 1} ⥤
      CosimplicialObject AddCommGrpCat.{u + 1} :=
  sheafToPresheaf (topology X) AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringLeft _ _ _).obj (U ⋙ Over.forget W).rightOp

instance (X : Scheme.{u}) (W : X.ProEt) (U : SimplicialObject (Over W)) :
    (abelianHypercoverSections X W U).Additive where
  map_add := by intros; rfl

private instance alternating_additive :
    (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).Additive where
  map_add := by intros; rfl

/-- Alternating section rows, extended by zero in negative simplicial degrees.
Source: Stacks Project, Tag 09A2.
(auxiliary; not a blueprint node). -/
def abelianHypercoverRows (X : Scheme.{u}) (W : X.ProEt)
    (U : SimplicialObject (Over W)) :
    Sheaf (topology X) AddCommGrpCat.{u + 1} ⥤ CochainComplex AddCommGrpCat.{u + 1} ℤ :=
  abelianHypercoverSections X W U ⋙
    AlgebraicTopology.alternatingCofaceMapComplex _ ⋙
      ComplexShape.embeddingUpNat.extendFunctor _

instance (X : Scheme.{u}) (W : X.ProEt) (U : SimplicialObject (Over W)) :
    (abelianHypercoverRows X W U).Additive := by
  unfold abelianHypercoverRows
  infer_instance

/-- Coproduct total sections with differential δ + (-1)^p d.
For bounded-below inputs this agrees with the finite effective diagonal total.
Source: Stacks Project, Tag 09A2.
(auxiliary; not a blueprint node). -/
def abelianHypercoverTotal (X : Scheme.{u}) (W : X.ProEt)
    (U : SimplicialObject (Over W)) :
    CochainComplex (Sheaf (topology X) AddCommGrpCat.{u + 1}) ℤ ⥤
      CochainComplex AddCommGrpCat.{u + 1} ℤ :=
  (abelianHypercoverRows X W U).mapHomologicalComplex (.up ℤ) ⋙
    flipFunctor _ (.up ℤ) (.up ℤ) ⋙ totalFunctor _ _ _ (.up ℤ)

private theorem alternating_preservesColimits (C : Type*) [Category* C] [Preadditive C]
    (J : Type v) [Category.{w} J] [HasColimitsOfShape J C] :
    PreservesColimitsOfShape J (AlgebraicTopology.alternatingCofaceMapComplex C) := by
  constructor
  intro K
  have : HasColimitsOfShape J (CosimplicialObject C) := by
    unfold CosimplicialObject
    infer_instance
  apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit K)
  apply HomologicalComplex.isColimitOfEval
  intro n
  change IsColimit (((CategoryTheory.evaluation SimplexCategory C).obj
    (SimplexCategory.mk n)).mapCocone (colimit.cocone K))
  exact isColimitOfPreserves _ (colimit.isColimit K)

private theorem flip_preservesColimits {C : Type*} [Category* C] [Preadditive C]
    (J : Type v) [Category.{w} J] [HasColimitsOfShape J C] :
    PreservesColimitsOfShape J (flipFunctor C (.up ℤ) (.up ℤ)) := by
  constructor
  intro K
  apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit K)
  apply HomologicalComplex.isColimitOfEval
  intro p
  apply HomologicalComplex.isColimitOfEval
  intro q
  exact isColimitOfPreserves
    (HomologicalComplex.eval _ (.up ℤ) q ⋙ HomologicalComplex.eval C (.up ℤ) p)
    (colimit.isColimit K)

private theorem total_preservesColimits {C : Type*} [Category* C] [Preadditive C]
    [HasCoproducts.{0} C] (J : Type v) [Category.{w} J] [HasColimitsOfShape J C] :
    PreservesColimitsOfShape J (totalFunctor C (.up ℤ) (.up ℤ) (.up ℤ)) := by
  constructor
  intro K
  apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit K)
  apply HomologicalComplex.isColimitOfEval
  intro n
  let c := ComplexShape.up ℤ
  let hc := colimit.isColimit K
  have heval (p q : ℤ) : IsColimit
      ((HomologicalComplex.eval _ c p ⋙ HomologicalComplex.eval C c q).mapCocone
        (colimit.cocone K)) := isColimitOfPreserves _ hc
  refine { desc := (fun s ↦ (colimit K).totalDesc
    (fun p q h ↦ (heval p q).desc
      { pt := s.pt
        ι :=
          { app j := (K.obj j).ιTotal c p q n h ≫ s.ι.app j
            naturality j k f := by
              change ((K.map f).f p).f q ≫ (K.obj k).ιTotal c p q n h ≫ s.ι.app k =
                ((K.obj j).ιTotal c p q n h ≫ s.ι.app j) ≫ 𝟙 _
              rw [← ιTotal_map_assoc]
              have hw := s.w f
              change (total.map (K.map f) c).f n ≫ s.ι.app k = s.ι.app j at hw
              rw [hw, Category.comp_id] } }))
           fac := ?_, uniq := ?_ }
  · intro s j
    apply total.hom_ext
    intro p q h
    change (K.obj j).ιTotal c p q n h ≫
      (total.map (colimit.ι K j) c).f n ≫ _ =
        (K.obj j).ιTotal c p q n h ≫ s.ι.app j
    rw [ιTotal_map_assoc, ι_totalDesc]
    exact (heval p q).fac _ j
  · intro s m hm
    apply total.hom_ext
    intro p q h
    change (colimit K).ιTotal c p q n h ≫ m =
      (colimit K).ιTotal c p q n h ≫ _
    rw [ι_totalDesc]
    apply (heval p q).hom_ext
    intro j
    dsimp
    erw [(heval p q).fac]
    have hi := congrArg (fun f ↦ (K.obj j).ιTotal c p q n h ≫ f) (hm j)
    change (K.obj j).ιTotal c p q n h ≫
      (total.map (colimit.ι K j) c).f n ≫ m =
        (K.obj j).ιTotal c p q n h ≫ s.ι.app j at hi
    change ((colimit.ι K j).f p).f q ≫ (colimit K).ιTotal c p q n h ≫ m =
      (K.obj j).ιTotal c p q n h ≫ s.ι.app j
    simpa only [ιTotal_map_assoc] using hi

/-- Total abelian hypercover sections preserve small colimits when all terms are
 affine weakly contractible.
Source: Stacks Project, Tags 0935(2), 0946(1), and 09A2.
(auxiliary; not a blueprint node).
Proof: evaluate the cosimplicial object in each degree and apply affine exact
colimit-preserving evaluation. Alternating cofaces and extension by zero preserve
colimits degreewise. Flipping preserves them degreewise. In a total degree, the
coproduct of the individual colimits is the colimit of the coproducts; the descent
map is defined on each total summand and its equations follow on each summand. -/
theorem abelianHypercoverTotal_preservesColimits
    (X : Scheme.{u}) (W : X.ProEt) (U : SimplicialObject (Over W))
    (haff : ∀ n : ℕ, IsAffine (U _⦋n⦌).left.left)
    (hweak : ∀ (n : ℕ) (F G : Sheaf (topology X) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op (U _⦋n⦌).left))) :
    PreservesColimitsOfSize.{u + 1, u + 1} (abelianHypercoverTotal X W U) := by
  have (J : Type (u + 1)) [SmallCategory J] :
      PreservesColimitsOfShape J (abelianHypercoverSections X W U) := by
    apply preservesColimitsOfShape_of_evaluation
    intro n
    have : IsAffine (U.obj (op n)).left.left := haff n.len
    exact (affine_weaklyContractible_abelian_evaluation_colimits
      X (U.obj (op n)).left (hweak n.len)).2.preservesColimitsOfShape
  have (J : Type (u + 1)) [SmallCategory J] :
      PreservesColimitsOfShape J (abelianHypercoverTotal X W U) := by
    have := alternating_preservesColimits AddCommGrpCat.{u + 1} J
    have := extension_preservesColimits (C := AddCommGrpCat.{u + 1})
      ComplexShape.embeddingUpNat J
    have : PreservesColimitsOfShape J (abelianHypercoverRows X W U) := by
      unfold abelianHypercoverRows
      infer_instance
    have := flip_preservesColimits (C := AddCommGrpCat.{u + 1}) J
    have := total_preservesColimits (C := AddCommGrpCat.{u + 1}) J
    unfold abelianHypercoverTotal
    infer_instance
  exact ⟨fun {J} _ ↦ inferInstance⟩

end
end AlgebraicGeometry.Scheme.ProEt
