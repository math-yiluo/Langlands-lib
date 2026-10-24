import Langlands.AlgebraicGeometry.FiniteEtale.StructuralStatements
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Types.Coproducts

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.FiniteEtale

open _root_.AlgebraicGeometry

/-- The morphism property of being finite étale. -/
abbrev finiteEtale : MorphismProperty Scheme.{u} := @IsFinite ⊓ @Etale

theorem coverProperty_eq (S : Scheme.{u}) : coverProperty S = finiteEtale.overObj := rfl

instance finiteEtale_hasOfPostcompProperty :
    finiteEtale.{u}.HasOfPostcompProperty finiteEtale := by
  have : MorphismProperty.HasOfPostcompProperty @IsFinite.{u} finiteEtale :=
    .of_le _ @IsSeparated (fun _ _ f hf => by have := hf.1; infer_instance)
  have : MorphismProperty.HasOfPostcompProperty @Etale.{u} finiteEtale :=
    .of_le _ @Etale inf_le_right
  infer_instance

/-- A coproduct of two étale morphisms is étale. -/
theorem etale_coprod_desc {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [Etale f] [Etale g] :
    Etale (coprod.desc f g) := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Etale) (coprodOpenCover.{_, 0} X Y)]
  rintro (⟨⟩ | ⟨⟩) <;> simpa [coprodOpenCover]

variable (S : Scheme.{u})

instance coverProperty_isClosedUnderLimitsOfShape_pempty :
    (coverProperty S).IsClosedUnderLimitsOfShape (Discrete PEmpty.{1}) := by
  rw [coverProperty_eq]; infer_instance

instance coverProperty_isClosedUnderLimitsOfShape_cospan :
    (coverProperty S).IsClosedUnderLimitsOfShape WalkingCospan := by
  rw [coverProperty_eq]; infer_instance

instance coverProperty_isClosedUnderColimitsOfShape_pempty :
    (coverProperty S).IsClosedUnderColimitsOfShape (Discrete PEmpty.{1}) := by
  refine CostructuredArrow.isClosedUnderColimitsOfShape (P := finiteEtale) (L := 𝟭 _)
    (fun D _ => colimit.cocone D) (fun D _ => colimit.isColimit D) ?_ S
  intro D _ X s _
  let e : colimit D ≅ ⊥_ Scheme := HasColimit.isoOfNatIso D.uniqueFromEmpty
  have : IsEmpty ↥(colimit.cocone D).pt := Function.isEmpty ⇑e.hom
  exact ⟨inferInstance, inferInstance⟩

instance coverProperty_isClosedUnderColimitsOfShape_pair :
    (coverProperty S).IsClosedUnderColimitsOfShape (Discrete WalkingPair) := by
  refine CostructuredArrow.isClosedUnderColimitsOfShape (P := finiteEtale) (L := 𝟭 _)
    (fun D _ => colimit.cocone D) (fun D _ => colimit.isColimit D) ?_ S
  intro D _ X s hs
  let e := HasColimit.isoOfNatIso (diagramIsoPair D)
  have h : (colimit.isColimit D).desc (Cocone.mk X s) =
      e.hom ≫ coprod.desc (s.app ⟨.left⟩) (s.app ⟨.right⟩) := by
    refine colimit.hom_ext fun ⟨j⟩ => ?_
    cases j <;> simp [e]
  have := (hs ⟨.left⟩).1
  have := (hs ⟨.left⟩).2
  have := (hs ⟨.right⟩).1
  have := (hs ⟨.right⟩).2
  rw [h]
  refine (MorphismProperty.cancel_left_of_respectsIso finiteEtale e.hom _).mpr ?_
  exact ⟨inferInstance, etale_coprod_desc _ _⟩

instance coverProperty_isClosedUnderFiniteCoproducts :
    (coverProperty S).IsClosedUnderFiniteCoproducts :=
  ObjectProperty.IsClosedUnderFiniteCoproducts.mk'

/-! ### Points of coproducts of schemes -/

section Points

variable {K : Type u} [Field K] {A B : Scheme.{u}}

/-- A morphism from the spectrum of a field into a binary coproduct of schemes factors through
one of the two coprojections. -/
theorem exists_factor_coprod (y : Spec (.of K) ⟶ A ⨿ B) :
    (∃ a : Spec (.of K) ⟶ A, a ≫ coprod.inl = y) ∨
      ∃ b : Spec (.of K) ⟶ B, b ≫ coprod.inr = y := by
  have hy : y default ∈ (⊤ : Set ↥(A ⨿ B)) := trivial
  rw [← (isCompl_range_inl_inr A B).sup_eq_top] at hy
  have hrange {Z : Scheme.{u}} (f : Z ⟶ A ⨿ B) (hf : y default ∈ Set.range f) :
      Set.range y ⊆ Set.range f := by
    rintro _ ⟨p, rfl⟩
    rwa [Subsingleton.elim p default]
  rcases hy with h | h
  · exact .inl ⟨IsOpenImmersion.lift _ y (hrange _ h), IsOpenImmersion.lift_fac _ _ _⟩
  · exact .inr ⟨IsOpenImmersion.lift _ y (hrange _ h), IsOpenImmersion.lift_fac _ _ _⟩

/-- No morphism from the spectrum of a field into a binary coproduct of schemes factors through
both coprojections. -/
theorem comp_inl_ne_comp_inr (a : Spec (.of K) ⟶ A) (b : Spec (.of K) ⟶ B) :
    a ≫ coprod.inl ≠ b ≫ coprod.inr := by
  intro h
  have h' : (a ≫ coprod.inl) default = (b ≫ coprod.inr) default := by rw [h]
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h'
  exact Set.disjoint_left.mp (isCompl_range_inl_inr A B).disjoint ⟨_, rfl⟩ ⟨_, h'.symm⟩

end Points

/-! ### Preservation by the point functor -/

variable {S} {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)

instance pointFunctor_preservesLimitsOfShape_pempty :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (pointFunctor s) :=
  inferInstanceAs
    (PreservesLimitsOfShape _ (inclusion S ⋙ coyoneda.obj (Opposite.op (Over.mk s))))

instance pointFunctor_preservesLimitsOfShape_cospan :
    PreservesLimitsOfShape WalkingCospan (pointFunctor s) :=
  inferInstanceAs
    (PreservesLimitsOfShape _ (inclusion S ⋙ coyoneda.obj (Opposite.op (Over.mk s))))

/-- The underlying scheme of a finite étale cover. -/
abbrev coverToScheme (S : Scheme.{u}) : Cover S ⥤ Scheme.{u} := inclusion S ⋙ Over.forget S

/-- The point functor sends the coproduct cofan of two covers to a coproduct of sets. -/
noncomputable def pointFunctorCoprodIsColimit (X Y : Cover S) :
    IsColimit (BinaryCofan.mk ((pointFunctor s).map (coprod.inl : X ⟶ X ⨿ Y))
      ((pointFunctor s).map coprod.inr)) := by
  let e := PreservesColimitPair.iso (coverToScheme S) X Y
  have hl : (coprod.inl : X ⟶ X ⨿ Y).hom.left = coprod.inl ≫ e.hom := by
    rw [PreservesColimitPair.iso_hom]
    exact (coprodComparison_inl (coverToScheme S)).symm
  have hr : (coprod.inr : Y ⟶ X ⨿ Y).hom.left = coprod.inr ≫ e.hom := by
    rw [PreservesColimitPair.iso_hom]
    exact (coprodComparison_inr (coverToScheme S)).symm
  refine ((Types.binaryCofan_isColimit_iff _).mpr ⟨?_, ?_, ?_⟩).some
  · intro x x' h
    have h' : x.left ≫ (coprod.inl : X ⟶ X ⨿ Y).hom.left =
        x'.left ≫ (coprod.inl : X ⟶ X ⨿ Y).hom.left :=
      congrArg CommaMorphism.left h
    rw [hl, ← Category.assoc, ← Category.assoc, cancel_mono, cancel_mono] at h'
    exact Over.OverMorphism.ext h'
  · intro x x' h
    have h' : x.left ≫ (coprod.inr : Y ⟶ X ⨿ Y).hom.left =
        x'.left ≫ (coprod.inr : Y ⟶ X ⨿ Y).hom.left :=
      congrArg CommaMorphism.left h
    rw [hr, ← Category.assoc, ← Category.assoc, cancel_mono, cancel_mono] at h'
    exact Over.OverMorphism.ext h'
  · refine ⟨Set.disjoint_left.mpr ?_,
      codisjoint_iff.mpr (Set.eq_univ_of_forall fun (y : Fiber s (X ⨿ Y)) => ?_)⟩
    · rintro _ ⟨x, rfl⟩ ⟨x', h⟩
      have h' : x'.left ≫ (coprod.inr : Y ⟶ X ⨿ Y).hom.left =
          x.left ≫ (coprod.inl : X ⟶ X ⨿ Y).hom.left :=
        congrArg CommaMorphism.left h
      rw [hl, hr, ← Category.assoc, ← Category.assoc, cancel_mono] at h'
      exact comp_inl_ne_comp_inr _ _ h'.symm
    · have hy : y.left ≫ (X ⨿ Y).obj.hom = s := Over.w y
      rcases exists_factor_coprod (y.left ≫ e.inv) with ⟨a, ha⟩ | ⟨b, hb⟩
      · have hfac : a ≫ (coprod.inl : X ⟶ X ⨿ Y).hom.left = y.left := by
          rw [hl, ← Category.assoc, ha, Category.assoc, e.inv_hom_id]
          exact Category.comp_id _
        refine Or.inl ⟨Over.homMk a ?_, Over.OverMorphism.ext hfac⟩
        show a ≫ X.obj.hom = s
        rw [← Over.w (coprod.inl : X ⟶ X ⨿ Y).hom, ← Category.assoc, hfac, hy]
      · have hfac : b ≫ (coprod.inr : Y ⟶ X ⨿ Y).hom.left = y.left := by
          rw [hr, ← Category.assoc, hb, Category.assoc, e.inv_hom_id]
          exact Category.comp_id _
        refine Or.inr ⟨Over.homMk b ?_, Over.OverMorphism.ext hfac⟩
        show b ≫ Y.obj.hom = s
        rw [← Over.w (coprod.inr : Y ⟶ X ⨿ Y).hom, ← Category.assoc, hfac, hy]

instance pointFunctor_preservesColimitsOfShape_pair :
    PreservesColimitsOfShape (Discrete WalkingPair) (pointFunctor s) where
  preservesColimit {K} := by
    have : PreservesColimit (pair (K.obj ⟨.left⟩) (K.obj ⟨.right⟩)) (pointFunctor s) :=
      preservesColimit_of_preserves_colimit_cocone (coprodIsCoprod _ _)
        ((isColimitMapCoconeBinaryCofanEquiv _ _ _).symm (pointFunctorCoprodIsColimit s _ _))
    exact preservesColimit_of_iso_diagram _ (diagramIsoPair K).symm

instance pointFunctor_preservesColimitsOfShape_pempty :
    PreservesColimitsOfShape (Discrete PEmpty.{1}) (pointFunctor s) := by
  have hempty : IsEmpty ↥((coverToScheme S).obj (⊥_ (Cover S))) :=
    isInitial_iff_isEmpty.mp ⟨IsInitial.isInitialObj (coverToScheme S) _ initialIsInitial⟩
  have : PreservesColimit (Functor.empty.{0} (Cover S)) (pointFunctor s) :=
    preservesColimit_of_preserves_colimit_cocone initialIsInitial
      ((isColimitMapCoconeEmptyCoconeEquiv _ _).symm
        ((Types.initial_iff_empty _).mpr ⟨fun (x : Over.mk s ⟶ (⊥_ (Cover S)).obj) =>
          hempty.false (x.left (default : Spec (.of Ω)))⟩).some)
  exact preservesColimitsOfShape_pempty_of_preservesInitial _

/-! ### Preservation by the fibre functor -/

variable (hfin : ∀ Y : Cover S, Finite (Fiber s Y))

instance fiberFunctor_preservesLimitsOfShape (J : Type) [SmallCategory J]
    [PreservesLimitsOfShape J (pointFunctor s)] :
    PreservesLimitsOfShape J (fiberFunctor s hfin) :=
  have : PreservesLimitsOfShape J (fiberFunctor s hfin ⋙ FintypeCat.incl) :=
    inferInstanceAs (PreservesLimitsOfShape J (pointFunctor s))
  preservesLimitsOfShape_of_reflects_of_preserves _ FintypeCat.incl

instance fiberFunctor_preservesColimitsOfShape (J : Type) [SmallCategory J]
    [PreservesColimitsOfShape J (pointFunctor s)] :
    PreservesColimitsOfShape J (fiberFunctor s hfin) :=
  have : PreservesColimitsOfShape J (fiberFunctor s hfin ⋙ FintypeCat.incl) :=
    inferInstanceAs (PreservesColimitsOfShape J (pointFunctor s))
  preservesColimitsOfShape_of_reflects_of_preserves _ FintypeCat.incl

instance fiberFunctor_preservesFiniteCoproducts : PreservesFiniteCoproducts (fiberFunctor s hfin) :=
  ⟨fun n => PreservesFiniteCoproducts.of_preserves_binary_and_initial _ (Fin n)⟩

end Langlands.AlgebraicGeometry.FiniteEtale

open Langlands.AlgebraicGeometry.FiniteEtale in
/-- The published structural proposition on finite limits and finite coproducts of finite étale
covers and their preservation by the geometric fibre functor. -/
theorem Langlands.AlgebraicGeometry.FiniteEtale.geometricFiniteLimitsCoproducts
    {S : AlgebraicGeometry.Scheme.{u}} [ConnectedSpace S]
    [AlgebraicGeometry.IsLocallyNoetherian S] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : AlgebraicGeometry.Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y)) :
    GeometricFiniteLimitsCoproducts s hfin :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
