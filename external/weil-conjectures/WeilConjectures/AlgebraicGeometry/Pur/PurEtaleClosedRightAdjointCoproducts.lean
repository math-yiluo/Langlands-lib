/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedSupportTriangle
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ClosedImmersion
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-!
# Coproducts and the right adjoint to closed direct image

## References

* Bhatt--Scholze, *Pro-étale topology*, Section 6.4, printed pp. 48--49
* Bhatt--Scholze, Pro-étale topology, Section 6.4, Lemma 6.4.4 and the last paragraph of Proposition
  6.4.8
-/

set_option autoImplicit false

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.Functor

open CategoryTheory.Pretriangulated
open Opposite CategoryTheory.Pretriangulated.Opposite

private noncomputable def cofanUnopIsColimit
    {C : Type u} [Category.{v} C] {I : Type w} (F : I → Cᵒᵖ) [HasProduct F] :
    IsColimit (Cofan.mk (∏ᶜ F).unop (fun i ↦ (Pi.π F i).unop)) := by
  let hc := productIsProduct F
  refine Cofan.IsColimit.mk _
    (fun s ↦ (hc.lift (Fan.mk (op s.pt) (fun i ↦ (s.inj i).op))).unop) ?_ ?_
  · intro s i
    apply Quiver.Hom.op_inj
    exact hc.fac (Fan.mk (op s.pt) (fun i ↦ (s.inj i).op)) (Discrete.mk i)
  · intro s m hm
    apply Quiver.Hom.op_inj
    apply hc.hom_ext
    intro ⟨i⟩
    exact (congrArg Quiver.Hom.op (hm i)).trans
      (hc.fac (Fan.mk (op s.pt) (fun i ↦ (s.inj i).op)) (Discrete.mk i)).symm

private theorem triangleCoproducts
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasCoproducts.{w} C] (I : Type w) (T : I → Triangle C)
    (hT : ∀ i, T i ∈ distTriang C) :
    ∃ c : Cofan T,
      Nonempty (IsColimit (Triangle.π₁.mapCocone c)) ∧
      Nonempty (IsColimit (Triangle.π₂.mapCocone c)) ∧
      Nonempty (IsColimit (Triangle.π₃.mapCocone c)) ∧ c.pt ∈ distTriang C := by
  classical
  let e := triangleOpEquivalence C
  let T' : I → Triangle Cᵒᵖ := fun i ↦ e.functor.obj (op (T i))
  let U := productTriangle T'
  let Z := (e.inverse.obj U).unop
  let c : Cofan T := Cofan.mk Z (fun i ↦
    ((e.unitIso.app (op (T i))).unop).inv ≫
      (e.inverse.map (productTriangle.π T' i)).unop)
  refine ⟨c, ⟨?_⟩, ⟨?_⟩, ⟨?_⟩, ?_⟩
  · refine (isColimitMapCoconeCofanMkEquiv Triangle.π₁ T _).symm ?_
    refine IsColimit.ofIsoColimit (cofanUnopIsColimit (fun i ↦ (T' i).obj₃))
      (Cocone.ext (Iso.refl _) ?_)
    intro ⟨i⟩
    change (Pi.π (fun i ↦ (T' i).obj₃) i).unop ≫ 𝟙 _ =
      𝟙 _ ≫ (Pi.π (fun i ↦ (T' i).obj₃) i).unop
    simp only [Category.id_comp, Category.comp_id]
  · refine (isColimitMapCoconeCofanMkEquiv Triangle.π₂ T _).symm ?_
    refine IsColimit.ofIsoColimit (cofanUnopIsColimit (fun i ↦ (T' i).obj₂))
      (Cocone.ext (Iso.refl _) ?_)
    intro ⟨i⟩
    change (Pi.π (fun i ↦ (T' i).obj₂) i).unop ≫ 𝟙 _ =
      𝟙 _ ≫ (Pi.π (fun i ↦ (T' i).obj₂) i).unop
    simp only [Category.id_comp, Category.comp_id]
  · refine (isColimitMapCoconeCofanMkEquiv Triangle.π₃ T _).symm ?_
    refine IsColimit.ofIsoColimit (cofanUnopIsColimit (fun i ↦ (T' i).obj₁))
      (Cocone.ext (Iso.refl _) ?_)
    intro ⟨i⟩
    change (Pi.π (fun i ↦ (T' i).obj₁) i).unop ≫ 𝟙 _ =
      𝟙 _ ≫ (Pi.π (fun i ↦ (T' i).obj₁) i).unop
    simp only [Category.id_comp, Category.comp_id]
  · exact unop_distinguished U (productTriangle_distinguished T'
      (fun i ↦ op_distinguished (T i) (hT i)))

private theorem preservesCoproducts_of_triangle
    {A : Type*} [Category A] [HasZeroObject A] [HasShift A ℤ]
    [Preadditive A] [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    [HasCoproducts.{u + 1} A] (H Q : A ⥤ A)
    (ε : H ⟶ 𝟭 A) (η : 𝟭 A ⟶ Q)
    (δ : Q ⟶ H ⋙ shiftFunctor A (1 : ℤ))
    (hT : ∀ K, Triangle.mk (ε.app K) (η.app K) (δ.app K) ∈ distTriang A)
    (I : Type (u + 1)) [PreservesColimitsOfShape (Discrete I) Q] :
    PreservesColimitsOfShape (Discrete I) H := by
  classical
  let T : A ⥤ Triangle A :=
    { obj := fun K ↦ Triangle.mk (ε.app K) (η.app K) (δ.app K)
      map := fun f ↦
        { hom₁ := H.map f
          hom₂ := f
          hom₃ := Q.map f
          comm₁ := (ε.naturality f).symm
          comm₂ := (η.naturality f).symm
          comm₃ := (δ.naturality f).symm } }
  have hpres (E : I → A) : PreservesColimit (Discrete.functor E) H := by
    obtain ⟨c, ⟨hc₁⟩, ⟨hc₂⟩, ⟨hc₃⟩, hc⟩ :=
      triangleCoproducts I (fun i ↦ T.obj (E i)) (fun i ↦ hT (E i))
    let s : Cofan (fun i ↦ T.obj (E i)) :=
      Cofan.mk (T.obj (∐ E)) (fun i ↦ T.map (Sigma.ι E i))
    let hc₁ := (Cofan.isColimitMapCoconeEquiv Triangle.π₁ _ c) hc₁
    let hc₂ := (Cofan.isColimitMapCoconeEquiv Triangle.π₂ _ c) hc₂
    let hc₃ := (Cofan.isColimitMapCoconeEquiv Triangle.π₃ _ c) hc₃
    let s₁ : Cofan (fun i ↦ H.obj (E i)) :=
      Cofan.mk (H.obj (∐ E)) (fun i ↦ H.map (Sigma.ι E i))
    let s₂ : Cofan E := Cofan.mk (∐ E) (Sigma.ι E)
    let s₃ : Cofan (fun i ↦ Q.obj (E i)) :=
      Cofan.mk (Q.obj (∐ E)) (fun i ↦ Q.map (Sigma.ι E i))
    let a := hc₁.desc s₁
    let b := hc₂.desc s₂
    let d := hc₃.desc s₃
    have ha' (i : I) : (c.inj i).hom₁ ≫ a = (s.inj i).hom₁ := hc₁.fac s₁ ⟨i⟩
    have hb' (i : I) : (c.inj i).hom₂ ≫ b = (s.inj i).hom₂ := hc₂.fac s₂ ⟨i⟩
    have hd' (i : I) : (c.inj i).hom₃ ≫ d = (s.inj i).hom₃ := hc₃.fac s₃ ⟨i⟩
    let φ : c.pt ⟶ s.pt :=
      { hom₁ := a
        hom₂ := b
        hom₃ := d
        comm₁ := by
          apply hc₁.hom_ext
          intro ⟨i⟩
          change (c.inj i).hom₁ ≫ _ = _
          rw [← Category.assoc, ← (c.inj i).comm₁, Category.assoc, hb',
            ← Category.assoc]
          erw [ha']
          exact (s.inj i).comm₁
        comm₂ := by
          apply hc₂.hom_ext
          intro ⟨i⟩
          change (c.inj i).hom₂ ≫ _ = _
          rw [← Category.assoc, ← (c.inj i).comm₂, Category.assoc, hd',
            ← Category.assoc]
          erw [hb']
          exact (s.inj i).comm₂
        comm₃ := by
          apply hc₃.hom_ext
          intro ⟨i⟩
          change (c.inj i).hom₃ ≫ _ = _
          rw [← Category.assoc, ← (c.inj i).comm₃, Category.assoc,
            ← Functor.map_comp]
          rw [ha', ← Category.assoc]
          erw [hd']
          exact (s.inj i).comm₃ }
    have hs₂ : IsColimit s₂ := coproductIsCoproduct E
    have hs₃ : IsColimit s₃ :=
      isColimitOfHasCoproductOfPreservesColimit Q E
    have hb : IsIso φ.hom₂ := by
      change IsIso (hc₂.coconePointUniqueUpToIso hs₂).hom
      infer_instance
    have hd : IsIso φ.hom₃ := by
      change IsIso (hc₃.coconePointUniqueUpToIso hs₃).hom
      infer_instance
    have ha : IsIso a := isIso₁_of_isIso₂₃ φ hc (hT (∐ E)) hb hd
    apply preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct E)
    refine (isColimitMapCoconeCofanMkEquiv H E _).symm ?_
    exact IsColimit.ofPointIso hc₁
  let _ := hpres
  exact preservesColimitsOfShape_of_discrete H

namespace AlgebraicGeometry.Etale

/-- The right adjoint to closed derived direct image preserves arbitrary coproducts
when the ambient scheme is finite type over an algebraically closed field. -/
theorem preservesCoproducts_closedRightAdjoint
    {k : Type u} [Field k] [IsAlgClosed k]
    (C : Type (u + 1)) [CommRing C] [Finite C]
    {X Z : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I)
      (R(lowerStar (ModuleCat.{u + 1} C) g)).rightAdjoint := by
  let : HasCoproducts.{u + 1} (DerivedCategoryModule C X) :=
    CategoryTheory.derived_hasCoproducts
  let : HasCoproducts.{u + 1} (DerivedCategoryModule C Z) :=
    CategoryTheory.derived_hasCoproducts
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  let W : X.Opens := ⟨(Set.range g.base)ᶜ,
    (IsClosedImmersion.isClosedEmbedding g).isClosed_range.isOpen_compl⟩
  have hij : Set.range g.base = (Set.range W.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]
    exact (compl_compl _).symm
  have : NoetherianSpace W := W.ι.isOpenEmbedding.isEmbedding.noetherianSpace
  have : CompactSpace W := inferInstance
  have hcd := hasFiniteCohomologicalDimensionMorphism_of_isSepClosed_of_locallyOfFiniteType
    C (isAddTorsion_of_finite) (W.ι ≫ f) f W.ι rfl
  let F := R(lowerStar (ModuleCat.{u + 1} C) g)
  let G := F.rightAdjoint
  let J := D(upperStar (ModuleCat.{u + 1} C) W.ι)
  let Q := R(lowerStar (ModuleCat.{u + 1} C) W.ι)
  have : PreservesColimitsOfShape (Discrete I) Q :=
    preservesCoproducts_rightDerivedLowerStar C W.ι hcd I
  have : J.IsLeftAdjoint :=
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} C) W.ι).isLeftAdjoint
  obtain ⟨δ, hδ⟩ := exists_etale_closedSupportTriangle C g W.ι hij
  have : PreservesColimitsOfShape (Discrete I) (G ⋙ F) :=
    preservesCoproducts_of_triangle (G ⋙ F) (J ⋙ Q)
      (Adjunction.ofIsLeftAdjoint F).counit
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} C) W.ι).unit δ hδ I
  have : ReflectsColimitsOfShape (Discrete I) F :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves G F

end AlgebraicGeometry.Etale
