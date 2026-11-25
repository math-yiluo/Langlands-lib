/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived

/-! # A normalized cochain derived adjunction from resolving models

Source: Stacks Project, Derived Categories, Tags 0FND and 09T5.
(blueprint: lem-cbc-cochain-derived-adjunction).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u v u' v' w w'
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor
namespace CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem kan_of_precomp_quotient
    {A : Type u} [Category.{v} A] [Abelian A]
    {D : Type u'} [Category.{v'} D] {H : Type w} [Category.{w'} H]
    (L : HomotopyCategory A (.up ℤ) ⥤ D)
    (G : HomotopyCategory A (.up ℤ) ⥤ H) (F : D ⥤ H)
    (α : L ⋙ F ⟶ G)
    (h : F.IsRightKanExtension
      ((associator (HomotopyCategory.quotient A (.up ℤ)) L F).hom ≫
        whiskerLeft (HomotopyCategory.quotient A (.up ℤ)) α)) :
    F.IsRightKanExtension α := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  have : ((whiskeringLeft _ _ H).obj q).Full := by
    exact inferInstanceAs (((whiskeringLeft _ _ H).obj
      (HomotopyCategory.quotient A (.up ℤ))).Full)
  have : ((whiskeringLeft _ _ H).obj q).Faithful := by
    exact inferInstanceAs (((whiskeringLeft _ _ H).obj
      (HomotopyCategory.quotient A (.up ℤ))).Faithful)
  let P := RightExtension.precomp L G q
  have : P.Full := by
    dsimp only [P, RightExtension.precomp]
    apply CostructuredArrow.full_map₂
  have : P.Faithful := by
    dsimp [P, RightExtension.precomp]
    infer_instance
  let β := (associator q L F).hom ≫ whiskerLeft q α
  let e : P.obj (RightExtension.mk F α) ≅ RightExtension.mk F β :=
    CostructuredArrow.isoMk (Iso.refl _)
  let := h
  exact ⟨⟨IsTerminal.isTerminalOfObj P _
    (IsTerminal.ofIso (F.isUniversalOfIsRightKanExtension β) e.symm)⟩⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem kan_change_iso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {Q Q' : C ⥤ D} {G G' : C ⥤ H} (F : D ⥤ H)
    (i : Q ≅ Q') (j : G ≅ G') (α : Q ⋙ F ⟶ G)
    [F.IsRightKanExtension α] :
    F.IsRightKanExtension (whiskerRight i.inv F ≫ α ≫ j.hom) := by
  let P := (rightExtensionEquivalenceOfIso₁ i G).functor ⋙
    (rightExtensionEquivalenceOfIso₂ Q' j).functor
  constructor
  refine ⟨IsTerminal.ofIso
    (IsTerminal.isTerminalObj P _ (F.isUniversalOfIsRightKanExtension α)) ?_⟩
  exact CostructuredArrow.isoMk (Iso.refl _) (by
    ext X
    simp [P, rightExtensionEquivalenceOfIso₁, rightExtensionEquivalenceOfIso₂])

private theorem inverted_indDiagram
    {D : Type*} [Category* D] {H : Type*} [Category* H]
    (W : MorphismProperty D) [W.HasLeftCalculusOfFractions]
    (U : D ⥤ H) (hU : W.IsInvertedBy U) (X : D) :
    IsEssentiallyConstantIndDiagram
      (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ U) (U.obj X) := by
  classical
  let I := W.Under ⊤ X
  let V := MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ U
  have hI : IsFiltered I := by
    refine {
      nonempty := ⟨MorphismProperty.Under.mk ⊤ (𝟙 X) (W.id_mem X)⟩
      cocone_objs := ?_
      cocone_maps := ?_ }
    · intro s t
      obtain ⟨ψ, hψ⟩ :=
        (MorphismProperty.RightFraction.mk s.hom s.prop t.hom).exists_leftFraction
      let k : I := MorphismProperty.Under.mk ⊤ (t.hom ≫ ψ.s)
        (W.comp_mem _ _ t.prop ψ.hs)
      exact ⟨k, MorphismProperty.Under.homMk ψ.f hψ.symm,
        MorphismProperty.Under.homMk ψ.s, trivial⟩
    · intro s t f g
      obtain ⟨Y, a, ha, heq⟩ := MorphismProperty.HasLeftCalculusOfFractions.ext
        f.right g.right s.hom s.prop (f.w.symm.trans g.w)
      let k : I := MorphismProperty.Under.mk ⊤ (t.hom ≫ a)
        (W.comp_mem _ _ t.prop ha)
      refine ⟨k, MorphismProperty.Under.homMk a, ?_⟩
      exact MorphismProperty.Under.Hom.ext heq
  have hi (j : I) : IsIso (U.map j.hom) := hU _ j.prop
  let p : V ⟶ (Functor.const I).obj (U.obj X) :=
    { app := fun j ↦ CategoryTheory.inv (U.map j.hom)
      naturality := by
        intro s t f
        change U.map f.right ≫ CategoryTheory.inv (U.map t.hom) =
          CategoryTheory.inv (U.map s.hom) ≫ 𝟙 _
        apply (cancel_epi (U.map s.hom)).1
        rw [← Category.assoc, ← U.map_comp, MorphismProperty.Under.w f]
        simp }
  let j₀ : I := MorphismProperty.Under.mk ⊤ (𝟙 X) (W.id_mem X)
  refine ⟨hI, p, j₀, 𝟙 _, ?_, ?_⟩
  · change 𝟙 _ ≫ CategoryTheory.inv (U.map (𝟙 X)) = 𝟙 _
    simp
  · intro j
    refine ⟨j, MorphismProperty.Under.homMk j.hom (by simp [j₀]), 𝟙 j, ?_⟩
    change U.map (𝟙 j.right) = CategoryTheory.inv (U.map j.hom) ≫ 𝟙 _ ≫ U.map j.hom
    simp

/-- An ordinary adjunction and a universal cochain left derived pair computed on resolutions
induce a derived adjunction, with the original unit and the specified cochain counit.

Source: Stacks Project, Derived Categories, Tags 0FND and 09T5
(blueprint: lem-cbc-cochain-derived-adjunction).

Proof: Transfer the universal counit along the full homotopy quotient and its localization
comparison. The resolving class makes incoming denominator diagrams essentially constant;
exactness of restriction makes outgoing ones constant. Apply derived-adjunction compatibility
on homotopy categories. Its representative formula applied to the identity is the unit
formula. Conjugating by the quotient/localization comparisons gives the cochain formula. -/
theorem exists_cochainDerivedAdjunction
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    (E : A ⥤ B) [E.Additive] (V : B ⥤ A) [V.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V] (adj : E ⊣ V)
    (F : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ F ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ))]
    (P : ObjectProperty (CochainComplex A ℤ))
    (hres : ∀ K, ∃ (L : CochainComplex A ℤ) (p : L ⟶ K), P L ∧ QuasiIso p)
    (hε : ∀ K, P K → IsIso (ε.app K)) :
    ∃ d : F ⊣ V.mapDerivedCategory,
      ∀ K : CochainComplex A ℤ,
        d.unit.app (DerivedCategory.Q.obj K) ≫ V.mapDerivedCategory.map (ε.app K) ≫
          V.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj K) =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) := by
  classical
  let q := HomotopyCategory.quotient A (.up ℤ)
  let H := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := B)
  let i := DerivedCategory.quotientCompQhIso A
  let j : q ⋙ H ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (associator _ _ _).symm ≪≫
      isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  let α₀ := whiskerRight i.hom F ≫ ε ≫ j.inv
  let αpre : q ⋙ (DerivedCategory.Qh ⋙ F) ⟶ q ⋙ H :=
    (associator _ _ _).inv ≫ α₀
  let α : DerivedCategory.Qh ⋙ F ⟶ H :=
    ((whiskeringLeft _ _ _).obj q).preimage αpre
  have hαpre : whiskerLeft q α = αpre :=
    ((whiskeringLeft _ _ _).obj q).map_preimage αpre
  have hα : F.IsRightKanExtension α := by
    apply kan_of_precomp_quotient _ _ _ α
    have := IsLeftDerivedFunctor.isRightKanExtension F ε
      (HomologicalComplex.quasiIso A (.up ℤ))
    have hh := kan_change_iso F i.symm j.symm ε
    have he : (associator q DerivedCategory.Qh F).hom ≫ whiskerLeft q α = α₀ := by
      rw [hαpre]
      simp [αpre]
    rw [he]
    exact hh
  let WA := HomotopyCategory.quasiIso A (.up ℤ)
  let WB := HomotopyCategory.quasiIso B (.up ℤ)
  let P' : Set (HomotopyCategory A (.up ℤ)) := fun X ↦
    ∃ K : CochainComplex A ℤ, P K ∧ q.obj K = X
  have hres' : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : HomotopyCategory A (.up ℤ)) (s : Y ⟶ X), Y ∈ P' ∧ WA s := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨L, p, hL, hp⟩ := hres K
    exact ⟨q.obj L, q.map p, ⟨L, hL, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hp⟩
  have hαiso : ∀ X, X ∈ P' → IsIso (α.app X) := by
    rintro X ⟨K, hK, rfl⟩
    have := hε K hK
    have he := NatTrans.congr_app hαpre K
    change α.app (q.obj K) = _ at he
    rw [he]
    dsimp [αpre, α₀]
    simp only [Category.id_comp, isIso_comp_left_iff, MorphismProperty.isomorphisms.iff]
    infer_instance
  have hinv : ∀ (X Y : HomotopyCategory A (.up ℤ)) (s : X ⟶ Y),
      X ∈ P' → Y ∈ P' → WA s → IsIso (H.map s) := by
    intro X Y s hX hY hs
    have := hαiso X hX
    have := hαiso Y hY
    have : IsIso (DerivedCategory.Qh.map s) :=
      Localization.inverts DerivedCategory.Qh _ _ hs
    rw [← isIso_comp_left_iff (α.app X), ← α.naturality s]
    change IsIso (F.map (DerivedCategory.Qh.map s) ≫ α.app Y)
    infer_instance
  have : WA.HasTwoOutOfThreeProperty :=
    (HomotopyCategory.quasiIso_saturated_triangulated A).2.2.2.2.1
  have : WA.HasRightCalculusOfFractions :=
    (HomotopyCategory.quasiIso_saturated_triangulated A).2.1
  have : WB.HasLeftCalculusOfFractions :=
    (HomotopyCategory.quasiIso_saturated_triangulated B).1
  have hL : ∀ X, ∃ Y, IsEssentiallyConstantProDiagram
      (MorphismProperty.Over.forget WA ⊤ X ⋙ Over.forget X ⋙ H) Y := by
    intro X
    obtain ⟨Y, u, hY, _⟩ := resolvingClass_essentialConstancy WA H P' hres' hinv X
    exact ⟨Y, hY⟩
  let U := V.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := A)
  have hU : WB.IsInvertedBy U := by
    intro X Y f hf
    have : IsIso (DerivedCategory.Qh.map f) :=
      Localization.inverts DerivedCategory.Qh WB f hf
    exact (NatIso.isIso_map_iff V.mapDerivedCategoryFactorsh f).1 (by
      change IsIso (V.mapDerivedCategory.map (DerivedCategory.Qh.map f))
      infer_instance)
  have hR : ∀ K, ∃ X, IsEssentiallyConstantIndDiagram
      (MorphismProperty.Under.forget WB ⊤ K ⋙ Under.forget K ⋙ U) X :=
    fun K ↦ ⟨U.obj K, inverted_indDiagram WB U hU K⟩
  have hRF := isRightDerivedFunctor_of_inverts WB
    V.mapDerivedCategory V.mapDerivedCategoryFactorsh
  have hLF : F.IsLeftDerivedFunctor α WA := ⟨hα⟩
  obtain ⟨d, hd⟩ := exists_derived_adjunction_compatibility
    V E adj hR hL V.mapDerivedCategory F V.mapDerivedCategoryFactorsh.inv α hRF hLF
  refine ⟨d, ?_⟩
  intro K
  have hu := hd (q.obj K) ((E.mapHomotopyCategory (.up ℤ)).obj (q.obj K)) (𝟙 _)
  simp only [Functor.map_id, Adjunction.homEquiv_id] at hu
  erw [Category.comp_id] at hu
  have hαK := NatTrans.congr_app hαpre K
  change α.app (q.obj K) = _ at hαK
  let EK := (E.mapHomologicalComplex (.up ℤ)).obj K
  let η := (adj.mapHomologicalComplex (.up ℤ)).unit.app K
  have hαexpr : α.app (q.obj K) =
      F.map (i.hom.app K) ≫ ε.app K ≫
        (DerivedCategory.quotientCompQhIso B).inv.app EK := by
    rw [hαK]
    simp [αpre, α₀, j, Functor.mapHomotopyCategoryFactors, EK]
  have hf : V.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient B (.up ℤ)).obj EK) =
      V.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso B).hom.app EK) ≫
        V.mapDerivedCategoryFactors.hom.app EK ≫
        (DerivedCategory.quotientCompQhIso A).inv.app
          ((V.mapHomologicalComplex (.up ℤ)).obj EK) := by
    simpa [Functor.mapHomotopyCategoryFactors] using
      V.mapDerivedCategoryFactorsh_hom_app EK
  have hu' : d.unit.app (DerivedCategory.Qh.obj (q.obj K)) ≫
      V.mapDerivedCategory.map (F.map (i.hom.app K)) ≫
      V.mapDerivedCategory.map (ε.app K) ≫
      V.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso B).inv.app EK) ≫
      V.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient B (.up ℤ)).obj EK) =
      DerivedCategory.Qh.map (q.map η) := by
    have hh := congrArg (fun f ↦ f ≫
      V.mapDerivedCategoryFactorsh.hom.app
        ((E.mapHomotopyCategory (.up ℤ)).obj (q.obj K))) hu
    simp only [Adjunction.homEquiv_unit, hαexpr, Functor.map_comp,
      Category.assoc, Iso.inv_hom_id_app] at hh
    erw [Adjunction.mapHomotopyCategory_unit_app_quotient] at hh
    erw [Category.comp_id] at hh
    exact hh
  rw [hf] at hu'
  have hcancel :
      V.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso B).inv.app EK) ≫
      V.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso B).hom.app EK) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
  rw [reassoc_of% hcancel] at hu'
  have hn := d.unit.naturality (i.hom.app K)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  have hpost := congrArg (fun f ↦ f ≫
    (DerivedCategory.quotientCompQhIso A).hom.app
      ((V.mapHomologicalComplex (.up ℤ)).obj EK)) hu'
  simp only [Category.assoc, Iso.inv_hom_id_app] at hpost
  erw [Category.comp_id] at hpost
  erw [DerivedCategory.quotientCompQhIso_hom_naturality] at hpost
  apply (cancel_epi (i.hom.app K)).1
  rw [← Category.assoc, hn]
  simpa only [Category.assoc, q, i, EK, η, Functor.id_obj, Functor.comp_obj] using hpost

end CategoryTheory.Functor
