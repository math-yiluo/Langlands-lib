/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra

/-!
# Composition of right derived functors on categories of algebras

Let `F`, `G` be additive autoequivalences of abelian categories `C`, `D` in which coproducts
indexed by `ℤ` exist and are exact, and let `e : L ⋙ G ≅ F ⋙ L` transport an additive functor
`L : C ⥤ D` to the functor `mapOfNatIso e : IsoAlgebra F ⥤ IsoAlgebra G`.

The K-injective complexes of `IsoAlgebra F` are not detected on the underlying complexes, so
`mapOfNatIso e` need not preserve them even if `L` does. Nevertheless, the unit of the total
right derived functor of `mapOfNatIso e` is an isomorphism on every complex of algebras whose
underlying complex is K-injective
(`CategoryTheory.Endofunctor.IsoAlgebra.isIso_rightDerivedFunctorUnit_app_mapOfNatIso`): after
forgetting the algebra structures, the right derived functor of `mapOfNatIso e` is that of `L`.

Consequently, if `mapOfNatIso e₁` is followed by `mapOfNatIso e₂` and the underlying functor
`L₁` of the first one preserves K-injective complexes, the right derived functor of the
composite is the composite of the right derived functors
(`CategoryTheory.Endofunctor.IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompIso`).
-/

@[expose] public section

universe w w' w'' v v' v'' u u' u''

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

section Map

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E] {F : C ⥤ C} {G : D ⥤ D} {H : E ⥤ E}

/-- An isomorphism `α : L ≅ L'` compatible with commutation isomorphisms `e` and `e'` induces an
isomorphism `mapOfNatIso e ≅ mapOfNatIso e'` of the transported functors. -/
@[simps!]
noncomputable def mapOfNatIsoIsoOfIso {L L' : C ⥤ D} {e : L ⋙ G ≅ F ⋙ L}
    {e' : L' ⋙ G ≅ F ⋙ L'} (α : L ≅ L')
    (hα : Functor.whiskerRight α.hom G ≫ e'.hom = e.hom ≫ Functor.whiskerLeft F α.hom) :
    mapOfNatIso e ≅ mapOfNatIso e' where
  hom := mapOfNatIsoHom α.hom hα
  inv := mapOfNatIsoHom α.inv (by
    ext K
    have h := congr_app hα K
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h ⊢
    rw [← cancel_epi (G.map (α.hom.app K)), ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      Functor.map_id, Category.id_comp, reassoc_of% h]
    simp)
  hom_inv_id := by
    ext K : 2
    exact ObjectProperty.hom_ext _ (Algebra.Hom.ext (α.hom_inv_id_app K.carrier))
  inv_hom_id := by
    ext K : 2
    exact ObjectProperty.hom_ext _ (Algebra.Hom.ext (α.inv_hom_id_app K.carrier))

/-- The composite of the commutation isomorphisms `e₁ : L₁ ⋙ G ≅ F ⋙ L₁` and
`e₂ : L₂ ⋙ H ≅ G ⋙ L₂`, a commutation isomorphism for `L₁ ⋙ L₂`. -/
noncomputable def compCommIso {L₁ : C ⥤ D} {L₂ : D ⥤ E} (e₁ : L₁ ⋙ G ≅ F ⋙ L₁)
    (e₂ : L₂ ⋙ H ≅ G ⋙ L₂) : (L₁ ⋙ L₂) ⋙ H ≅ F ⋙ (L₁ ⋙ L₂) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft L₁ e₂ ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e₁ L₂ ≪≫ Functor.associator _ _ _

@[simp]
lemma compCommIso_hom_app {L₁ : C ⥤ D} {L₂ : D ⥤ E} (e₁ : L₁ ⋙ G ≅ F ⋙ L₁)
    (e₂ : L₂ ⋙ H ≅ G ⋙ L₂) (X : C) :
    (compCommIso e₁ e₂).hom.app X = e₂.hom.app (L₁.obj X) ≫ L₂.map (e₁.hom.app X) := by
  simp [compCommIso]

/-- Transporting along two commutation isomorphisms in turn is transporting along their
composite. -/
noncomputable def mapOfNatIsoCompIso {L₁ : C ⥤ D} {L₂ : D ⥤ E} (e₁ : L₁ ⋙ G ≅ F ⋙ L₁)
    (e₂ : L₂ ⋙ H ≅ G ⋙ L₂) :
    mapOfNatIso e₁ ⋙ mapOfNatIso e₂ ≅ mapOfNatIso (compCommIso e₁ e₂) :=
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ (Algebra.isoMk (Iso.refl _) (by
    simp [mapOfNatIso, Algebra.mapOfNatTrans])))
    (fun f ↦ ObjectProperty.hom_ext _ (Algebra.Hom.ext (by
      simp [mapOfNatIso, Algebra.mapOfNatTrans])))

end Map

section Unit

variable {D : Type u'} [Category.{v'} D] [Abelian D] {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  [HasColimitsOfShape (Discrete ℤ) D] [HasExactColimitsOfShape (Discrete ℤ) D]
  {E : Type u''} [Category.{v''} E] [Abelian E] {H : E ⥤ E} [H.Additive] [H.IsEquivalence]
  {L : D ⥤ E} [L.Additive] (e : L ⋙ H ≅ G ⋙ L)
  [HasDerivedCategory.{w'} (IsoAlgebra G)] [HasDerivedCategory.{w''} (IsoAlgebra H)]
  [HasDerivedCategory.{w'} D] [HasDerivedCategory.{w''} E]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra G)] [Abelian.HasKInjectiveResolutions D]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra H)]

omit [Abelian.HasKInjectiveResolutions (IsoAlgebra H)] in
/-- The derived functor of the exact forgetful functor of algebras reflects isomorphisms:
a morphism `f` of the derived category of algebras is an isomorphism if its image under the
derived forgetful functor is one. -/
lemma isIso_of_isIso_forget_mapDerivedCategory_map {K K' : DerivedCategory (IsoAlgebra H)}
    (f : K ⟶ K') [IsIso ((forget H).mapDerivedCategory.map f)] : IsIso f := by
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso ((forget H).map ((DerivedCategory.homologyFunctor _ n).map f)) :=
    (NatIso.isIso_map_iff ((forget H).mapDerivedCategoryHomologyFunctorIso n) f).2
      (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ (forget H)

/-- The unit of the total right derived functor of `mapOfNatIso e` is an isomorphism on a
complex of algebras whose underlying complex is K-injective. -/
lemma isIso_rightDerivedFunctorUnit_app_mapOfNatIso (Y : CochainComplex (IsoAlgebra G) ℤ)
    [CochainComplex.IsKInjective (((forget G).mapHomologicalComplex (ComplexShape.up ℤ)).obj Y)] :
    IsIso ((mapOfNatIso e).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj Y)) := by
  -- two right derived functors of `(mapOfNatIso e ⋙ For).mapHomotopyCategory ⋙ Qh`
  let Φ := (mapOfNatIso e ⋙ forget H).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh
  let α₁ := Functor.rightDerivedFunctorCompUnit (mapOfNatIso e) (forget H)
  have := Functor.isRightDerivedFunctor_rightDerivedFunctor_comp_of_exact (mapOfNatIso e)
    (forget H)
  let ι : Φ ≅ (forget G ⋙ L).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
    Functor.isoWhiskerRight
      { hom := NatTrans.mapHomotopyCategory (mapOfNatIsoCompForgetIso e).hom _
        inv := NatTrans.mapHomotopyCategory (mapOfNatIsoCompForgetIso e).inv _
        hom_inv_id := by
          rw [← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
            NatTrans.mapHomotopyCategory_id]
        inv_hom_id := by
          rw [← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
            NatTrans.mapHomotopyCategory_id] } _
  let α₂ : Φ ⟶ DerivedCategory.Qh ⋙ ((forget G).rightDerivedFunctor ⋙ L.rightDerivedFunctor) :=
    ι.hom ≫ Functor.rightDerivedFunctorCompUnit (forget G) L
  have : ((forget G).rightDerivedFunctor ⋙ L.rightDerivedFunctor).IsRightDerivedFunctor α₂
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) := by
    refine (HomotopyCategory.KInjectives.localizerMorphism_derives
      Φ).isRightDerivedFunctor_of_isIso _ (fun X₁ ↦ ?_)
    obtain ⟨K, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X₁
    have := (HomotopyCategory.KInjectives.localizerMorphism_derives
      ((forget G ⋙ L).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh)).isIso_of_isRightDerivedFunctor
        (Functor.rightDerivedFunctorCompUnit (forget G) L) (HomotopyCategory.KInjectives.mk K)
    exact IsIso.comp_isIso (f := ι.hom.app _)
  set W := HomotopyCategory.quasiIso (IsoAlgebra G) (ComplexShape.up ℤ)
  set qY := (HomotopyCategory.quotient (IsoAlgebra G) (ComplexShape.up ℤ)).obj Y
  let d := ((mapOfNatIso e).rightDerivedFunctor ⋙ (forget H).rightDerivedFunctor).rightDerivedDesc
    α₁ W _ α₂
  have : IsIso d := (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _ α₁ W _ α₂).1
    inferInstance
  have hfac := Functor.rightDerived_fac_app _ α₁ W _ α₂ qY
  have h₂ : IsIso (α₂.app qY) := by
    have : IsIso (L.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
        (((forget G).mapHomologicalComplex _).obj Y))) := inferInstance
    have : IsIso (L.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
          (((forget G).mapHomologicalComplex (ComplexShape.up ℤ)).obj qY.as))) := this
    dsimp [α₂, Functor.rightDerivedFunctorCompUnit]
    infer_instance
  have h₁ : IsIso (α₁.app qY) := by
    rw [← hfac] at h₂
    exact IsIso.of_isIso_comp_right _ (d.app _)
  dsimp [α₁, Functor.rightDerivedFunctorCompUnit] at h₁
  simp only [Category.id_comp, Category.comp_id, isIso_comp_left_iff] at h₁
  have h₃ : IsIso ((forget H).mapDerivedCategory.map
      ((mapOfNatIso e).rightDerivedFunctorUnit.app qY)) :=
    (NatIso.isIso_map_iff (forget H).rightDerivedFunctorIsoMapDerivedCategory _).1 h₁
  exact isIso_of_isIso_forget_mapDerivedCategory_map _

end Unit

section Comp

variable {C : Type u} [Category.{v} C] [Abelian C] {F : C ⥤ C} [F.Additive] [F.IsEquivalence]
  [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
  {D : Type u'} [Category.{v'} D] [Abelian D] {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  [HasColimitsOfShape (Discrete ℤ) D] [HasExactColimitsOfShape (Discrete ℤ) D]
  {E : Type u''} [Category.{v''} E] [Abelian E] {H : E ⥤ E} [H.Additive] [H.IsEquivalence]
  {L₁ : C ⥤ D} [L₁.Additive] (e₁ : L₁ ⋙ G ≅ F ⋙ L₁)
  {L₂ : D ⥤ E} [L₂.Additive] (e₂ : L₂ ⋙ H ≅ G ⋙ L₂)
  [HasDerivedCategory.{w} (IsoAlgebra F)] [HasDerivedCategory.{w'} (IsoAlgebra G)]
  [HasDerivedCategory.{w''} (IsoAlgebra H)]
  [HasDerivedCategory.{w'} D] [HasDerivedCategory.{w''} E]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra F)]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra G)] [Abelian.HasKInjectiveResolutions D]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra H)]
  [HasDerivedCategory.{w} C] [Abelian.HasKInjectiveResolutions C]
  [L₁.PreservesKInjectiveComplexes]

/-- If the underlying functor `L₁` of `mapOfNatIso e₁` preserves K-injective complexes, then
`R(mapOfNatIso e₁) ⋙ R(mapOfNatIso e₂)`, with the composite unit, is a right derived functor
of `mapOfNatIso e₁ ⋙ mapOfNatIso e₂`: on a K-injective complex `K` of algebras, the underlying
complex of `mapOfNatIso e₁` applied to `K` is `L₁` applied to the K-injective underlying
complex of `K`, on which the unit of `R(mapOfNatIso e₂)` is an isomorphism. -/
instance isRightDerivedFunctor_rightDerivedFunctor_comp_mapOfNatIso :
    ((mapOfNatIso e₁).rightDerivedFunctor ⋙
      (mapOfNatIso e₂).rightDerivedFunctor).IsRightDerivedFunctor
      (Functor.rightDerivedFunctorCompUnit (mapOfNatIso e₁) (mapOfNatIso e₂))
      (HomotopyCategory.quasiIso (IsoAlgebra F) (ComplexShape.up ℤ)) := by
  refine (HomotopyCategory.KInjectives.localizerMorphism_derives
    ((mapOfNatIso e₁ ⋙ mapOfNatIso e₂).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)).isRightDerivedFunctor_of_isIso _ (fun X₁ => ?_)
  obtain ⟨K, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X₁
  change IsIso ((Functor.rightDerivedFunctorCompUnit (mapOfNatIso e₁) (mapOfNatIso e₂)).app
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
  have h₁ : IsIso ((mapOfNatIso e₁).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) := inferInstance
  have : CochainComplex.IsKInjective ((L₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := inferInstance
  have : CochainComplex.IsKInjective (((forget G).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((mapOfNatIso e₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := this
  have h₂ := isIso_rightDerivedFunctorUnit_app_mapOfNatIso e₂
    (((mapOfNatIso e₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  have h₂' : IsIso ((mapOfNatIso e₂).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient (IsoAlgebra G) (ComplexShape.up ℤ)).obj
        (((mapOfNatIso e₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient (IsoAlgebra F) (ComplexShape.up ℤ)).obj K).as))) := h₂
  dsimp [Functor.rightDerivedFunctorCompUnit]
  infer_instance

/-- The composition isomorphism `R(mapOfNatIso e₁ ⋙ mapOfNatIso e₂) ≅
R(mapOfNatIso e₁) ⋙ R(mapOfNatIso e₂)`, when `L₁` preserves K-injective complexes. -/
noncomputable def rightDerivedFunctorMapOfNatIsoCompIso :
    (mapOfNatIso e₁ ⋙ mapOfNatIso e₂).rightDerivedFunctor ≅
      (mapOfNatIso e₁).rightDerivedFunctor ⋙ (mapOfNatIso e₂).rightDerivedFunctor :=
  Functor.rightDerivedUnique _ _ (mapOfNatIso e₁ ⋙ mapOfNatIso e₂).rightDerivedFunctorUnit
    (Functor.rightDerivedFunctorCompUnit (mapOfNatIso e₁) (mapOfNatIso e₂))
    (HomotopyCategory.quasiIso (IsoAlgebra F) (ComplexShape.up ℤ))

end Comp

end CategoryTheory.Endofunctor.IsoAlgebra
