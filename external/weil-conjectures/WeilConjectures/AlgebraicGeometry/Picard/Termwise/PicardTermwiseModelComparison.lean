/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PicardTermwiseModels
public import WeilConjectures.AlgebraicGeometry.PicardOrdinaryModelCycles
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.PicardDerivedModelSections
import WeilConjectures.AlgebraicGeometry.Picard.Termwise.PicardTermwiseSourceCoherence
import WeilConjectures.AlgebraicGeometry.Picard.Termwise.PicardTermwiseTargetCoherence

/-! # Termwise model comparisons before imposing connectivity

## References

* Stacks Project, Tags 06YJ and 0D5S
* Stacks Project, Tag 08DW
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- Transport naturality across independent source and target comparison squares. -/
private theorem picard_comparison_transport
    {C₀ C₁ D₀ D₁ : Type*} [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    (Q : C₀ ⥤ D₀) (Q' : C₁ ⥤ D₁) (L : D₀ ⥤ D₁) (F : C₀ ⥤ C₁)
    (η : Q ⋙ L ⟶ F ⋙ Q')
    {A B : D₀} {A' B' : D₁} {X Y : C₀} {X' Y' : C₁}
    (cA : A' ≅ L.obj A) (cB : B' ≅ L.obj B)
    (a : A ≅ Q.obj X) (b : B ≅ Q.obj Y)
    (a' : A' ≅ Q'.obj X') (b' : B' ≅ Q'.obj Y')
    (u : X' ≅ F.obj X) (w : Y' ≅ F.obj Y)
    (ha : a'.hom ≫ Q'.map u.hom = cA.hom ≫ L.map a.hom ≫ η.app X)
    (hb : b'.hom ≫ Q'.map w.hom = cB.hom ≫ L.map b.hom ≫ η.app Y)
    (f : X ⟶ Y) :
    cA.hom ≫ L.map (a.hom ≫ Q.map f ≫ b.inv) ≫ cB.inv =
      a'.hom ≫ Q'.map (u.hom ≫ F.map f ≫ w.inv) ≫ b'.inv := by
  have hn := η.naturality f
  change L.map (Q.map f) ≫ η.app Y = η.app X ≫ Q'.map (F.map f) at hn
  have hb' := congrArg
    (fun z ↦ L.map b.inv ≫ cB.inv ≫ z ≫ Q'.map w.inv ≫ b'.inv) hb
  simp only [Category.assoc, cB.inv_hom_id_assoc] at hb'
  rw [← Q'.map_comp_assoc w.hom w.inv, w.hom_inv_id, Q'.map_id] at hb'
  simp only [Category.id_comp, b'.hom_inv_id, Category.comp_id] at hb'
  rw [← L.map_comp_assoc b.inv b.hom, b.inv_hom_id, L.map_id, Category.id_comp] at hb'
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc a'.hom, ha]
  simp only [Category.assoc]
  rw [← reassoc_of% hn, hb']

-- The pinned comparison families elaborate large derived-category functor expressions.
/-- Source and target object comparisons can be chosen simultaneously, so that
restriction of a localized chain map is represented by a chain map whose zeroth
component is ordinary tensor restriction. No connectivity is assumed: this theorem
computes objects and the restriction of already given chain maps, not all derived
morphisms. The degree-zero source identification is included explicitly. -/
theorem picard_termwise_model_comparison
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (U : W.Opens)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K)) :
    ∃ (a : ∀ {T : Scheme.{v}} (t : T ⟶ W),
        (derivedPullback t).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings W.toRingedSpace)) 0).obj
            (SheafOfModules.unit (moduleRings W.toRingedSpace))) ≅
          DerivedCategory.Q.obj (picardTermwiseSource t))
      (b : ∀ {T : Scheme.{v}} (t : T ⟶ W) (s : T ⟶ U.toScheme),
        s ≫ U.ι = t →
          ((derivedPullback t).obj E ≅
            DerivedCategory.Q.obj (picardTermwiseModel W U K s))),
      ∀ {T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
        (s : T ⟶ U.toScheme) (s' : T' ⟶ U.toScheme)
        (ht : i ≫ t = t') (hs : i ≫ s = s')
        (hf : s ≫ U.ι = t) (hf' : s' ≫ U.ι = t')
        (f : picardTermwiseSource t ⟶ picardTermwiseModel W U K s),
      ∃ f' : picardTermwiseSource t' ⟶ picardTermwiseModel W U K s',
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫ f'.f 0 =
          picardOrdinaryModelRestriction W U K i t t' s s' ht hs
            ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫ f.f 0) ∧
        picardDerivedModelRestriction E i t t' ht
            ((a t).hom ≫ DerivedCategory.Q.map f ≫ (b t s hf).inv) =
          (a t').hom ≫ DerivedCategory.Q.map f' ≫ (b t' s' hf').inv := by
  obtain ⟨b, hb⟩ := picard_termwise_target_coherence W E U K hK hE
  refine ⟨fun t ↦ picardTermwiseSourceIso t, b, ?_⟩
  intro T T' i t t' s s' ht hs hf hf' f
  let : (Modules.tensorPullback i).Additive :=
    (Classical.choose (Modules.exists_tensorPullbackAdjunction i)).left_adjoint_additive
  let F := (Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)
  let u := picardTermwiseSourceRestrictionIso i t t' ht
  let w := picardTermwiseModelRestrictionIso W U K i s s' hs
  let f' := u.hom ≫ F.map f ≫ w.inv
  refine ⟨f', ?_, ?_⟩
  · let ct := Modules.tensorPullbackCompositionIso i t t' ht
    let cs := Modules.tensorPullbackCompositionIso i s s' hs
    change (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫ f'.f 0 =
      ct.hom.app _ ≫ (Modules.tensorPullback i).map
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫ f.f 0) ≫ cs.inv.app _
    simp [f', u, w, F, picardTermwiseSourceRestrictionIso,
      picardTermwiseModelRestrictionIso,
      Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
      NatTrans.mapHomologicalComplex, Category.assoc]
    simp [CochainComplex.singleFunctor,
      HomologicalComplex.single_map_f_self, Category.assoc]
    rfl
  · let c := (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) i t ≪≫
        eqToIso (congrArg (fun g : T' ⟶ W ↦ derivedPullback g) ht)
    have hu := picard_termwise_source_coherence i t t' ht
    have hw := hb i t t' s s' ht hs hf hf'
    change (picardTermwiseSourceIso t').hom ≫ DerivedCategory.Q.map u.hom =
      c.inv.app _ ≫ (derivedPullback i).map (picardTermwiseSourceIso t).hom ≫
        (picardTermwiseCounit i).app (picardTermwiseSource t) at hu
    change (b t' s' hf').hom ≫ DerivedCategory.Q.map w.hom =
      c.inv.app E ≫ (derivedPullback i).map (b t s hf).hom ≫
        (picardTermwiseCounit i).app (picardTermwiseModel W U K s) at hw
    exact picard_comparison_transport DerivedCategory.Q DerivedCategory.Q
      (derivedPullback i) F (picardTermwiseCounit i)
      (c.app _).symm (c.app E).symm (picardTermwiseSourceIso t) (b t s hf)
      (picardTermwiseSourceIso t') (b t' s' hf') u w hu hw f

end
end AlgebraicGeometry.Scheme
