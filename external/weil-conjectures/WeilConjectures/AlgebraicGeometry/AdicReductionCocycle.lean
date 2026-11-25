/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
import all WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore

/-! # Cocycle for the canonical quotient reductions

Source: Stacks Project, Tags 06YY and 09C2, ordinary tensor balancing.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard derivedExtension derivedPull
  DerivedCategory.Q CategoryTheory.constantSheaf CategoryTheory.Functor.mapDerivedCategory
attribute [local irreducible] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  CochainComplex.IsKFlatTensor CochainComplex.IsKFlatIndependentCoefficients
attribute [local instance 10000] change_additive pull_additive SheafOfModules.instAbelian
attribute [local instance 10000] adicFiniteSectionModule

attribute [local irreducible] change pull

-- Transport the entire comparison before projecting to its component maps.
private def ordinaryComp
    {D : Type w} [SmallCategory D] {T : GrothendieckTopology D}
    {R S V : Sheaf T CommRingCat.{w}} (f : R ⟶ S) (g : S ⟶ V) (k : R ⟶ V)
    (e : k = f ≫ g) : change f ⋙ change g ≅ change k :=
  e.symm ▸ adicFiniteChangeComp f g

private theorem ordinaryComp_tensor
    {D : Type w} [SmallCategory D] {T : GrothendieckTopology D}
    {R S V : Sheaf T CommRingCat.{w}} (f : R ⟶ S) (g : S ⟶ V) (k : R ⟶ V)
    (e : k = f ≫ g) (M : Mod R) (U : Dᵒᵖ) (m : M.val.obj U) :
    ((ordinaryComp f g k e).hom.app M).val.app U
        (tensorSection g ((change f).obj M) U 1 (tensorSection f M U 1 m)) =
      tensorSection k M U 1 m := by
  subst k
  rw [ordinaryComp, adicFiniteChangeComp]
  simpa only [map_one, mul_one] using
    (adicFiniteChangeComp_existsUnique f g).exists.choose_spec M U 1 1 m

-- The three adjunctions reduce equality to successive insertions of one.
private theorem triple_tensor_ext
    {D : Type w} [SmallCategory D] {T : GrothendieckTopology D}
    {R S V W : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (g : S ⟶ V) (h : V ⟶ W) (M : Mod R) (N : Mod W)
    (a b : (change h).obj ((change g).obj ((change f).obj M)) ⟶ N)
    (hab : ∀ (U : Dᵒᵖ) (m : M.val.obj U),
      a.val.app U (tensorSection h _ U 1
        (tensorSection g _ U 1 (tensorSection f M U 1 m))) =
      b.val.app U (tensorSection h _ U 1
        (tensorSection g _ U 1 (tensorSection f M U 1 m)))) : a = b := by
  apply (adicFiniteHomEquiv h _ N).injective
  apply (adicFiniteHomEquiv g _ _).injective
  apply (adicFiniteHomEquiv f M _).injective
  apply SheafOfModules.hom_ext
  ext U m
  simpa only [adicFiniteHomEquiv_apply] using hab U m

private theorem ordinaryComp_cocycle
    {D : Type w} [SmallCategory D] {T : GrothendieckTopology D}
    {R S V W : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (g : S ⟶ V) (h : V ⟶ W)
    (fg : R ⟶ V) (efg : fg = f ≫ g) (gh : S ⟶ W) (egh : gh = g ≫ h)
    (k : R ⟶ W) (ek₁ : k = fg ≫ h) (ek₂ : k = f ≫ gh) (M : Mod R) :
    (change h).map ((ordinaryComp f g fg efg).hom.app M) ≫
        (ordinaryComp fg h k ek₁).hom.app M =
      (ordinaryComp g h gh egh).hom.app ((change f).obj M) ≫
        (ordinaryComp f gh k ek₂).hom.app M := by
  apply triple_tensor_ext f g h M _
  intro U m
  change ((ordinaryComp fg h k ek₁).hom.app M).val.app U
      (((change h).map ((ordinaryComp f g fg efg).hom.app M)).val.app U
        (tensorSection h _ U 1 (tensorSection g _ U 1 (tensorSection f M U 1 m)))) =
    ((ordinaryComp f gh k ek₂).hom.app M).val.app U
      (((ordinaryComp g h gh egh).hom.app ((change f).obj M)).val.app U
        (tensorSection h _ U 1 (tensorSection g _ U 1 (tensorSection f M U 1 m))))
  rw [tensorSection_map, ordinaryComp_tensor, ordinaryComp_tensor,
    ordinaryComp_tensor, ordinaryComp_tensor]

-- Naturality and the four computation squares reduce derived coherence to ordinary coherence.
private theorem paste_cocycle
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    (q₀ : C₀ ⥤ D₀) (q₁ : C₁ ⥤ D₁) (q₂ : C₂ ⥤ D₂) (q₃ : C₃ ⥤ D₃)
    (a : C₀ ⥤ C₁) (b : C₁ ⥤ C₂) (c : C₂ ⥤ C₃)
    (d : C₀ ⥤ C₂) (e : C₁ ⥤ C₃) (f : C₀ ⥤ C₃)
    (A : D₀ ⥤ D₁) (B : D₁ ⥤ D₂) (C : D₂ ⥤ D₃)
    (D : D₀ ⥤ D₂) (E : D₁ ⥤ D₃) (F : D₀ ⥤ D₃)
    (α : q₀ ⋙ A ⟶ a ⋙ q₁) (β : q₁ ⋙ B ⟶ b ⋙ q₂)
    (γ : q₂ ⋙ C ⟶ c ⋙ q₃) (δ : q₀ ⋙ D ⟶ d ⋙ q₂)
    (ε : q₁ ⋙ E ⟶ e ⋙ q₃) (φ : q₀ ⋙ F ⟶ f ⋙ q₃)
    (s : A ⋙ B ⟶ D) (t : B ⋙ C ⟶ E)
    (u : D ⋙ C ⟶ F) (v : A ⋙ E ⟶ F)
    (σ : a ⋙ b ⟶ d) (τ : b ⋙ c ⟶ e)
    (υ : d ⋙ c ⟶ f) (ν : a ⋙ e ⟶ f) (X : C₀)
    (hs : s.app (q₀.obj X) ≫ δ.app X =
      B.map (α.app X) ≫ β.app (a.obj X) ≫ q₂.map (σ.app X))
    (ht : t.app (q₁.obj (a.obj X)) ≫ ε.app (a.obj X) =
      C.map (β.app (a.obj X)) ≫ γ.app (b.obj (a.obj X)) ≫
        q₃.map (τ.app (a.obj X)))
    (hu : u.app (q₀.obj X) ≫ φ.app X =
      C.map (δ.app X) ≫ γ.app (d.obj X) ≫ q₃.map (υ.app X))
    (hv : v.app (q₀.obj X) ≫ φ.app X =
      E.map (α.app X) ≫ ε.app (a.obj X) ≫ q₃.map (ν.app X))
    (ho : c.map (σ.app X) ≫ υ.app X = τ.app (a.obj X) ≫ ν.app X)
    [Mono (φ.app X)] :
    C.map (s.app (q₀.obj X)) ≫ u.app (q₀.obj X) =
      t.app (A.obj (q₀.obj X)) ≫ v.app (q₀.obj X) := by
  have hSC := congrArg C.map hs
  simp only [Functor.map_comp] at hSC
  have hγ := γ.naturality (σ.app X)
  simp only [Functor.comp_map] at hγ
  have htα := t.naturality (α.app X)
  simp only [Functor.comp_map] at htα
  apply (cancel_mono (φ.app X)).1
  calc
    _ = C.map (s.app (q₀.obj X)) ≫
        (C.map (δ.app X) ≫ γ.app (d.obj X) ≫ q₃.map (υ.app X)) := by
      rw [Category.assoc, hu]
    _ = C.map (B.map (α.app X)) ≫ C.map (β.app (a.obj X)) ≫
        C.map (q₂.map (σ.app X)) ≫ γ.app (d.obj X) ≫ q₃.map (υ.app X) := by
      simpa only [Category.assoc, Functor.comp_obj] using
        congrArg (fun z ↦ z ≫ γ.app (d.obj X) ≫ q₃.map (υ.app X)) hSC
    _ = C.map (B.map (α.app X)) ≫ C.map (β.app (a.obj X)) ≫
        γ.app (b.obj (a.obj X)) ≫ q₃.map (c.map (σ.app X)) ≫
          q₃.map (υ.app X) := by
      simpa only [Category.assoc, Functor.comp_obj] using congrArg
        (fun z ↦ C.map (B.map (α.app X)) ≫ C.map (β.app (a.obj X)) ≫
          z ≫ q₃.map (υ.app X)) hγ
    _ = C.map (B.map (α.app X)) ≫ C.map (β.app (a.obj X)) ≫
        γ.app (b.obj (a.obj X)) ≫ q₃.map (τ.app (a.obj X)) ≫
          q₃.map (ν.app X) := by
      rw [← q₃.map_comp, ho, q₃.map_comp]
    _ = C.map (B.map (α.app X)) ≫ t.app (q₁.obj (a.obj X)) ≫
        ε.app (a.obj X) ≫ q₃.map (ν.app X) := by
      simpa only [Category.assoc, Functor.comp_obj] using congrArg
        (fun z ↦ C.map (B.map (α.app X)) ≫ z ≫ q₃.map (ν.app X)) ht.symm
    _ = t.app (A.obj (q₀.obj X)) ≫ E.map (α.app X) ≫
        ε.app (a.obj X) ≫ q₃.map (ν.app X) := by
      simpa only [Category.assoc, Functor.comp_obj] using congrArg
        (fun z ↦ z ≫ ε.app (a.obj X) ≫ q₃.map (ν.app X)) htα
    _ = _ := by rw [Category.assoc, hv]

private theorem specified_extend_formula
    {D : Type w} [SmallCategory D] {T : GrothendieckTopology D}
    {R S V : Sheaf T CommRingCat.{w}} (f : R ⟶ S) (g : S ⟶ V) (k : R ⟶ V)
    (e : k = f ≫ g) (P : Cx R)
    (hk : CochainComplex.IsKFlatIndependentCoefficients (J := T) (R := R) P) :
    (adicFiniteExtendComp f g k e).hom.app ((Q R).obj P) ≫
        (extendComparison k).app P =
      (extend g).map ((extendComparison f).app P) ≫
        (extendComparison g).app (((change f).mapHomologicalComplex (.up ℤ)).obj P) ≫
        (Q V).map ((Functor.mapHomologicalComplexCompIso
          (ordinaryComp f g k e) (.up ℤ)).hom.app P) := by
  subst k
  simpa only [adicFiniteExtendComp, ordinaryComp, eqToIso_refl, Iso.trans_refl,
    adicFiniteExtendCompFormula] using
    (adicFiniteExtendComp_existsUnique f g).exists.choose_spec P hk

private theorem complex_cocycle
    {D : Type w} [SmallCategory D] {T : GrothendieckTopology D}
    {R S V W : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (g : S ⟶ V) (h : V ⟶ W)
    (fg : R ⟶ V) (efg : fg = f ≫ g) (gh : S ⟶ W) (egh : gh = g ≫ h)
    (k : R ⟶ W) (ek₁ : k = fg ≫ h) (ek₂ : k = f ≫ gh) (P : Cx R) :
    ((change h).mapHomologicalComplex (.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso
          (ordinaryComp f g fg efg) (.up ℤ)).hom.app P) ≫
      (Functor.mapHomologicalComplexCompIso (ordinaryComp fg h k ek₁) (.up ℤ)).hom.app P =
    (Functor.mapHomologicalComplexCompIso (ordinaryComp g h gh egh) (.up ℤ)).hom.app
        (((change f).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (Functor.mapHomologicalComplexCompIso (ordinaryComp f gh k ek₂) (.up ℤ)).hom.app P := by
  apply HomologicalComplex.hom_ext
  intro i
  exact ordinaryComp_cocycle f g h fg efg gh egh k ek₁ ek₂ (P.X i)

private theorem sheaf_cocycle
    {D : Type w} [SmallCategory D] {T : GrothendieckTopology D}
    {R S V W : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (g : S ⟶ V) (h : V ⟶ W)
    (fg : R ⟶ V) (efg : fg = f ≫ g) (gh : S ⟶ W) (egh : gh = g ≫ h)
    (k : R ⟶ W) (ek₁ : k = fg ≫ h) (ek₂ : k = f ≫ gh) (N : ConstantCompletion.D R) :
    (extend h).map ((adicFiniteExtendComp f g fg efg).hom.app N) ≫
        (adicFiniteExtendComp fg h k ek₁).hom.app N =
      (adicFiniteExtendComp g h gh egh).hom.app ((extend f).obj N) ≫
        (adicFiniteExtendComp f gh k ek₂).hom.app N := by
  let := HasDerivedCategory.standard (Mod R)
  let lhs : extend f ⋙ extend g ⋙ extend h ⟶ extend k :=
    Functor.whiskerRight (adicFiniteExtendComp f g fg efg).hom (extend h) ≫
      (adicFiniteExtendComp fg h k ek₁).hom
  let rhs : extend f ⋙ extend g ⋙ extend h ⟶ extend k :=
    Functor.whiskerLeft (extend f) (adicFiniteExtendComp g h gh egh).hom ≫
      (adicFiniteExtendComp f gh k ek₂).hom
  have he : lhs = rhs := by
    apply resolving_nat_ext (AdicFiniteGood R) adicFiniteGood_resolution lhs rhs
    intro P hp
    have hpf := adicFiniteGood_change f P hp
    have hk := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hp.kflat
    have hkf := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).2 hpf.kflat
    have : IsIso ((extendComparison k).app P) :=
      adicFiniteExtension_isIso k P hp.kflat
    exact paste_cocycle (Q R) (Q S) (Q V) (Q W)
      ((change f).mapHomologicalComplex (.up ℤ))
      ((change g).mapHomologicalComplex (.up ℤ))
      ((change h).mapHomologicalComplex (.up ℤ))
      ((change fg).mapHomologicalComplex (.up ℤ))
      ((change gh).mapHomologicalComplex (.up ℤ))
      ((change k).mapHomologicalComplex (.up ℤ))
      (extend f) (extend g) (extend h) (extend fg) (extend gh) (extend k)
      (extendComparison f) (extendComparison g) (extendComparison h)
      (extendComparison fg) (extendComparison gh) (extendComparison k)
      (adicFiniteExtendComp f g fg efg).hom (adicFiniteExtendComp g h gh egh).hom
      (adicFiniteExtendComp fg h k ek₁).hom (adicFiniteExtendComp f gh k ek₂).hom
      (Functor.mapHomologicalComplexCompIso (ordinaryComp f g fg efg) (.up ℤ)).hom
      (Functor.mapHomologicalComplexCompIso (ordinaryComp g h gh egh) (.up ℤ)).hom
      (Functor.mapHomologicalComplexCompIso (ordinaryComp fg h k ek₁) (.up ℤ)).hom
      (Functor.mapHomologicalComplexCompIso (ordinaryComp f gh k ek₂) (.up ℤ)).hom P
      (specified_extend_formula f g fg efg P hk)
      (specified_extend_formula g h gh egh _ hkf)
      (specified_extend_formula fg h k ek₁ P hk)
      (specified_extend_formula f gh k ek₂ P hk)
      (complex_cocycle f g h fg efg gh egh k ek₁ ek₂ P)
  simpa only [lhs, rhs, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] using congrArg (fun z ↦ z.app N) he

private theorem transfer_cocycle
    {C₀ C₁ C₂ C₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    (a : C₀ ⥤ C₁) (b : C₁ ⥤ C₂) (c : C₂ ⥤ C₃)
    (d : C₀ ⥤ C₂) (e : C₁ ⥤ C₃) (f : C₀ ⥤ C₃)
    (s s' : a ⋙ b ≅ d) (t t' : b ⋙ c ≅ e)
    (u u' : d ⋙ c ≅ f) (v v' : a ⋙ e ≅ f)
    (hs : s = s') (ht : t = t') (hu : u = u') (hv : v = v') (N : C₀)
    (hc : c.map (s'.hom.app N) ≫ u'.hom.app N =
      t'.hom.app (a.obj N) ≫ v'.hom.app N) :
    c.map (s.hom.app N) ≫ u.hom.app N = t.hom.app (a.obj N) ≫ v.hom.app N := by
  subst s'
  subst t'
  subst u'
  subst v'
  exact hc

private theorem ring_cocycle
    {D : Type w} [SmallCategory D] (T : GrothendieckTopology D)
    {A B C E : Type w} [CommRing A] [CommRing B] [CommRing C] [CommRing E]
    (f : A →+* B) (g : B →+* C) (h : C →+* E)
    {fg : A →+* C} (efg : fg = g.comp f)
    {gh : B →+* E} (egh : gh = h.comp g)
    {k : A →+* E} (ek₁ : k = h.comp fg) (ek₂ : k = gh.comp f)
    (N : ConstantCompletion.D (constant T A)) :
    (adicFiniteExtension T h).map
        ((adicFiniteExtensionComp T f g fg efg).hom.app N) ≫
      (adicFiniteExtensionComp T fg h k ek₁).hom.app N =
    (adicFiniteExtensionComp T g h gh egh).hom.app
        ((adicFiniteExtension T f).obj N) ≫
      (adicFiniteExtensionComp T f gh k ek₂).hom.app N := by
  exact transfer_cocycle
    (adicFiniteExtension T f) (adicFiniteExtension T g) (adicFiniteExtension T h)
    (adicFiniteExtension T fg) (adicFiniteExtension T gh) (adicFiniteExtension T k)
    (adicFiniteExtensionComp T f g fg efg)
    (adicFiniteExtendComp _ _ _ (adicFiniteConstantComp T f g fg efg))
    (adicFiniteExtensionComp T g h gh egh)
    (adicFiniteExtendComp _ _ _ (adicFiniteConstantComp T g h gh egh))
    (adicFiniteExtensionComp T fg h k ek₁)
    (adicFiniteExtendComp _ _ _ (adicFiniteConstantComp T fg h k ek₁))
    (adicFiniteExtensionComp T f gh k ek₂)
    (adicFiniteExtendComp _ _ _ (adicFiniteConstantComp T f gh k ek₂))
    rfl rfl rfl rfl N
    (sheaf_cocycle (adicFiniteConstantMap f T) (adicFiniteConstantMap g T)
      (adicFiniteConstantMap h T) _ (adicFiniteConstantComp T f g fg efg)
      _ (adicFiniteConstantComp T g h gh egh)
      _ (adicFiniteConstantComp T fg h k ek₁) (adicFiniteConstantComp T f gh k ek₂) N)

private theorem iso_cocycle_of_components
    {C₀ C₁ C₂ C₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    (a : C₀ ⥤ C₁) (b : C₁ ⥤ C₂) (c : C₂ ⥤ C₃)
    (d : C₀ ⥤ C₂) (e : C₁ ⥤ C₃) (f : C₀ ⥤ C₃)
    (s : a ⋙ b ≅ d) (t : b ⋙ c ≅ e) (u : d ⋙ c ≅ f) (v : a ⋙ e ≅ f)
    (hc : ∀ N, c.map (s.hom.app N) ≫ u.hom.app N =
      t.hom.app (a.obj N) ≫ v.hom.app N) :
    Functor.isoWhiskerRight s c ≪≫ u =
      Functor.associator a b c ≪≫ Functor.isoWhiskerLeft a t ≪≫ v := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  simpa only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] using hc N

-- Keep whole isomorphisms across specialization of the coefficient universe.
-- Taking projections first can make equal universe expressions trigger expensive unfolding.
private theorem ring_iso_cocycle
    {D : Type w} [SmallCategory D] (T : GrothendieckTopology D)
    {A B C E : Type w} [CommRing A] [CommRing B] [CommRing C] [CommRing E]
    (f : A →+* B) (g : B →+* C) (h : C →+* E)
    {fg : A →+* C} (efg : fg = g.comp f)
    {gh : B →+* E} (egh : gh = h.comp g)
    {k : A →+* E} (ek₁ : k = h.comp fg) (ek₂ : k = gh.comp f) :
    Functor.isoWhiskerRight (adicFiniteExtensionComp T f g fg efg) (adicFiniteExtension T h) ≪≫
        adicFiniteExtensionComp T fg h k ek₁ =
      Functor.associator (adicFiniteExtension T f) (adicFiniteExtension T g)
          (adicFiniteExtension T h) ≪≫
        Functor.isoWhiskerLeft (adicFiniteExtension T f) (adicFiniteExtensionComp T g h gh egh) ≪≫
          adicFiniteExtensionComp T f gh k ek₂ := by
  exact iso_cocycle_of_components
    (adicFiniteExtension T f) (adicFiniteExtension T g) (adicFiniteExtension T h)
    (adicFiniteExtension T fg) (adicFiniteExtension T gh) (adicFiniteExtension T k)
    (adicFiniteExtensionComp T f g fg efg) (adicFiniteExtensionComp T g h gh egh)
    (adicFiniteExtensionComp T fg h k ek₁) (adicFiniteExtensionComp T f gh k ek₂)
    (ring_cocycle T f g h efg egh ek₁ ek₂)

private theorem replace_reduction_components
    {C₀ C₁ C₂ C₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    (a : C₀ ⥤ C₁) (b : C₁ ⥤ C₂) (c : C₂ ⥤ C₃)
    (d : C₀ ⥤ C₂) (e : C₁ ⥤ C₃) (f : C₀ ⥤ C₃)
    (s : a ⋙ b ≅ d) (t : b ⋙ c ≅ e) (u : d ⋙ c ≅ f) (v : a ⋙ e ≅ f)
    (N : C₀) (Nr : C₁) (Nm : C₂) (Nn : C₃)
    (er : Nr = a.obj N) (em : Nm = d.obj N) (en : Nn = f.obj N)
    (ρ₁ : b.obj Nr ≅ Nm) (ρ₂ : c.obj Nm ≅ Nn) (ρ₃ : e.obj Nr ≅ Nn)
    (h₁ : HEq ρ₁ (s.app N)) (h₂ : HEq ρ₂ (u.app N)) (h₃ : HEq ρ₃ (v.app N))
    (hc : Functor.isoWhiskerRight s c ≪≫ u =
      Functor.associator a b c ≪≫ Functor.isoWhiskerLeft a t ≪≫ v) :
    c.map ρ₁.hom ≫ ρ₂.hom = t.hom.app Nr ≫ ρ₃.hom := by
  subst Nr
  subst Nm
  subst Nn
  cases h₁
  cases h₂
  cases h₃
  have hh := congrArg (fun z : (a ⋙ b) ⋙ c ≅ f ↦ z.hom.app N) hc
  simpa only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, Iso.app_hom] using hh

private theorem reduction_eq (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (N : adicFiniteAmbient.{u, v} X A) (n : ℕ) :
    adicFiniteReduction.{u, v} X J N n =
      (adicFiniteExtension (coefficientProEtaleModelTopology.{u, v} X)
        (adicFiniteQuotient J n)).obj N := by
  rfl

private theorem rho_eq (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (N : adicFiniteAmbient.{u, v} X A) {m n : ℕ} (h : n ≤ m) :
    adicFiniteRho.{u, v} X J N h =
      (adicFiniteExtensionComp (coefficientProEtaleModelTopology.{u, v} X)
        (adicFiniteQuotient J m) (adicFiniteFactor J h) (adicFiniteQuotient J n)
        (adicFiniteQuotientComp J h)).app N := by
  rfl

/-- The canonical quotient reassociations obey their cocycle before any descent.
Source: Stacks Project, Tag 09C2, repeated quotient tensor computations; parent
proof steps 1 and 4. (auxiliary; not a blueprint node).

Proof: resolve N by a flat-term K-flat complex P. Successive scalar extensions
are computed on the successive ordinary extensions of P. Use the normalization
adicFiniteExtendCompFormula for each reassociation and cancel the invertible
computation maps. Both resulting ordinary chain maps send
(((p tensor x) tensor y) tensor z) to
p tensor q(r,n)(x) * q(m,n)(y) * z. They agree by associativity of multiplication
and the quotient factor identities. Sheafification preserves this equality.
Transport along the resolution isomorphism by naturality. The same calculation
includes equal indices, where the quotient factor is the identity. -/
theorem adicReduction_cocycle (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (N : adicFiniteAmbient.{u, v} X A)
    (r m n : ℕ) (hnm : n ≤ m) (hmr : m ≤ r) :
    (adicFiniteExtension (coefficientProEtaleModelTopology.{u, v} X)
      (adicFiniteFactor J hnm)).map (adicFiniteRho.{u, v} X J N hmr).hom ≫
        (adicFiniteRho.{u, v} X J N hnm).hom =
      (adicFiniteExtensionComp (coefficientProEtaleModelTopology.{u, v} X)
        (adicFiniteFactor J hmr) (adicFiniteFactor J hnm)
        (adicFiniteFactor J (hnm.trans hmr)) (adicFiniteFactorComp J hnm hmr)).hom.app
          (adicFiniteReduction.{u, v} X J N r) ≫
        (adicFiniteRho.{u, v} X J N (hnm.trans hmr)).hom := by
  exact replace_reduction_components
    (adicFiniteExtension (coefficientProEtaleModelTopology.{u, v} X) (adicFiniteQuotient J r))
    (adicFiniteExtension (coefficientProEtaleModelTopology.{u, v} X) (adicFiniteFactor J hmr))
    (adicFiniteExtension (coefficientProEtaleModelTopology.{u, v} X) (adicFiniteFactor J hnm))
    (adicFiniteExtension (coefficientProEtaleModelTopology.{u, v} X) (adicFiniteQuotient J m))
    (adicFiniteExtension (coefficientProEtaleModelTopology.{u, v} X)
      (adicFiniteFactor J (hnm.trans hmr)))
    (adicFiniteExtension (coefficientProEtaleModelTopology.{u, v} X) (adicFiniteQuotient J n))
    (adicFiniteExtensionComp (coefficientProEtaleModelTopology.{u, v} X)
      _ _ _ (adicFiniteQuotientComp J hmr))
    (adicFiniteExtensionComp (coefficientProEtaleModelTopology.{u, v} X)
      _ _ _ (adicFiniteFactorComp J hnm hmr))
    (adicFiniteExtensionComp (coefficientProEtaleModelTopology.{u, v} X)
      _ _ _ (adicFiniteQuotientComp J hnm))
    (adicFiniteExtensionComp (coefficientProEtaleModelTopology.{u, v} X)
      _ _ _ (adicFiniteQuotientComp J (hnm.trans hmr)))
    N (adicFiniteReduction.{u, v} X J N r) (adicFiniteReduction.{u, v} X J N m)
    (adicFiniteReduction.{u, v} X J N n)
    (reduction_eq.{u, v} X J N r) (reduction_eq.{u, v} X J N m)
    (reduction_eq.{u, v} X J N n)
    (adicFiniteRho.{u, v} X J N hmr) (adicFiniteRho.{u, v} X J N hnm)
    (adicFiniteRho.{u, v} X J N (hnm.trans hmr))
    (heq_of_eq (rho_eq.{u, v} X J N hmr)) (heq_of_eq (rho_eq.{u, v} X J N hnm))
    (heq_of_eq (rho_eq.{u, v} X J N (hnm.trans hmr)))
    (ring_iso_cocycle (coefficientProEtaleModelTopology.{u, v} X)
      (adicFiniteQuotient J r) (adicFiniteFactor J hmr) (adicFiniteFactor J hnm)
      (adicFiniteQuotientComp J hmr) (adicFiniteFactorComp J hnm hmr)
      (adicFiniteQuotientComp J hnm) (adicFiniteQuotientComp J (hnm.trans hmr)))

end AlgebraicGeometry.Scheme
