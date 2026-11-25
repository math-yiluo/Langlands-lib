/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportNormalizationData
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.BaseChangeCube
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper

/-!
# The graph comparison under geometric base change

Source: SGA 4 XVII 5.2.2 and 6.2.11; Stacks Project Tags 03S6 and 07A7
(auxiliary; not a blueprint node).
-/

section
set_option autoImplicit false
set_option linter.all false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
attribute [local irreducible] AlgebraicGeometry.Etale.upperStar
  AlgebraicGeometry.Etale.lowerStar
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.leftDerivedFunctor
  AlgebraicGeometry.Etale.leftDerivedUpperStarComp
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorCounit
  CategoryTheory.Functor.rightDerivedFunctorUnit
  CategoryTheory.Functor.mapDerivedCategoryFactorsh
  CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
universe u u' v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
@[irreducible]
private noncomputable def graph_iso_from_units
    {C D E : Type*} [Category C] [Category D] [Category E]
    {P : C ⥤ D} {S : D ⥤ C} {J : C ⥤ E} {F : E ⥤ C} {V : E ⥤ D}
    (e : P ⋙ S ≅ 𝟭 C) (u : 𝟭 C ≅ J ⋙ F) (ξ : F ≅ V ⋙ S) :
    P ⋙ S ≅ (J ⋙ V) ⋙ S :=
  e ≪≫ u ≪≫ Functor.isoWhiskerLeft J ξ ≪≫ (Functor.associator J V S).symm

private theorem graph_iso_from_units_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    {P : C ⥤ D} {S : D ⥤ C} {J : C ⥤ E} {F : E ⥤ C} {V : E ⥤ D}
    (e : P ⋙ S ≅ 𝟭 C) (u : 𝟭 C ≅ J ⋙ F) (ξ : F ≅ V ⋙ S) (N : C) :
    (graph_iso_from_units e u ξ).hom.app N =
      e.hom.app N ≫ u.hom.app N ≫ ξ.hom.app (J.obj N) := by
  simp only [graph_iso_from_units, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    Functor.associator_inv_app, Category.comp_id]

@[irreducible]
private noncomputable def transfer_natTrans
    {C D H : Type*} [Category C] [Category D] [Category H]
    {S : D ⥤ C} {T : C ⥤ D} (a : T ⊣ S) (b : S ⊣ T)
    {F G : H ⥤ D} (α : F ⋙ S ⟶ G ⋙ S) : F ⟶ G where
  app N := b.unit.app (F.obj N) ≫ T.map (α.app N) ≫ a.counit.app (G.obj N)
  naturality X Y f := by
    dsimp
    rw [← b.unit_naturality_assoc]
    rw [← T.map_comp_assoc]
    have hn := α.naturality f
    change S.map (F.map f) ≫ α.app Y = α.app X ≫ S.map (G.map f) at hn
    rw [hn]
    simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
    rw [a.counit_naturality]

private theorem transfer_natTrans_app
    {C D H : Type*} [Category C] [Category D] [Category H]
    {S : D ⥤ C} {T : C ⥤ D} (a : T ⊣ S) (b : S ⊣ T)
    {F G : H ⥤ D} (α : F ⋙ S ⟶ G ⋙ S) (N : H) :
    (transfer_natTrans a b α).app N =
      b.unit.app (F.obj N) ≫ T.map (α.app N) ≫ a.counit.app (G.obj N) := by
  unfold transfer_natTrans
  rfl

@[irreducible]
private noncomputable def graph_unit_from_exchange
    {C D Z W : Type*} [Category C] [Category D] [Category Z] [Category W]
    (L : C ⥤ W) (R : W ⥤ C) (a : L ⊣ R)
    (J : C ⥤ Z) (V : Z ⥤ W) (P : Z ⥤ D) (F : D ⥤ C)
    (τ : L ⟶ J ⋙ V) (β : P ⋙ F ⟶ V ⋙ R) [IsIso β] :
    𝟭 C ⟶ (J ⋙ P) ⋙ F :=
  a.unit ≫ Functor.whiskerRight τ R ≫
    (Functor.associator J V R).hom ≫
    Functor.whiskerLeft J (inv β) ≫ (Functor.associator J P F).inv

private theorem graph_unit_from_exchange_app
    {C D Z W : Type*} [Category C] [Category D] [Category Z] [Category W]
    (L : C ⥤ W) (R : W ⥤ C) (a : L ⊣ R)
    (J : C ⥤ Z) (V : Z ⥤ W) (P : Z ⥤ D) (F : D ⥤ C)
    (τ : L ⟶ J ⋙ V) (β : P ⋙ F ⟶ V ⋙ R) [IsIso β] (N : C) :
    (graph_unit_from_exchange L R a J V P F τ β).app N =
      a.unit.app N ≫ R.map (τ.app N) ≫ inv (β.app (J.obj N)) := by
  unfold graph_unit_from_exchange
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    NatIso.isIso_inv_app, Category.id_comp, Category.comp_id]

@[irreducible]
private noncomputable def transpose_natTrans
    {C D : Type*} [Category C] [Category D]
    {E : C ⥤ D} {F : D ⥤ C} (a : E ⊣ F) (T : C ⥤ D) (ν : 𝟭 C ⟶ T ⋙ F) :
    E ⟶ T :=
  (Functor.leftUnitor E).inv ≫ Functor.whiskerRight ν E ≫
    (Functor.associator T F E).hom ≫
    Functor.whiskerLeft T a.counit ≫ (Functor.rightUnitor T).hom

private theorem unit_transpose_natTrans
    {C D : Type*} [Category C] [Category D]
    {E : C ⥤ D} {F : D ⥤ C} (a : E ⊣ F) (T : C ⥤ D) (ν : 𝟭 C ⟶ T ⋙ F)
    (N : C) :
    a.unit.app N ≫ F.map ((transpose_natTrans a T ν).app N) = ν.app N := by
  unfold transpose_natTrans
  simp only [NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Category.id_comp, Functor.map_comp]
  have h := a.unit.naturality (ν.app N)
  dsimp at h
  rw [← reassoc_of% h]
  erw [Adjunction.right_triangle_components_assoc]
  simp

private theorem transport_baseChange_diagram
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (E P : C ⥤ D) (E' P' : C' ⥤ D')
    (S S₀ : D ⥤ D') (T T₀ : C ⥤ C') (e : S ≅ S₀) (d : T ≅ T₀)
    (κ : T ⋙ E' ≅ E ⋙ S) (φ : E ⟶ P) (φ' : E' ⟶ P')
    (ψ : P ⋙ S ⟶ T ⋙ P')
    (h : ∀ N, κ.hom.app N ≫ S.map (φ.app N) ≫ ψ.app N = φ'.app (T.obj N)) :
    Functor.whiskerRight φ S₀ ≫ Functor.whiskerLeft P e.inv ≫ ψ ≫
        Functor.whiskerRight d.hom P' =
      Functor.whiskerLeft E e.inv ≫ κ.inv ≫ Functor.whiskerRight d.hom E' ≫
        Functor.whiskerLeft T₀ φ' := by
  ext N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc]
  have h' : S.map (φ.app N) ≫ ψ.app N = κ.inv.app N ≫ φ'.app (T.obj N) := by
    rw [← cancel_epi (κ.hom.app N)]
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using h N
  rw [e.inv.naturality_assoc, reassoc_of% h']
  rw [φ'.naturality]

private theorem iso_conjugation_cancel
    {C : Type*} [Category C] {X Y Z W : C}
    (e : X ≅ Y) (β : Y ≅ Z) (f : Z ≅ W) :
    f.hom ≫ (e ≪≫ β ≪≫ f).inv ≫ e.hom = β.inv := by
  simp

private theorem mapDerivedCategoryNatIso_symm_iso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    Functor.mapDerivedCategoryNatIso e.symm = (Functor.mapDerivedCategoryNatIso e).symm := by
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_symm e

private theorem clopen_transfer_baseChange
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (S : C ⥤ D) (T : D ⥤ C) (S' : C' ⥤ D') (T' : D' ⥤ C')
    (H : C ⥤ C') (K : D ⥤ D')
    (a : T ⊣ S) (b : S ⊣ T) (a' : T' ⊣ S') (b' : S' ⊣ T')
    (e : H ⋙ S' ≅ S ⋙ K) (d : K ⋙ T' ≅ T ⋙ H)
    [IsIso a.unit] [IsIso a'.unit]
    (hb' : ∀ M, b'.counit.app M = inv (a'.unit.app M))
    (hu : ∀ X, S.map (b.unit.app X) = a.unit.app (S.obj X))
    (hu' : ∀ X, S'.map (b'.unit.app X) = a'.unit.app (S'.obj X))
    (hm : ∀ M, a'.unit.app (K.obj M) ≫ S'.map (d.hom.app M) =
      K.map (a.unit.app M) ≫ e.inv.app (T.obj M))
    (hc : ∀ X, H.map (a.counit.app X) = d.inv.app (S.obj X) ≫
      T'.map (e.inv.app X) ≫ a'.counit.app (H.obj X))
    {X Y : C} (ψ : S.obj X ⟶ S.obj Y) :
    H.map (b.unit.app X ≫ T.map ψ ≫ a.counit.app Y) =
      b'.unit.app (H.obj X) ≫
        T'.map (e.hom.app X ≫ K.map ψ ≫ e.inv.app Y) ≫ a'.counit.app (H.obj Y) := by
  have he : H.map (b.unit.app X) ≫ d.inv.app (S.obj X) =
      b'.unit.app (H.obj X) ≫ T'.map (e.hom.app X) := by
    apply (b'.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc, hb', hu']
    have hn := e.hom.naturality (b.unit.app X)
    simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
    rw [hu] at hn
    have hn2 : S'.map (H.map (b.unit.app X)) =
        e.hom.app X ≫ K.map (a.unit.app (S.obj X)) ≫
          e.inv.app (T.obj (S.obj X)) := by
      rw [← cancel_mono (e.hom.app (T.obj (S.obj X)))]
      rw [hn]
      simp
    have hj : K.map (a.unit.app (S.obj X)) ≫
        e.inv.app (T.obj (S.obj X)) ≫ S'.map (d.inv.app (S.obj X)) =
          a'.unit.app (K.obj (S.obj X)) := by
      rw [← reassoc_of% (hm (S.obj X)), ← Functor.map_comp, d.hom_inv_id_app]
      erw [CategoryTheory.Functor.map_id, Category.comp_id]
    have hn' := a'.unit.naturality (e.hom.app X)
    simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn'
    rw [hn2, Category.assoc, Category.assoc, reassoc_of% hj,
      IsIso.hom_inv_id, ← reassoc_of% hn', IsIso.hom_inv_id]
  have hn := d.inv.naturality ψ
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [hc, reassoc_of% hn, reassoc_of% he]
private theorem exact_adjunction_pair
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian C] [IsGrothendieckAbelian D]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D]
    [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    {F : C ⥤ D} {R : D ⥤ C} [F.Additive] [R.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (a : F ⊣ R) (b : R ⊣ F)
    (h : a.unit ≫ b.counit = 𝟙 (𝟭 C)) :
    a.mapDerivedCategoryAdjunction.unit ≫ b.mapDerivedCategoryAdjunction.counit =
      𝟙 (𝟭 (DerivedCategory C)) := by
  apply Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
  intro M
  simp only [NatTrans.comp_app, NatTrans.id_app]
  rw [b.mapDerivedCategoryAdjunction_counit_app_Qh_obj]
  rw [reassoc_of% (a.mapDerivedCategoryAdjunction_unit_app_fac M)]
  rw [← Functor.map_comp]
  have hm : (a.mapHomotopyCategory (.up ℤ)).unit.app M ≫
      (b.mapHomotopyCategory (.up ℤ)).counit.app M = 𝟙 M := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient,
      Adjunction.mapHomotopyCategory_counit_app_quotient,
      ← Functor.map_comp]
    have hh : (a.mapHomologicalComplex (.up ℤ)).unit.app K ≫
        (b.mapHomologicalComplex (.up ℤ)).counit.app K = 𝟙 K := by
      ext n
      change a.unit.app (K.X n) ≫ b.counit.app (K.X n) = 𝟙 _
      exact NatTrans.congr_app h (K.X n)
    rw [hh]
    exact (HomotopyCategory.quotient C (.up ℤ)).map_id K
  rw [hm, CategoryTheory.Functor.map_id]
  rfl

private theorem transported_adjunction_pair
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {R R' : D ⥤ C} (a : F ⊣ R) (b : R ⊣ F) (e : R' ≅ R)
    (h : a.unit ≫ b.counit = 𝟙 _) (X : C) :
    (a.ofNatIsoRight e.symm).unit.app X ≫
      (b.ofNatIsoLeft e.symm).counit.app X = 𝟙 X := by
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoLeft_counit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Iso.symm_inv, Category.assoc]
  rw [Iso.inv_hom_id_app_assoc]
  exact NatTrans.congr_app h X

private theorem graph_baseChange_diagram
    {C C' D E : Type*} [Category C] [Category C'] [Category D] [Category E]
    (H : C ⥤ C') (S : D ⥤ C') (V : E ⥤ D) (J : E ⥤ C')
    {P N K L : C} {X Y Z : C'} {B B' : E}
    (t₀ : P ⟶ N) (t₁ : N ⟶ K) (t₂ : K ⟶ L) (G : P ⟶ L)
    (a : X ⟶ Y) (b : Y ⟶ H.obj P) (c : H.obj L ⟶ Z)
    (d : Z ⟶ S.obj (V.obj B)) (s : H.obj K ⟶ J.obj B)
    (t₀' : X ⟶ H.obj N) (u' : H.obj N ⟶ J.obj B')
    (v : J.obj B ⟶ S.obj (V.obj B)) (v' : J.obj B' ⟶ S.obj (V.obj B'))
    (e : B ≅ B') (G' : X ⟶ S.obj (V.obj B'))
    (hG : G = t₀ ≫ t₁ ≫ t₂) (hG' : G' = t₀' ≫ u' ≫ v')
    (hpre : a ≫ b ≫ H.map t₀ = t₀')
    (hpost : H.map t₂ ≫ c ≫ d = s ≫ v)
    (hn : v ≫ S.map (V.map e.hom) = J.map e.hom ≫ v')
    (hu : H.map t₁ ≫ s = u' ≫ J.map e.inv) :
    a ≫ b ≫ H.map G ≫ c ≫ d ≫ S.map (V.map e.hom) = G' := by
  rw [hG, hG']
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hpost, reassoc_of% hpre, hn, reassoc_of% hu]
  rw [← Functor.map_comp_assoc, e.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

namespace AlgebraicGeometry

open Scheme

namespace Etale.GraphExchange

variable (Λ : Type u') [Category.{u + 1} Λ] [Abelian Λ]
  [IsGrothendieckAbelian.{u + 1} Λ] [HasSmallSiteSheafify Λ]
  [MonoidalCategory Λ] [MonoidalPreadditive Λ] [SymmetricCategory Λ]
  [MonoidalClosed Λ] [Abelian.HasFunctorialFlatResolution Λ]

private instance graphSheafColimits (X : Scheme.{u}) :
    HasColimitsOfShape ℤ (Sheaf X.smallEtaleTopology (Λ)) :=
  inferInstance
private instance graphSheafCountableCoproducts (X : Scheme.{u}) :
    HasCountableCoproducts (Sheaf X.smallEtaleTopology (Λ)) :=
  inferInstance
private instance graphSheafExactColimits (X : Scheme.{u}) :
    HasExactColimitsOfShape ℤ (Sheaf X.smallEtaleTopology (Λ)) :=
  inferInstance

private instance graphSheafFlatResolution (X : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution
      (Sheaf X.smallEtaleTopology (Λ)) := inferInstance
private instance graphSheafKInjective (X : Scheme.{u}) :
    Abelian.HasKInjectiveResolutions
      (Sheaf X.smallEtaleTopology (Λ)) := inferInstance
private instance graphSheafGrothendieck (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1}
      (Sheaf X.smallEtaleTopology (Λ)) := inferInstance

private instance graphUpperAdditive {V W : Scheme.{u}} (f : V ⟶ W) :
    (upperStar Λ f).Additive := inferInstance

private instance graphUpperPreservesFiniteLimits {V W : Scheme.{u}} (f : V ⟶ W) :
    PreservesFiniteLimits (upperStar Λ f) := inferInstance

private instance graphUpperPreservesFiniteColimits {V W : Scheme.{u}} (f : V ⟶ W) :
    PreservesFiniteColimits (upperStar Λ f) := inferInstance

private instance graphLowerAdditive {V W : Scheme.{u}} (f : V ⟶ W) :
    (lowerStar Λ f).Additive := inferInstance

private instance graphLowerPreservesFiniteLimits {V W : Scheme.{u}} (f : V ⟶ W) :
    PreservesFiniteLimits (lowerStar Λ f) := inferInstance

private instance graphOpenAdditive {V W : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f] :
    (openImmersionLowerShriek Λ f).Additive := inferInstance

private instance graphOpenPreservesFiniteLimits {V W : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f] :
    PreservesFiniteLimits (openImmersionLowerShriek Λ f) := inferInstance

private instance graphOpenPreservesFiniteColimits {V W : Scheme.{u}}
    (f : V ⟶ W) [IsOpenImmersion f] :
    PreservesFiniteColimits (openImmersionLowerShriek Λ f) := inferInstance

private instance graphEtaleAdditive {V W : Scheme.{u}}
    (f : V ⟶ W) [_root_.AlgebraicGeometry.Etale f] :
    (etaleLowerShriek Λ f inferInstance).Additive := inferInstance

private instance graphEtalePreservesFiniteLimits {V W : Scheme.{u}}
    (f : V ⟶ W) [_root_.AlgebraicGeometry.Etale f] :
    PreservesFiniteLimits (etaleLowerShriek Λ f inferInstance) := inferInstance

private instance graphEtalePreservesFiniteColimits {V W : Scheme.{u}}
    (f : V ⟶ W) [_root_.AlgebraicGeometry.Etale f] :
    PreservesFiniteColimits (etaleLowerShriek Λ f inferInstance) := inferInstance

private instance graphSheafLocalization (X : Scheme.{u}) :
    (DerivedCategory.Qh (C := Sheaf X.smallEtaleTopology Λ)).IsLocalization
      (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology Λ) (.up ℤ)) := inferInstance

private noncomputable def graphOpenAdjunction {V T : Scheme.{u}}
    (j : V ⟶ T) [IsOpenImmersion j] :
    D((j)_!open[Λ]) ⊣ L((j)^*[Λ]) :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction _ j).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory _ j).symm

private instance graphOpenAdjunctionUnitIso {V T : Scheme.{u}}
    (j : V ⟶ T) [IsOpenImmersion j] :
    IsIso (graphOpenAdjunction Λ j).unit := by
  simp only [graphOpenAdjunction, Adjunction.ofNatIsoRight_unit]
  infer_instance

attribute [local irreducible] graphOpenAdjunction

section BaseChange

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- **The derived base change isomorphism of the extension by zero along open immersions is the
mate of the square isomorphism of the derived pullbacks**, for the adjunctions `Dj_! ⊣ Lj^*`
and `Dj'_! ⊣ Lj'^*`. -/
private lemma unit_map_derivedOpenImmersionLowerShriekBaseChangeIso' (hsq : IsPullback g' j' j g'')
    (K : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (Λ))) :
    (graphOpenAdjunction Λ j').unit.app
        (L((g')^*[Λ]).obj K) ≫
      L((j')^*[Λ]).map
        ((derivedOpenImmersionLowerShriekBaseChangeIso _ hsq).hom.app K) =
    L((g')^*[Λ]).map
        ((graphOpenAdjunction Λ j).unit.app K) ≫
      (derivedSquareUpperStarIso _ hsq.toCommSq).inv.app
        (D((j)_!open[Λ]).obj K) := by
  have h := unit_map_derivedOpenImmersionLowerShriekBaseChangeIso (Λ) hsq K
  rw [derivedOpenImmersionSquareMap_app] at h
  have hn := (leftDerivedUpperStarIsoMapDerivedCategory (Λ) j').inv.naturality
    ((derivedOpenImmersionLowerShriekBaseChangeIso _ hsq).hom.app K)
  simp only [graphOpenAdjunction,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Category.assoc, Functor.map_comp]
  dsimp at hn ⊢
  rw [← hn, reassoc_of% h]
  simp

/-- The mate form of `unit_map_derivedOpenImmersionLowerShriekBaseChangeIso'`. -/
private lemma mateEquiv_derivedOpenImmersionLowerShriekBaseChangeIso
    (hsq : IsPullback g' j' j g'') :
    mateEquiv (graphOpenAdjunction Λ j)
      (graphOpenAdjunction Λ j')
      (TwoSquare.mk _ _ _ _ (derivedOpenImmersionLowerShriekBaseChangeIso _ hsq).hom) =
    TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso _ hsq.toCommSq).inv :=
  mateEquiv_eq_of_unit _ _ _ _ fun K ↦
    (unit_map_derivedOpenImmersionLowerShriekBaseChangeIso' Λ hsq K).symm

/-- **The counit of the extension by zero commutes with base change**: for a cartesian square
of open immersions, `Lg''^*` of the counit of `Dj_! ⊣ Lj^*` is, through the base change
isomorphism and the square isomorphism of the pullbacks, the counit of `Dj'_! ⊣ Lj'^*`. -/
private lemma leftDerivedUpperStar_map_counit_derivedOpenImmersionLowerShriek
    (hsq : IsPullback g' j' j g'')
    (T : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (Λ))) :
    L((g'')^*[Λ]).map
        ((graphOpenAdjunction Λ j).counit.app T) =
      (derivedOpenImmersionLowerShriekBaseChangeIso _ hsq).inv.app
          (L((j)^*[Λ]).obj T) ≫
        D((j')_!open[Λ]).map
          ((derivedSquareUpperStarIso _ hsq.toCommSq).inv.app T) ≫
        (graphOpenAdjunction Λ j').counit.app
          (L((g'')^*[Λ]).obj T) := by
  have h := mateEquiv_counit (graphOpenAdjunction Λ j)
    (graphOpenAdjunction Λ j')
    (TwoSquare.mk _ _ _ _ (derivedOpenImmersionLowerShriekBaseChangeIso _ hsq).hom) T
  rw [mateEquiv_derivedOpenImmersionLowerShriekBaseChangeIso] at h
  dsimp only [TwoSquare.mk, TwoSquare.natTrans] at h
  rw [h, Iso.inv_hom_id_app_assoc]

end BaseChange

section Clopen

variable {X W : Scheme.{u}} (σ : X ⟶ W) [IsOpenImmersion σ] [IsClosedImmersion σ]

private instance clopen_comparison_iso
    {V T : Scheme.{u}} (j : V ⟶ T) [IsOpenImmersion j] [IsClosedImmersion j] :
    IsIso (openImmersionLowerShriekToLowerStar (Λ) j) :=
  isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range _ _
    (Scheme.Hom.isClosedEmbedding _).isClosed_range

private noncomputable def sheafClopenAdjunction
    {V T : Scheme.{u}} (j : V ⟶ T) [IsOpenImmersion j] [IsClosedImmersion j] :
    upperStar (Λ) j ⊣
      openImmersionLowerShriek (Λ) j :=
  (upperStarLowerStarAdjunction (Λ) j).ofNatIsoRight
    (asIso (openImmersionLowerShriekToLowerStar (Λ) j)).symm

attribute [local irreducible] sheafClopenAdjunction

/-- Derive the two exact sheaf functors termwise, then transport restriction
along its canonical exact-functor comparison. -/
private noncomputable def clopenUpperStarLowerShriekAdjunction :
    L((σ)^*[Λ]) ⊣ D((σ)_!open[Λ]) :=
  (sheafClopenAdjunction Λ σ).mapDerivedCategoryAdjunction.ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory _ σ).symm

attribute [local irreducible] clopenUpperStarLowerShriekAdjunction

/-- The counit of `Lσ^* ⊣ Dσ_!` is the inverse of the unit of `Dσ_! ⊣ Lσ^*`. -/
@[reassoc (attr := simp)]
private lemma unit_app_clopenUpperStarLowerShriekAdjunction_counit_app
    (S : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (Λ))) :
    (graphOpenAdjunction Λ σ).unit.app S ≫
      (clopenUpperStarLowerShriekAdjunction Λ σ).counit.app S = 𝟙 S := by
  have h : (openImmersionLowerShriekUpperStarAdjunction
      (Λ) σ).unit ≫ (sheafClopenAdjunction Λ σ).counit = 𝟙 _ := by
    apply NatTrans.ext
    funext M
    simpa only [sheafClopenAdjunction, Adjunction.ofNatIsoRight_counit,
      NatTrans.comp_app, NatTrans.id_app, Functor.whiskerRight_app,
      Iso.symm_inv, asIso_hom, Functor.id_obj, Category.assoc] using
      unit_map_openImmersionLowerShriekToLowerStar_app_counit
        (Λ) σ M
  have hd := exact_adjunction_pair
    (openImmersionLowerShriekUpperStarAdjunction (Λ) σ)
    (sheafClopenAdjunction Λ σ) h
  unfold graphOpenAdjunction derivedOpenImmersionLowerShriekUpperStarAdjunction
    clopenUpperStarLowerShriekAdjunction
  exact transported_adjunction_pair
      (openImmersionLowerShriekUpperStarAdjunction
        (Λ) σ).mapDerivedCategoryAdjunction
      (sheafClopenAdjunction Λ σ).mapDerivedCategoryAdjunction
      (leftDerivedUpperStarIsoMapDerivedCategory (Λ) σ) hd S

/-- The counit of `Lσ^* ⊣ Dσ_!` is the inverse of the unit of `Dσ_! ⊣ Lσ^*`. -/
private lemma clopenUpperStarLowerShriekAdjunction_counit_app
    (S : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (Λ))) :
    (clopenUpperStarLowerShriekAdjunction Λ σ).counit.app S =
      inv ((graphOpenAdjunction Λ σ).unit.app S) := by
  rw [← cancel_epi ((graphOpenAdjunction Λ σ).unit.app S),
    unit_app_clopenUpperStarLowerShriekAdjunction_counit_app, IsIso.hom_inv_id]
  rfl

/-- `Lσ^*` of the unit of `Lσ^* ⊣ Dσ_!` is the unit of `Dσ_! ⊣ Lσ^*`. -/
private lemma leftDerivedUpperStar_map_clopenUpperStarLowerShriekAdjunction_unit_app
    (T : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (Λ))) :
    L((σ)^*[Λ]).map ((clopenUpperStarLowerShriekAdjunction Λ σ).unit.app T) =
      (graphOpenAdjunction Λ σ).unit.app
        (L((σ)^*[Λ]).obj T) := by
  have h := (clopenUpperStarLowerShriekAdjunction Λ σ).left_triangle_components T
  rw [clopenUpperStarLowerShriekAdjunction_counit_app] at h
  rw [← cancel_mono (inv
    ((graphOpenAdjunction Λ σ).unit.app
    (L((σ)^*[Λ]).obj T))), h, IsIso.hom_inv_id]
  rfl

variable {σ} in
/-- **Restrict to an open and closed piece, apply a map there, and extend by zero.** For an open
and closed immersion `σ : X ⟶ W` and a morphism `ψ : Lσ^* T₁ ⟶ Lσ^* T₂`, the morphism
`T₁ ⟶ Dσ_! Lσ^* T₁ ⟶ Dσ_! Lσ^* T₂ ⟶ T₂`, by the unit of `Lσ^* ⊣ Dσ_!` and the counit of
`Dσ_! ⊣ Lσ^*`. -/
private noncomputable def clopenTransfer
    {T₁ T₂ : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (Λ))}
    (ψ : L((σ)^*[Λ]).obj T₁ ⟶ L((σ)^*[Λ]).obj T₂) :
    T₁ ⟶ T₂ :=
  (clopenUpperStarLowerShriekAdjunction Λ σ).unit.app T₁ ≫
    D((σ)_!open[Λ]).map ψ ≫
    (graphOpenAdjunction Λ σ).counit.app T₂

attribute [local irreducible] clopenTransfer

/-- `clopenTransfer` is natural in both variables. -/
private lemma clopenTransfer_comp
    {T₀ T₁ T₂ T₃ : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (Λ))}
    (a : T₀ ⟶ T₁)
    (ψ : L((σ)^*[Λ]).obj T₁ ⟶ L((σ)^*[Λ]).obj T₂)
    (b : T₂ ⟶ T₃) :
    clopenTransfer Λ (L((σ)^*[Λ]).map a ≫ ψ ≫
      L((σ)^*[Λ]).map b) = a ≫ clopenTransfer Λ ψ ≫ b := by
  simp only [clopenTransfer, Functor.map_comp, Category.assoc]
  rw [← Adjunction.counit_naturality,
    ← (clopenUpperStarLowerShriekAdjunction Λ σ).unit_naturality_assoc]

-- the base change of the unit of `Lσ^* ⊣ Dσ_!` unfolds large derived functors
/-- **`clopenTransfer` commutes with base change**: for a cartesian square
`k ≫ σ = σ' ≫ h` of open and closed immersions `σ`, `σ'`, `Lh^*` of `clopenTransfer ψ` is
`clopenTransfer` of `ψ` pulled back along `k`, read through the square isomorphisms
`Lσ'^* Lh^* ≅ Lk^* Lσ^*`. -/
private lemma leftDerivedUpperStar_map_clopenTransfer
    {X' W' : Scheme.{u}} {k : X' ⟶ X} {σ' : X' ⟶ W'}
    {h : W' ⟶ W} [IsOpenImmersion σ'] [IsClosedImmersion σ'] (hsq : IsPullback k σ' σ h)
    {T₁ T₂ : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (Λ))}
    (ψ : L((σ)^*[Λ]).obj T₁ ⟶ L((σ)^*[Λ]).obj T₂) :
    L((h)^*[Λ]).map (clopenTransfer Λ ψ) =
      clopenTransfer Λ ((derivedSquareUpperStarIso _ hsq.toCommSq).hom.app T₁ ≫
        L((k)^*[Λ]).map ψ ≫
        (derivedSquareUpperStarIso _ hsq.toCommSq).inv.app T₂) := by
  unfold clopenTransfer
  exact clopen_transfer_baseChange
      (upperStar (Λ) σ).leftDerivedFunctor
      (openImmersionLowerShriek (Λ) σ).mapDerivedCategory
      (upperStar (Λ) σ').leftDerivedFunctor
      (openImmersionLowerShriek (Λ) σ').mapDerivedCategory
      (upperStar (Λ) h).leftDerivedFunctor
      (upperStar (Λ) k).leftDerivedFunctor
      (graphOpenAdjunction Λ σ) (clopenUpperStarLowerShriekAdjunction Λ σ)
      (graphOpenAdjunction Λ σ') (clopenUpperStarLowerShriekAdjunction Λ σ')
      (derivedSquareUpperStarIso (Λ) hsq.toCommSq)
      (derivedOpenImmersionLowerShriekBaseChangeIso (Λ) hsq)
      (clopenUpperStarLowerShriekAdjunction_counit_app Λ σ')
      (leftDerivedUpperStar_map_clopenUpperStarLowerShriekAdjunction_unit_app Λ σ)
      (leftDerivedUpperStar_map_clopenUpperStarLowerShriekAdjunction_unit_app Λ σ')
      (unit_map_derivedOpenImmersionLowerShriekBaseChangeIso' Λ hsq)
      (leftDerivedUpperStar_map_counit_derivedOpenImmersionLowerShriek Λ hsq) ψ

end Clopen

end Etale.GraphExchange

end AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme

namespace Compactification

variable {X Y : Scheme.{u}} {e : X ⟶ Y} (c : Compactification e)

/-- The graph `(j, 𝟙) : X ⟶ Z ×_Y X` of the open immersion `j : X ⟶ Z` of a compactification
of `e`. -/
private noncomputable def graphExchangeSection : X ⟶ pullback c.g e :=
  pullback.lift c.i (𝟙 X) (by rw [Category.id_comp, ← c.comm])

@[reassoc (attr := simp)]
private lemma graphExchangeSection_fst : c.graphExchangeSection ≫ pullback.fst c.g e = c.i :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private lemma graphExchangeSection_snd : c.graphExchangeSection ≫ pullback.snd c.g e = 𝟙 X :=
  pullback.lift_snd _ _ _

private instance graphExchangeSectionSplitMono : IsSplitMono c.graphExchangeSection :=
  ⟨⟨⟨pullback.snd c.g e, c.graphExchangeSection_snd⟩⟩⟩

/-- The graph is a closed immersion, being a section of the separated morphism
`Z ×_Y X ⟶ X`. -/
private instance isClosedImmersion_graphExchangeSection :
    IsClosedImmersion c.graphExchangeSection := by
  have : IsProper c.g := c.isProper
  have : IsClosedImmersion (c.graphExchangeSection ≫ pullback.snd c.g e) := by
    rw [graphExchangeSection_snd]
    infer_instance
  exact IsClosedImmersion.of_comp c.graphExchangeSection (pullback.snd c.g e)

/-- The graph is étale when `e` is: its composite with the étale projection `Z ×_Y X ⟶ Z` is the
open immersion `j`. -/
private instance etale_graphExchangeSection [_root_.AlgebraicGeometry.Etale e] :
    _root_.AlgebraicGeometry.Etale c.graphExchangeSection := by
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have : _root_.AlgebraicGeometry.Etale (c.graphExchangeSection ≫ pullback.fst c.g e) := by
    rw [graphExchangeSection_fst]
    infer_instance
  exact _root_.AlgebraicGeometry.Etale.of_comp c.graphExchangeSection (pullback.fst c.g e)

/-- The graph is an open immersion when `e` is étale: it is a flat monomorphism locally of
finite presentation. -/
private instance isOpenImmersion_graphExchangeSection [_root_.AlgebraicGeometry.Etale e] :
    IsOpenImmersion c.graphExchangeSection :=
  IsOpenImmersion.of_flat_of_mono c.graphExchangeSection

end Compactification

namespace Etale.GraphExchange

variable (Λ : Type u') [Category.{u + 1} Λ] [Abelian Λ]
  [IsGrothendieckAbelian.{u + 1} Λ] [HasSmallSiteSheafify Λ]
  [MonoidalCategory Λ] [MonoidalPreadditive Λ] [SymmetricCategory Λ]
  [MonoidalClosed Λ] [Abelian.HasFunctorialFlatResolution Λ]

section Construction

variable {X Y : Scheme.{u}} (e : X ⟶ Y) [_root_.AlgebraicGeometry.Etale e]
  (c : Compactification e)

/-- The isomorphism `Lq^* ⋙ Lσ^* ≅ Dj_! ⋙ Lq_Z^* ⋙ Lσ^*`: both sides are identified with the
identity, through `σ ≫ q = 𝟙` and `σ ≫ q_Z = j`, and the unit of `Dj_! ⊣ Lj^*`. -/
private noncomputable def compactificationEtaleGraphIso :
    L((pullback.snd c.g e)^*[Λ]) ⋙ L((c.graphExchangeSection)^*[Λ]) ≅
      (D((c.i)_!open[Λ]) ⋙ L((pullback.fst c.g e)^*[Λ])) ⋙
        L((c.graphExchangeSection)^*[Λ]) :=
  graph_iso_from_units
    (leftDerivedUpperStarCompSectionIso Λ c.graphExchangeSection (pullback.snd c.g e)
      c.graphExchangeSection_snd)
    (asIso (graphOpenAdjunction Λ c.i).unit)
    (leftDerivedUpperStarComp Λ c.graphExchangeSection (pullback.fst c.g e) c.i
      c.graphExchangeSection_fst.symm)

/-- The map `Lq^* ⟶ Dj_! ⋙ Lq_Z^*` "restricting to the graph and extending by zero"
(`AlgebraicGeometry.Etale.clopenTransfer` of
`AlgebraicGeometry.Etale.compactificationEtaleGraphIso`):
`Lq^* K ⟶ Dσ_! Lσ^* Lq^* K ≅ Dσ_! Lσ^* Lq_Z^* Dj_! K ⟶ Lq_Z^* Dj_! K`. -/
private noncomputable def compactificationEtaleGraphMap :
    L((pullback.snd c.g e)^*[Λ]) ⟶
      D((c.i)_!open[Λ]) ⋙ L((pullback.fst c.g e)^*[Λ]) :=
  transfer_natTrans (graphOpenAdjunction Λ c.graphExchangeSection)
    (clopenUpperStarLowerShriekAdjunction Λ c.graphExchangeSection)
    (compactificationEtaleGraphIso Λ e c).hom

end Construction
end Etale.GraphExchange
end AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme

namespace Compactification

variable {X Y X' Y' : Scheme.{u}} {e : X ⟶ Y} {g : Y' ⟶ Y} {e' : X' ⟶ Y'} {g' : X' ⟶ X}
  (sq : IsPullback g' e' e g) (c : Compactification e)

/-- The projection `Z' = Z ×_Y Y' ⟶ Z` of the base-changed compactification, typed with source
the scheme of `c.ofIsPullback sq`. -/
private noncomputable abbrev graphExchangeBaseFst : (c.ofIsPullback sq).Z ⟶ c.Z :=
  pullback.fst c.g g

/-- `AlgebraicGeometry.Compactification.isPullback_i_ofIsPullback`, with the projection typed by
`AlgebraicGeometry.Compactification.graphExchangeBaseFst`. -/
private lemma graphExchangeOpenSquare :
    IsPullback g' (c.ofIsPullback sq).i c.i (c.graphExchangeBaseFst sq) :=
  c.isPullback_i_ofIsPullback sq

/-- The fibre product square of the base-changed compactification, with its projection typed by
`AlgebraicGeometry.Compactification.graphExchangeBaseFst`. -/
private lemma isPullback_graphExchangeBaseFst :
    IsPullback (c.graphExchangeBaseFst sq) (c.ofIsPullback sq).g c.g g :=
  IsPullback.of_hasPullback c.g g

/-- The map `Z' ×_{Y'} X' ⟶ Z ×_Y X` between the fibre products attached to a compactification
and to its base change. -/
private noncomputable def graphExchangeSectionBaseChange :
    pullback (c.ofIsPullback sq).g e' ⟶ pullback c.g e :=
  pullback.lift (pullback.fst _ _ ≫ c.graphExchangeBaseFst sq) (pullback.snd _ _ ≫ g') (by
    have h₁ := pullback.condition (f := (c.ofIsPullback sq).g) (g := e')
    have h₂ := pullback.condition (f := c.g) (g := g)
    simp only [ofIsPullback_g] at h₁
    rw [Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc, Category.assoc, sq.w])

@[reassoc (attr := simp)]
private lemma graphExchangeSectionBaseChange_fst :
    c.graphExchangeSectionBaseChange sq ≫ pullback.fst c.g e =
      pullback.fst (c.ofIsPullback sq).g e' ≫ c.graphExchangeBaseFst sq :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private lemma graphExchangeSectionBaseChange_snd :
    c.graphExchangeSectionBaseChange sq ≫ pullback.snd c.g e = pullback.snd (c.ofIsPullback sq).g
      e' ≫ g' :=
  pullback.lift_snd _ _ _

/-- The square `W' ⟶ W` over `g' : X' ⟶ X` is cartesian. -/
private lemma isPullback_graphExchangeSectionBaseChange :
    IsPullback (c.graphExchangeSectionBaseChange sq) (pullback.snd (c.ofIsPullback sq).g e')
      (pullback.snd c.g e) g' := by
  have s := (IsPullback.of_hasPullback (c.ofIsPullback sq).g e').paste_horiz
    (IsPullback.of_hasPullback c.g g)
  rw [← graphExchangeSectionBaseChange_fst, ← sq.w] at s
  exact IsPullback.of_right s (graphExchangeSectionBaseChange_snd sq c) (IsPullback.of_hasPullback
    c.g e)

@[reassoc (attr := simp)]
private lemma graphExchangeSection_graphExchangeSectionBaseChange :
    (c.ofIsPullback sq).graphExchangeSection ≫ c.graphExchangeSectionBaseChange sq = g' ≫
      c.graphExchangeSection := by
  ext
  · simp only [Category.assoc, graphExchangeSectionBaseChange_fst, graphExchangeSection_fst_assoc,
    graphExchangeSection_fst,
      ofIsPullback_i_fst]
  · simp only [Category.assoc, graphExchangeSectionBaseChange_snd, graphExchangeSection_snd_assoc,
    graphExchangeSection_snd,
      Category.comp_id]

/-- The graph of the base-changed compactification is the base change of the graph. -/
private lemma isPullback_graphExchangeSection :
    IsPullback g' (c.ofIsPullback sq).graphExchangeSection c.graphExchangeSection
      (c.graphExchangeSectionBaseChange sq) := by
  have s : IsPullback g' ((c.ofIsPullback sq).graphExchangeSection ≫
      pullback.snd (c.ofIsPullback sq).g e') (c.graphExchangeSection ≫ pullback.snd c.g e) g' := by
    rw [graphExchangeSection_snd, graphExchangeSection_snd]
    exact IsPullback.id_vert g'
  exact IsPullback.of_bot s (graphExchangeSection_graphExchangeSectionBaseChange sq c).symm
    (isPullback_graphExchangeSectionBaseChange sq c)

end Compactification
namespace Etale.GraphExchange

section Coherence

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The composite `Lf^* ⋙ L(a ≫ b)^* ⟶ ...` of composition isomorphisms does not depend on the
chosen composite `m = a ≫ b`. -/
private lemma leftDerivedUpperStarComp_comp_map_congr {T S U R : Scheme.{u}} (f : T ⟶ S) (a : S ⟶ U)
    (b : U ⟶ R) (t : T ⟶ R) (m₁ m₂ : S ⟶ R) (h : m₁ = m₂) (p₁ : t = f ≫ m₁) (p₂ : t = f ≫ m₂)
    (q₁ : m₁ = a ≫ b) (q₂ : m₂ = a ≫ b)
    (K : _root_.DerivedCategory (Sheaf R.smallEtaleTopology A)) :
    (leftDerivedUpperStarComp A f m₁ t p₁).hom.app K ≫
        L((f)^*[A]).map ((leftDerivedUpperStarComp A a b m₁ q₁).hom.app K) =
      (leftDerivedUpperStarComp A f m₂ t p₂).hom.app K ≫
        L((f)^*[A]).map ((leftDerivedUpperStarComp A a b m₂ q₂).hom.app K) := by
  subst h
  rfl

/-- The square isomorphism of the derived pullbacks does not depend on the chosen composite. -/
private lemma derivedSquareUpperStarIso_hom_app_eq
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g) (d : X' ⟶ Y) (hd : d = g' ≫ f)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (derivedSquareUpperStarIso A sq).hom.app K =
      (leftDerivedUpperStarComp A f' g d (hd.trans sq.w)).inv.app K ≫
        (leftDerivedUpperStarComp A g' f d hd).hom.app K := by
  subst hd
  rfl

/-- **Coherence of the composition isomorphisms around an open piece**: the two identifications
`Lg'^* Lj^* ≅ Lσ'^* Lq_Z'^* Lgb^*` built from the faces of the commutative diagram
`j = σ ≫ q_Z`, `j' = σ' ≫ q_Z'`, `g' ≫ σ = σ' ≫ h`, `h ≫ q_Z = q_Z' ≫ gb` agree. -/
private lemma leftDerivedUpperStarComp_square_coherence {X' X W' W Z' Z : Scheme.{u}} {g' : X' ⟶ X}
    {σ : X ⟶ W} {σ' : X' ⟶ W'} {h : W' ⟶ W} {qZ : W ⟶ Z} {qZ' : W' ⟶ Z'} {gb : Z' ⟶ Z}
    {j : X ⟶ Z} {j' : X' ⟶ Z'} (Sσ : CommSq g' σ' σ h) (S5 : CommSq h qZ' qZ gb)
    (Sj : CommSq g' j' j gb) (hj : j = σ ≫ qZ) (hj' : j' = σ' ≫ qZ')
    (M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    L((g')^*[A]).map ((leftDerivedUpperStarComp A σ qZ j hj).hom.app M) ≫
        (derivedSquareUpperStarIso A Sσ).inv.app (L((qZ)^*[A]).obj M) ≫
        L((σ')^*[A]).map ((derivedSquareUpperStarIso A S5).inv.app M) =
      (derivedSquareUpperStarIso A Sj).inv.app M ≫
        (leftDerivedUpperStarComp A σ' qZ' j' hj').hom.app (L((gb)^*[A]).obj M) := by
  have ht₁ : g' ≫ j = (g' ≫ σ) ≫ qZ := by rw [hj, Category.assoc]
  have ht₂ : g' ≫ j = j' ≫ gb := Sj.w
  rw [← cancel_epi ((leftDerivedUpperStarComp A g' j (g' ≫ j) rfl).hom.app M)]
  simp only [derivedSquareUpperStarIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  rw [leftDerivedUpperStarComp_assoc'_app_assoc A g' σ qZ (g' ≫ σ) j (g' ≫ j) rfl hj ht₁,
    Iso.hom_inv_id_app_assoc,
    ← leftDerivedUpperStarComp_assoc'_app_assoc A σ' h qZ (g' ≫ σ) (h ≫ qZ) (g' ≫ j) Sσ.w rfl
      ht₁, ← Functor.map_comp_assoc (L((σ')^*[A])), Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [Iso.hom_inv_id_app_assoc,
    ← leftDerivedUpperStarComp_assoc'_app A σ' qZ' gb j' (qZ' ≫ gb) (g' ≫ j) hj' rfl ht₂]
  exact leftDerivedUpperStarComp_comp_map_congr A σ' qZ' gb (g' ≫ j) _ _ S5.w _ _ _ _ M

end Coherence

variable (Λ : Type u') [Category.{u + 1} Λ] [Abelian Λ]
  [IsGrothendieckAbelian.{u + 1} Λ] [HasSmallSiteSheafify Λ]
  [MonoidalCategory Λ] [MonoidalPreadditive Λ] [SymmetricCategory Λ]
  [MonoidalClosed Λ] [Abelian.HasFunctorialFlatResolution Λ]

section Unfold

variable {X Y : Scheme.{u}} (e : X ⟶ Y) [_root_.AlgebraicGeometry.Etale e]
  (c : Compactification e)

omit [_root_.AlgebraicGeometry.Etale e] in
private lemma compactificationEtaleGraphIso_hom_app
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (Λ))) :
    have : IsOpenImmersion c.i := c.isOpenImmersion
    (compactificationEtaleGraphIso Λ e c).hom.app N =
      (leftDerivedUpperStarCompSectionIso _ c.graphExchangeSection (pullback.snd c.g e)
          c.graphExchangeSection_snd).hom.app N ≫
        (graphOpenAdjunction Λ c.i).unit.app N ≫
        (leftDerivedUpperStarComp _ c.graphExchangeSection (pullback.fst c.g e) c.i
          c.graphExchangeSection_fst.symm).hom.app (D((c.i)_!open[Λ]).obj N) := by
  unfold compactificationEtaleGraphIso
  simpa only [asIso_hom] using graph_iso_from_units_app
    (leftDerivedUpperStarCompSectionIso Λ c.graphExchangeSection (pullback.snd c.g e)
      c.graphExchangeSection_snd)
    (asIso (graphOpenAdjunction Λ c.i).unit)
    (leftDerivedUpperStarComp Λ c.graphExchangeSection (pullback.fst c.g e) c.i
      c.graphExchangeSection_fst.symm) N

private lemma compactificationEtaleGraphMap_app
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (Λ))) :
    (compactificationEtaleGraphMap Λ e c).app N =
      clopenTransfer Λ ((compactificationEtaleGraphIso Λ e c).hom.app N) :=
by
  unfold compactificationEtaleGraphMap
  rw [transfer_natTrans_app]
  unfold clopenTransfer
  rfl

end Unfold
section BaseChange

variable {X Y X' Y' : Scheme.{u}} {e : X ⟶ Y} {g : Y' ⟶ Y} {e' : X' ⟶ Y'} {g' : X' ⟶ X}
  (sq : IsPullback g' e' e g) (c : Compactification e) [_root_.AlgebraicGeometry.Etale e]
  [_root_.AlgebraicGeometry.Etale e']

attribute [local irreducible] compactificationEtaleGraphIso
  compactificationEtaleGraphMap
-- the derived functors involved are large terms
omit [_root_.AlgebraicGeometry.Etale e] [_root_.AlgebraicGeometry.Etale e'] in
/-- The coherence of the graph isomorphisms `Lq^* ⋙ Lσ^* ≅ Dj_! ⋙ Lq_Z^* ⋙ Lσ^*` with base
change. -/
private lemma compactificationEtaleGraphIso_baseChange
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (Λ))) :
    L(((c.ofIsPullback sq).graphExchangeSection)^*[Λ]).map
        ((derivedSquareUpperStarIso _ (c.isPullback_graphExchangeSectionBaseChange
          sq).toCommSq).hom.app N) ≫
      (derivedSquareUpperStarIso _ (c.isPullback_graphExchangeSection sq).toCommSq).hom.app
        (L((pullback.snd c.g e)^*[Λ]).obj N) ≫
      L((g')^*[Λ]).map ((compactificationEtaleGraphIso Λ e c).hom.app N) ≫
      (derivedSquareUpperStarIso _ (c.isPullback_graphExchangeSection sq).toCommSq).inv.app
        (L((pullback.fst c.g e)^*[Λ]).obj
          (D((c.i)_!open[Λ]).obj N)) ≫
      L(((c.ofIsPullback sq).graphExchangeSection)^*[Λ]).map
        ((derivedSquareUpperStarIso _ (⟨c.graphExchangeSectionBaseChange_fst sq⟩ :
            CommSq (c.graphExchangeSectionBaseChange sq) (pullback.fst (c.ofIsPullback sq).g e')
              (pullback.fst c.g e) (c.graphExchangeBaseFst sq))).inv.app
            (D((c.i)_!open[Λ]).obj N) ≫
          L((pullback.fst (c.ofIsPullback sq).g e')^*[Λ]).map
            ((derivedOpenImmersionLowerShriekBaseChangeIso _
              (c.graphExchangeOpenSquare sq)).inv.app N)) =
    (compactificationEtaleGraphIso Λ e' (c.ofIsPullback sq)).hom.app
      (L((g')^*[Λ]).obj N) := by
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have : IsOpenImmersion (c.ofIsPullback sq).i := (c.ofIsPullback sq).isOpenImmersion
  -- the sections of `q` and `q'`
  have hpre := leftDerivedUpperStar_map_comp_compSectionIso (Λ) g'
    (pullback.snd c.g e) (pullback.snd (c.ofIsPullback sq).g e') (c.graphExchangeSectionBaseChange
      sq)
    c.graphExchangeSection (c.ofIsPullback sq).graphExchangeSection
      (c.isPullback_graphExchangeSectionBaseChange sq).w
    (c.graphExchangeSection_graphExchangeSectionBaseChange sq) c.graphExchangeSection_snd
      (c.ofIsPullback sq).graphExchangeSection_snd N
  rw [← derivedSquareUpperStarIso_hom_app_eq (Λ)
    (c.isPullback_graphExchangeSection sq).toCommSq _
      (c.graphExchangeSection_graphExchangeSectionBaseChange sq)] at hpre
  have hpre' : L(((c.ofIsPullback sq).graphExchangeSection)^*[Λ]).map
      ((derivedSquareUpperStarIso _ (c.isPullback_graphExchangeSectionBaseChange
        sq).toCommSq).hom.app N) ≫
      (derivedSquareUpperStarIso _ (c.isPullback_graphExchangeSection sq).toCommSq).hom.app
        (L((pullback.snd c.g e)^*[Λ]).obj N) ≫
      L((g')^*[Λ]).map ((leftDerivedUpperStarCompSectionIso _ c.graphExchangeSection
        (pullback.snd c.g e) c.graphExchangeSection_snd).hom.app N) =
      (leftDerivedUpperStarCompSectionIso _ (c.ofIsPullback sq).graphExchangeSection
        (pullback.snd (c.ofIsPullback sq).g e') (c.ofIsPullback
          sq).graphExchangeSection_snd).hom.app
        (L((g')^*[Λ]).obj N) := by
    rw [← hpre, ← Functor.map_comp_assoc]
    simp [derivedSquareUpperStarIso]
  -- the open immersions `j` and `j'`
  have hJ := unit_map_derivedOpenImmersionLowerShriekBaseChangeIso' Λ
    (c.graphExchangeOpenSquare sq) N
  have hpost := leftDerivedUpperStarComp_square_coherence (Λ)
    (c.isPullback_graphExchangeSection sq).toCommSq
    (⟨c.graphExchangeSectionBaseChange_fst sq⟩ : CommSq (c.graphExchangeSectionBaseChange sq)
      (pullback.fst (c.ofIsPullback sq).g e') (pullback.fst c.g e) (c.graphExchangeBaseFst sq))
    (c.graphExchangeOpenSquare sq).toCommSq c.graphExchangeSection_fst.symm
    (c.ofIsPullback sq).graphExchangeSection_fst.symm (D((c.i)_!open[Λ]).obj N)
  have hnat := (leftDerivedUpperStarComp (Λ) (c.ofIsPullback sq).graphExchangeSection
    (pullback.fst (c.ofIsPullback sq).g e') (c.ofIsPullback sq).i
    (c.ofIsPullback sq).graphExchangeSection_fst.symm).hom.naturality
      ((derivedOpenImmersionLowerShriekBaseChangeIso _ (c.graphExchangeOpenSquare sq)).inv.app N)
  simpa only [Iso.app_hom, Iso.symm_hom, Functor.map_comp, Category.assoc] using
    (graph_baseChange_diagram
    L((g')^*[Λ]) L(((c.ofIsPullback sq).graphExchangeSection)^*[Λ])
    L((pullback.fst (c.ofIsPullback sq).g e')^*[Λ]) L(((c.ofIsPullback sq).i)^*[Λ])
    ((leftDerivedUpperStarCompSectionIso Λ c.graphExchangeSection (pullback.snd c.g e)
      c.graphExchangeSection_snd).hom.app N)
    ((graphOpenAdjunction Λ c.i).unit.app N)
    ((leftDerivedUpperStarComp Λ c.graphExchangeSection (pullback.fst c.g e) c.i
      c.graphExchangeSection_fst.symm).hom.app (D((c.i)_!open[Λ]).obj N))
    ((compactificationEtaleGraphIso Λ e c).hom.app N)
    (L(((c.ofIsPullback sq).graphExchangeSection)^*[Λ]).map
      ((derivedSquareUpperStarIso Λ
        (c.isPullback_graphExchangeSectionBaseChange sq).toCommSq).hom.app N))
    ((derivedSquareUpperStarIso Λ (c.isPullback_graphExchangeSection sq).toCommSq).hom.app
      (L((pullback.snd c.g e)^*[Λ]).obj N))
    ((derivedSquareUpperStarIso Λ (c.isPullback_graphExchangeSection sq).toCommSq).inv.app
      (L((pullback.fst c.g e)^*[Λ]).obj (D((c.i)_!open[Λ]).obj N)))
    (L(((c.ofIsPullback sq).graphExchangeSection)^*[Λ]).map
      ((derivedSquareUpperStarIso Λ (⟨c.graphExchangeSectionBaseChange_fst sq⟩ :
        CommSq (c.graphExchangeSectionBaseChange sq)
          (pullback.fst (c.ofIsPullback sq).g e') (pullback.fst c.g e)
          (c.graphExchangeBaseFst sq))).inv.app (D((c.i)_!open[Λ]).obj N)))
    ((derivedSquareUpperStarIso Λ (c.graphExchangeOpenSquare sq).toCommSq).inv.app
      (D((c.i)_!open[Λ]).obj N))
    ((leftDerivedUpperStarCompSectionIso Λ (c.ofIsPullback sq).graphExchangeSection
      (pullback.snd (c.ofIsPullback sq).g e')
      (c.ofIsPullback sq).graphExchangeSection_snd).hom.app (L((g')^*[Λ]).obj N))
    ((graphOpenAdjunction Λ (c.ofIsPullback sq).i).unit.app (L((g')^*[Λ]).obj N))
    ((leftDerivedUpperStarComp Λ (c.ofIsPullback sq).graphExchangeSection
      (pullback.fst (c.ofIsPullback sq).g e') (c.ofIsPullback sq).i
      (c.ofIsPullback sq).graphExchangeSection_fst.symm).hom.app
      (L((c.graphExchangeBaseFst sq)^*[Λ]).obj (D((c.i)_!open[Λ]).obj N)))
    ((leftDerivedUpperStarComp Λ (c.ofIsPullback sq).graphExchangeSection
      (pullback.fst (c.ofIsPullback sq).g e') (c.ofIsPullback sq).i
      (c.ofIsPullback sq).graphExchangeSection_fst.symm).hom.app
      (D(((c.ofIsPullback sq).i)_!open[Λ]).obj (L((g')^*[Λ]).obj N)))
    ((derivedOpenImmersionLowerShriekBaseChangeIso Λ (c.graphExchangeOpenSquare sq)).symm.app N)
    ((compactificationEtaleGraphIso Λ e' (c.ofIsPullback sq)).hom.app (L((g')^*[Λ]).obj N))
    (compactificationEtaleGraphIso_hom_app Λ e c N)
    (compactificationEtaleGraphIso_hom_app Λ e' (c.ofIsPullback sq) (L((g')^*[Λ]).obj N))
    hpre' hpost hnat.symm hJ.symm)

/-- The "restrict to the graph and extend by zero" maps commute with base change. -/
private lemma compactificationEtaleGraphMap_baseChange
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (Λ))) :
    (derivedSquareUpperStarIso _ (c.isPullback_graphExchangeSectionBaseChange
      sq).toCommSq).hom.app N ≫
      L((c.graphExchangeSectionBaseChange sq)^*[Λ]).map
        ((compactificationEtaleGraphMap Λ e c).app N) ≫
      (derivedSquareUpperStarIso _ (⟨c.graphExchangeSectionBaseChange_fst sq⟩ :
          CommSq (c.graphExchangeSectionBaseChange sq) (pullback.fst (c.ofIsPullback sq).g e')
            (pullback.fst c.g e) (c.graphExchangeBaseFst sq))).inv.app
          (D((c.i)_!open[Λ]).obj N) ≫
      L((pullback.fst (c.ofIsPullback sq).g e')^*[Λ]).map
        ((derivedOpenImmersionLowerShriekBaseChangeIso _
          (c.graphExchangeOpenSquare sq)).inv.app N) =
    (compactificationEtaleGraphMap Λ e' (c.ofIsPullback sq)).app
      (L((g')^*[Λ]).obj N) := by
  rw [compactificationEtaleGraphMap_app, compactificationEtaleGraphMap_app]
  rw [leftDerivedUpperStar_map_clopenTransfer Λ c.graphExchangeSection
    (c.isPullback_graphExchangeSection sq),
    ← clopenTransfer_comp]
  congr 1
  simp only [Category.assoc]
  exact compactificationEtaleGraphIso_baseChange Λ sq c N

end BaseChange
end Etale.GraphExchange
end AlgebraicGeometry

private theorem unit_cube_diagram
    {C C' W W' Z' X' : Type*}
    [Category C] [Category C'] [Category W] [Category W'] [Category Z'] [Category X']
    (H : C ⥤ C') (R : W ⥤ C) (T : W ⥤ W') (R' : W' ⥤ C')
    (E' : X' ⥤ C') (V' : Z' ⥤ W') (P' : Z' ⥤ X')
    (β₃ : R ⋙ H ⟶ T ⋙ R') (β₄ : P' ⋙ E' ⟶ V' ⋙ R') [IsIso β₄]
    {N Y : C} {PN VJ : W} {BJ J' : Z'} {Z : X'} {QN : W'}
    (β₀ : Y ⟶ R.obj VJ) [IsIso β₀] (β₂ : Z ⟶ P'.obj BJ)
    (α : H.obj Y ⟶ E'.obj Z) (γ : T.obj VJ ⟶ V'.obj BJ)
    (ψ : QN ⟶ T.obj PN) (δ : BJ ⟶ J')
    (τ : PN ⟶ VJ) (τ' : QN ⟶ V'.obj J')
    (η : N ⟶ R.obj PN) (η' : H.obj N ⟶ R'.obj QN)
    (u : N ⟶ Y) (u' : H.obj N ⟶ E'.obj (P'.obj J'))
    (χ : Z ⟶ P'.obj J')
    (hu₀ : u = η ≫ R.map τ ≫ inv β₀)
    (hu' : u' = η' ≫ R'.map τ' ≫ inv (β₄.app J'))
    (hχ : χ = β₂ ≫ P'.map δ)
    (hcube : H.map β₀ ≫ β₃.app VJ ≫ R'.map γ =
      α ≫ E'.map β₂ ≫ β₄.app BJ)
    (hu : H.map η ≫ β₃.app PN = η' ≫ R'.map ψ)
    (hτ : ψ ≫ T.map τ ≫ γ ≫ V'.map δ = τ') :
    H.map u ≫ α ≫ E'.map χ = u' := by
  rw [hu₀, hu', hχ]
  have n₄ := β₄.naturality δ
  have n₃ := β₃.naturality τ
  dsimp only [Functor.comp_map] at n₄ n₃
  rw [← cancel_mono (β₄.app J')]
  simp only [Functor.map_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [n₄, ← reassoc_of% hcube, ← Functor.map_comp_assoc H (inv β₀), IsIso.inv_hom_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% n₃, reassoc_of% hu]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← Functor.map_comp]
  simp only [Category.assoc, hτ]

private theorem transpose_baseChange_diagram
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    (E : C ⥤ D) (F : D ⥤ C) (E' : C' ⥤ D') (F' : D' ⥤ C')
    (a : E ⊣ F) (a' : E' ⊣ F') (H : C ⥤ C') (G : D ⥤ D')
    (S : C ⥤ D) (S' : C' ⥤ D') (d : G ⋙ F' ≅ F ⋙ H)
    (b : H ⋙ E' ⟶ E ⋙ G) (κ : S ⋙ G ⟶ H ⋙ S')
    (φ : E ⟶ S) (φ' : E' ⟶ S')
    (ν : 𝟭 C ⟶ S ⋙ F) (ν' : 𝟭 C' ⟶ S' ⋙ F')
    (hφ : ∀ N, a.unit.app N ≫ F.map (φ.app N) = ν.app N)
    (hφ' : ∀ N, a'.unit.app N ≫ F'.map (φ'.app N) = ν'.app N)
    (hb : ∀ N, a'.unit.app (H.obj N) ≫ F'.map (b.app N) =
      H.map (a.unit.app N) ≫ d.inv.app (E.obj N))
    (hν : ∀ N, H.map (ν.app N) ≫ d.inv.app (S.obj N) ≫
      F'.map (κ.app N) = ν'.app (H.obj N)) (N : C) :
    b.app N ≫ G.map (φ.app N) ≫ κ.app N = φ'.app (H.obj N) := by
  apply (a'.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [hφ', reassoc_of% (hb N), ← hν N, ← hφ N,
    Functor.map_comp, Category.assoc]
  have hn := d.inv.naturality (φ.app N)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]

attribute [local irreducible] AlgebraicGeometry.Etale.GraphExchange.graphOpenAdjunction
  AlgebraicGeometry.Etale.GraphExchange.clopenUpperStarLowerShriekAdjunction
  AlgebraicGeometry.Etale.GraphExchange.compactificationEtaleGraphIso
  AlgebraicGeometry.Etale.GraphExchange.compactificationEtaleGraphMap

private theorem transported_unit_fac
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian C] [IsGrothendieckAbelian D]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D]
    [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    {F : C ⥤ D} {R : D ⥤ C} [F.Additive] [R.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (a : F ⊣ R)
    {R' : DerivedCategory D ⥤ DerivedCategory C} (e : R' ≅ R.mapDerivedCategory)
    (κ : DerivedCategory.Qh ⋙ R' ⟶ R.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (he : Functor.whiskerLeft DerivedCategory.Qh e.hom ≫
      R.mapDerivedCategoryFactorsh.hom = κ)
    (M : HomotopyCategory C (.up ℤ)) :
    (a.mapDerivedCategoryAdjunction.ofNatIsoRight e.symm).unit.app
        (DerivedCategory.Qh.obj M) ≫
      R'.map (F.mapDerivedCategoryFactorsh.hom.app M) ≫
      κ.app ((F.mapHomotopyCategory (.up ℤ)).obj M) =
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app M) := by
  have h := a.mapDerivedCategoryAdjunction_unit_app_fac M
  have hc := NatTrans.congr_app he ((F.mapHomotopyCategory (.up ℤ)).obj M)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hc
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc]
  rw [← hc]
  erw [← e.inv.naturality_assoc]
  simp only [Functor.comp_obj]
  erw [Iso.inv_hom_id_app_assoc]
  exact h

private theorem transported_transfer_fac
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian C] [IsGrothendieckAbelian D]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D]
    [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    {F : C ⥤ D} {R : D ⥤ C} [F.Additive] [R.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (a : R ⊣ F) (b : F ⊣ R)
    {F' : DerivedCategory C ⥤ DerivedCategory D}
    (e : F' ≅ F.mapDerivedCategory)
    (M N : HomotopyCategory C (.up ℤ))
    {X Y : DerivedCategory C}
    (x : X ⟶ DerivedCategory.Qh.obj M) (y : Y ⟶ DerivedCategory.Qh.obj N)
    [IsIso x] [IsIso y]
    (ψ : (F.mapHomotopyCategory (.up ℤ)).obj M ⟶
      (F.mapHomotopyCategory (.up ℤ)).obj N)
    (ψD : F'.obj X ⟶ F'.obj Y)
    (hψ : ψD ≫ F'.map y ≫ e.hom.app _ ≫ F.mapDerivedCategoryFactorsh.hom.app N =
      F'.map x ≫ e.hom.app _ ≫ F.mapDerivedCategoryFactorsh.hom.app M ≫
        DerivedCategory.Qh.map ψ) :
    (b.mapDerivedCategoryAdjunction.ofNatIsoLeft e.symm).unit.app X ≫
      R.mapDerivedCategory.map ψD ≫
      (a.mapDerivedCategoryAdjunction.ofNatIsoRight e.symm).counit.app Y ≫ y =
    x ≫ DerivedCategory.Qh.map
      ((b.mapHomotopyCategory (.up ℤ)).unit.app M ≫
        (R.mapHomotopyCategory (.up ℤ)).map ψ ≫
        (a.mapHomotopyCategory (.up ℤ)).counit.app N) := by
  simp only [Adjunction.ofNatIsoLeft_unit, Adjunction.ofNatIsoRight_counit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Iso.symm_inv, Functor.map_comp, Category.assoc]
  erw [← a.mapDerivedCategoryAdjunction.counit.naturality]
  rw [a.mapDerivedCategoryAdjunction_counit_app_Qh_obj]
  try simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc R.mapDerivedCategory (e.hom.app Y)
    (F.mapDerivedCategory.map y)]
  rw [← e.hom.naturality]
  rw [← Functor.map_comp_assoc R.mapDerivedCategory ψD
    (F'.map y ≫ e.hom.app _)]
  rw [← Functor.map_comp_assoc R.mapDerivedCategory
    (ψD ≫ F'.map y ≫ e.hom.app _) (F.mapDerivedCategoryFactorsh.hom.app N)]
  simp only [Category.assoc]
  rw [hψ, e.hom.naturality_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc R.mapDerivedCategory (e.inv.app X) (e.hom.app X),
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [← b.mapDerivedCategoryAdjunction.unit.naturality_assoc]
  erw [R.mapDerivedCategoryFactorsh.hom.naturality_assoc]
  rw [reassoc_of% (b.mapDerivedCategoryAdjunction_unit_app_fac M)]
  all_goals simp only [Functor.id_map, Functor.comp_map, Functor.map_comp, Category.assoc]

private theorem homotopy_comp_inv
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (K : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app K = 𝟙 _ := by
  rw [← cancel_epi ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G))
    (.up ℤ)).hom.app K), Iso.hom_inv_id_app,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app]
  erw [Category.comp_id]
private theorem homotopy_compHom_inv
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] (e : H ≅ F ⋙ G)
    (K : HomotopyCategory C (.up ℤ)) :
    inv (Functor.mapHomotopyCategoryCompHom F G H e K) =
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K ≫
        (NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app K := by
  rw [← cancel_epi (Functor.mapHomotopyCategoryCompHom F G H e K), IsIso.hom_inv_id]
  simp only [Functor.mapHomotopyCategoryCompHom, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id,
    NatTrans.mapHomotopyCategory_id, NatTrans.id_app]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem homotopy_unit_diagram
    {C D E W : Type*} [Category C] [Category D] [Category E] [Category W]
    [Preadditive C] [Preadditive D] [Preadditive E] [Preadditive W]
    [Limits.HasBinaryBiproducts C] [Limits.HasBinaryBiproducts D]
    [Limits.HasBinaryBiproducts E] [Limits.HasBinaryBiproducts W]
    (L : C ⥤ D) (F : D ⥤ C) (J : C ⥤ E) (R : E ⥤ D)
    (V : E ⥤ W) (Q : W ⥤ C) (P : C ⥤ W)
    [L.Additive] [F.Additive] [J.Additive] [R.Additive]
    [V.Additive] [Q.Additive] [P.Additive]
    (a : L ⊣ F) (b : P ⊣ Q) (γ : L ⟶ J ⋙ R) (τ : P ⟶ J ⋙ V)
    (β : R ⋙ F ⟶ V ⋙ Q)
    (h : ∀ M, a.unit.app M ≫ F.map (γ.app M) ≫ β.app (J.obj M) =
      b.unit.app M ≫ Q.map (τ.app M))
    (K : HomotopyCategory C (.up ℤ)) :
    let γH := (γ.mapHomotopyCategory (.up ℤ)).app K ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (J ⋙ R)) (.up ℤ)).inv.app K
    let τH := (τ.mapHomotopyCategory (.up ℤ)).app K ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (J ⋙ V)) (.up ℤ)).inv.app K
    let βH := β.mapHomotopyCategory (.up ℤ)
    (a.mapHomotopyCategory (.up ℤ)).unit.app K ≫
      (F.mapHomotopyCategory (.up ℤ)).map γH ≫
        βH.app ((J.mapHomotopyCategory (.up ℤ)).obj K) =
    (b.mapHomotopyCategory (.up ℤ)).unit.app K ≫
      (Q.mapHomotopyCategory (.up ℤ)).map τH := by
  try dsimp only
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  simp only [NatTrans.comp_app, homotopy_comp_inv,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Adjunction.mapHomotopyCategory_unit_app_quotient, Category.comp_id, Category.id_comp]
  simp only [NatTrans.mapHomotopyCategory_app]
  erw [Functor.mapHomotopyCategory_map, Functor.mapHomotopyCategory_map]
  simp only [← Functor.map_comp]
  congr 1
  ext n : 1
  exact h (M.X n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem homotopy_transfer_diagram
    {C W E : Type*} [Category C] [Category W] [Category E]
    [Preadditive C] [Preadditive W] [Preadditive E]
    [Limits.HasBinaryBiproducts C] [Limits.HasBinaryBiproducts W]
    [Limits.HasBinaryBiproducts E]
    (P : C ⥤ W) (S : W ⥤ C) (T : C ⥤ W) (V : E ⥤ W)
    (J : C ⥤ E) (F : E ⥤ C) (I : C ⥤ C)
    [P.Additive] [S.Additive] [T.Additive] [V.Additive]
    [J.Additive] [F.Additive] [I.Additive]
    (a : T ⊣ S) (b : S ⊣ T) (j : J ⊣ F)
    (e : I ≅ P ⋙ S) (d : I ≅ 𝟭 C) (ξ : F ≅ V ⋙ S) (τ : P ⟶ J ⋙ V)
    (h : ∀ M, τ.app M = b.unit.app (P.obj M) ≫
      T.map (e.inv.app M ≫ d.hom.app M ≫ j.unit.app M ≫ ξ.hom.app (J.obj M)) ≫
      a.counit.app (V.obj (J.obj M)))
    (K : HomotopyCategory C (.up ℤ)) :
    let compH := Functor.mapHomotopyCategoryCompHom P S I e K
    let idH := (d.hom.mapHomotopyCategory (.up ℤ)).app K ≫
      (Functor.mapHomotopyCategoryIdIso _ (.up ℤ)).hom.app K
    let jH := (j.mapHomotopyCategory (.up ℤ)).unit.app K
    let postH := Functor.mapHomotopyCategoryCompHom V S F ξ
      ((J.mapHomotopyCategory (.up ℤ)).obj K)
    (τ.mapHomotopyCategory (.up ℤ)).app K ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (J ⋙ V)) (.up ℤ)).inv.app K =
    (b.mapHomotopyCategory (.up ℤ)).unit.app ((P.mapHomotopyCategory (.up ℤ)).obj K) ≫
      (T.mapHomotopyCategory (.up ℤ)).map (inv compH ≫ idH ≫ jH ≫ postH) ≫
      (a.mapHomotopyCategory (.up ℤ)).counit.app
        ((V.mapHomotopyCategory (.up ℤ)).obj ((J.mapHomotopyCategory (.up ℤ)).obj K)) := by
  try dsimp only
  rw [homotopy_compHom_inv]
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  simp only [Functor.mapHomotopyCategoryCompHom, homotopy_comp_inv,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryIdIso_hom_app_eq_id, Category.comp_id, Category.id_comp]
  have hu : (b.mapHomotopyCategory (.up ℤ)).unit.app
      ((P.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient C (.up ℤ)).obj M)) =
      (HomotopyCategory.quotient W (.up ℤ)).map
        ((b.mapHomologicalComplex (.up ℤ)).unit.app
          ((P.mapHomologicalComplex (.up ℤ)).obj M)) := by
    exact Adjunction.mapHomotopyCategory_unit_app_quotient (.up ℤ) b
      ((P.mapHomologicalComplex (.up ℤ)).obj M)
  have hc : (a.mapHomotopyCategory (.up ℤ)).counit.app
      ((V.mapHomotopyCategory (.up ℤ)).obj ((J.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient C (.up ℤ)).obj M))) =
      (HomotopyCategory.quotient W (.up ℤ)).map
        ((a.mapHomologicalComplex (.up ℤ)).counit.app
          ((V.mapHomologicalComplex (.up ℤ)).obj
            ((J.mapHomologicalComplex (.up ℤ)).obj M))) := by
    exact Adjunction.mapHomotopyCategory_counit_app_quotient (.up ℤ) a
      ((V.mapHomologicalComplex (.up ℤ)).obj ((J.mapHomologicalComplex (.up ℤ)).obj M))
  rw [hu, hc, Adjunction.mapHomotopyCategory_unit_app_quotient]
  have hτ : (τ.mapHomotopyCategory (.up ℤ)).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj M) =
      (HomotopyCategory.quotient W (.up ℤ)).map
        ((τ.mapHomologicalComplex (.up ℤ)).app M) := rfl
  have he : (e.inv.mapHomotopyCategory (.up ℤ)).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj M) =
      (HomotopyCategory.quotient C (.up ℤ)).map
        ((e.inv.mapHomologicalComplex (.up ℤ)).app M) := rfl
  have hd : (d.hom.mapHomotopyCategory (.up ℤ)).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj M) =
      (HomotopyCategory.quotient C (.up ℤ)).map
        ((d.hom.mapHomologicalComplex (.up ℤ)).app M) := rfl
  have hξ : (ξ.hom.mapHomotopyCategory (.up ℤ)).app
      ((J.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient C (.up ℤ)).obj M)) =
      (HomotopyCategory.quotient C (.up ℤ)).map
        ((ξ.hom.mapHomologicalComplex (.up ℤ)).app
          ((J.mapHomologicalComplex (.up ℤ)).obj M)) := rfl
  rw [hτ, he, hd, hξ]
  erw [Category.comp_id]
  simp only [← Functor.map_comp]
  erw [Functor.mapHomotopyCategory_map]
  simp only [← Functor.map_comp]
  congr 1
  ext n : 1
  change τ.app (M.X n) = b.unit.app (P.obj (M.X n)) ≫
    T.map (e.inv.app (M.X n) ≫ d.hom.app (M.X n) ≫
      j.unit.app (M.X n) ≫ ξ.hom.app (J.obj (M.X n))) ≫
    a.counit.app (V.obj (J.obj (M.X n)))
  exact h (M.X n)
namespace AlgebraicGeometry.Etale

private theorem graph_transfer_composition
    {C D E : Type*} [Category C] [Category D] [Category E]
    {S : C ⥤ D} {T : D ⥤ C} {V : D ⥤ E} {W : E ⥤ D}
    {J : C ⥤ E} {R : E ⥤ C}
    (s : S ⊣ T) (v : V ⊣ W) (j : J ⊣ R) (t : R ≅ W ⋙ T)
    (M : C) :
    v.unit.app (S.obj M) ≫ W.map
        ((((s.comp v).ofNatIsoRight t.symm).leftAdjointUniq j).hom.app M) =
      S.map (j.unit.app M ≫ t.hom.app (J.obj M)) ≫ s.counit.app (W.obj (J.obj M)) := by
  apply (s.homEquiv _ _).injective
  rw [s.homEquiv_unit]
  have h := Adjunction.unit_leftAdjointUniq_hom_app ((s.comp v).ofNatIsoRight t.symm) j M
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.comp_unit_app,
    NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Functor.comp_map, Category.assoc] at h
  have hn := t.inv.naturality
    ((((s.comp v).ofNatIsoRight t.symm).leftAdjointUniq j).hom.app M)
  dsimp only [Functor.comp_map] at hn
  rw [← hn] at h
  have h' := congrArg (fun z => z ≫ t.hom.app (J.obj M)) h
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h'
  have hr := (s.homEquiv _ _).apply_symm_apply (j.unit.app M ≫ t.hom.app (J.obj M))
  rw [Adjunction.homEquiv_counit] at hr
  simpa only [Functor.map_comp, Functor.comp_obj, Functor.id_obj, Category.assoc] using h'.trans
    hr.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem graph_baseChange_unit
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {P : D ⥤ E} {S : E ⥤ D}
    {Q : C ⥤ F} {T : F ⥤ C} {V : F ⥤ E} {W : E ⥤ F}
    (a : L ⊣ R) (b : P ⊣ S) (c : Q ⊣ T) (d : V ⊣ W)
    (x : S ⋙ R ≅ W ⋙ T) (M : C) {N : E} (φ : (Q ⋙ V).obj M ⟶ N) :
    a.unit.app M ≫ R.map (b.unit.app (L.obj M)) ≫
        R.map (S.map
          ((((a.comp b).ofNatIsoRight x).leftAdjointUniq (c.comp d)).hom.app M ≫ φ)) ≫
        x.hom.app N =
      c.unit.app M ≫ T.map (d.unit.app (Q.obj M) ≫ W.map φ) := by
  have h := Adjunction.homEquiv_naturality_right
    ((a.comp b).ofNatIsoRight x)
    ((((a.comp b).ofNatIsoRight x).leftAdjointUniq (c.comp d)).hom.app M) φ
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app] at h
  simp only [Adjunction.homEquiv_unit, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Adjunction.comp_unit_app,
    Functor.comp_map, Functor.map_comp, Category.assoc] at h ⊢
  simp only [← Functor.comp_map] at h ⊢
  rw [← x.hom.naturality_assoc, ← x.hom.naturality] at h
  exact h

namespace GraphSheaf
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f] (c : Compactification f)
private noncomputable abbrev sectionMap : U ⟶ pullback c.g f :=
  c.graphExchangeSection
private theorem section_fst : sectionMap f c ≫ pullback.fst c.g f = c.i :=
  pullback.lift_fst _ _ _
private theorem section_snd : sectionMap f c ≫ pullback.snd c.g f = 𝟙 U :=
  pullback.lift_snd _ _ _
private noncomputable def sectionIso :
    upperStar (A) (pullback.snd c.g f) ⋙
      upperStar (A) (sectionMap f c) ≅ 𝟭 _ :=
  (upperStarComp _ _ _ (𝟙 U) (section_snd f c).symm).symm ≪≫ upperStarId _ U
attribute [local irreducible] sectionIso
private noncomputable def projection :
    upperStar (A) (pullback.snd c.g f) ⟶
      openImmersionLowerShriek (A) (sectionMap f c) :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (upperStarLowerStarAdjunction _ (sectionMap f c)).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (sectionIso A f c).hom _ ≫ (Functor.leftUnitor _).hom ≫
    (asIso (openImmersionLowerShriekToLowerStar _ (sectionMap f c))).inv
private noncomputable def composition :
    openImmersionLowerShriek (A) (sectionMap f c) ⋙
      etaleLowerShriek (A) (pullback.fst c.g f) inferInstance ≅
        openImmersionLowerShriek (A) c.i :=
  (((openImmersionLowerShriekUpperStarAdjunction _ (sectionMap f c)).comp
    (etaleLowerShriekUpperStarAdjunction _ (pullback.fst c.g f) inferInstance)).ofNatIsoRight
      (upperStarComp _ _ _ c.i (section_fst f c).symm).symm).leftAdjointUniq
    (openImmersionLowerShriekUpperStarAdjunction _ c.i)
attribute [local irreducible] projection
  composition
  etaleLowerShriek
  openImmersionLowerShriek
private noncomputable def transfer :
    upperStar (A) (pullback.snd c.g f) ⟶
      openImmersionLowerShriek (A) c.i ⋙
        upperStar (A) (pullback.fst c.g f) where
  app M := (projection A f c).app M ≫
    (etaleLowerShriekUpperStarAdjunction _ (pullback.fst c.g f) inferInstance).unit.app _ ≫
    (upperStar (A) (pullback.fst c.g f)).map
      ((composition A f c).hom.app M)
  naturality M N φ := by
    simp only [Functor.comp_map, Category.assoc]
    erw [(projection A f c).naturality_assoc]
    erw [← Adjunction.unit_naturality_assoc]
    rw [← Functor.map_comp]
    erw [(composition A f c).hom.naturality]
    simp only [Functor.map_comp, Category.assoc]
attribute [local irreducible] transfer
private theorem transfer_formula
    (M : Sheaf U.smallEtaleTopology (A)) :
    (transfer A f c).app M =
      (projection A f c).app M ≫
        (openImmersionLowerShriek (A) (sectionMap f c)).map
          ((openImmersionLowerShriekUpperStarAdjunction _ c.i).unit.app M ≫
            (upperStarComp _ _ _ c.i (section_fst f c).symm).hom.app
              ((openImmersionLowerShriek (A) c.i).obj M)) ≫
        (openImmersionLowerShriekUpperStarAdjunction _ (sectionMap f c)).counit.app _ := by
  have hv := graph_transfer_composition
    (openImmersionLowerShriekUpperStarAdjunction (A) (sectionMap f c))
    (etaleLowerShriekUpperStarAdjunction (A)
      (pullback.fst c.g f) inferInstance)
    (openImmersionLowerShriekUpperStarAdjunction (A) c.i)
    (upperStarComp _ _ _ c.i (section_fst f c).symm) M
  simpa only [composition, transfer] using congrArg (fun z => (projection A f c).app M ≫ z) hv
private noncomputable def clopenAdjunction :
    upperStar (A) (sectionMap f c) ⊣
      openImmersionLowerShriek (A) (sectionMap f c) :=
  GraphExchange.sheafClopenAdjunction A (sectionMap f c)
attribute [local irreducible] clopenAdjunction
private theorem projection_formula
    (M : Sheaf U.smallEtaleTopology (A)) :
    (projection A f c).app M =
      (clopenAdjunction A f c).unit.app _ ≫
        (openImmersionLowerShriek (A) (sectionMap f c)).map
          ((sectionIso A f c).hom.app M) := by
  simp only [projection, clopenAdjunction, GraphExchange.sheafClopenAdjunction,
    Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_inv_app, Functor.associator_inv_app,
    Functor.leftUnitor_hom_app, Iso.symm_hom, asIso_inv,
    Category.id_comp, Category.comp_id]
  erw [Category.id_comp]
  rw [Category.assoc]
  congr 1
  exact (asIso (openImmersionLowerShriekToLowerStar
    (A) (sectionMap f c))).inv.naturality _
private theorem transfer_clopen
    (M : Sheaf U.smallEtaleTopology (A)) :
    (transfer A f c).app M =
      (clopenAdjunction A f c).unit.app _ ≫
        (openImmersionLowerShriek (A) (sectionMap f c)).map
          ((sectionIso A f c).hom.app M ≫
            (openImmersionLowerShriekUpperStarAdjunction
              (A) c.i).unit.app M ≫
            (upperStarComp _ _ _ c.i (section_fst f c).symm).hom.app
              ((openImmersionLowerShriek (A) c.i).obj M)) ≫
        (openImmersionLowerShriekUpperStarAdjunction (A)
          (sectionMap f c)).counit.app _ := by
  rw [transfer_formula, projection_formula]
  simp only [Functor.map_comp, Category.assoc]

end GraphSheaf
namespace GraphSheaf
variable (A : Type (u + 1)) [CommRing A]
  {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f] (c : Compactification f)
private noncomputable def delta :
    etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ⋙
      upperStar (ModuleCat.{u + 1} A) c.g ⟶
        openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i :=
  (etaleLowerShriekBaseChangeIso A (IsPullback.of_hasPullback c.g f)).hom ≫
    Functor.whiskerRight (projection (ModuleCat.{u + 1} A) f c) _ ≫ (composition (ModuleCat.{u +
      1} A) f c).hom
attribute [local irreducible] delta
  projection
  composition
  etaleLowerShriek
  openImmersionLowerShriek
private theorem transfer_eq (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (transfer (ModuleCat.{u + 1} A) f c).app M =
      ((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
        (pullback.fst c.g f) inferInstance).homEquiv _ _)
        ((etaleLowerShriekBaseChangeIso A (IsPullback.of_hasPullback c.g f)).inv.app M ≫
          (delta A f c).app M) := by
  simp only [delta, NatTrans.comp_app, Functor.whiskerRight_app,
    Iso.inv_hom_id_app_assoc, Adjunction.homEquiv_unit, Functor.map_comp,
    Category.assoc]
  erw [Adjunction.unit_naturality_assoc]
  with_unfolding_all rfl
set_option maxRecDepth 4000 in
private theorem comparison_app
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (etaleCompactificationGraphMap A f c).app M =
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g).homEquiv _ _
        ((delta A f c).app M) := by
  unfold etaleCompactificationGraphMap delta projection composition sectionIso sectionMap
  rfl
private theorem comparison_unit
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) f inferInstance).unit.app M ≫
        (upperStar (ModuleCat.{u + 1} A) f).map
          ((etaleCompactificationGraphMap A f c).app M) ≫
        (baseChangeMap (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback c.g f).toCommSq).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).obj M) =
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (pullback.snd c.g f)).unit.app M ≫
        (lowerStar (ModuleCat.{u + 1} A) (pullback.snd c.g f)).map
          ((transfer (ModuleCat.{u + 1} A) f c).app M) := by
  rw [comparison_app, transfer_eq]
  letI : ∀ F, IsIso ((baseChangeMap (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback c.g f).toCommSq).app F) :=
    fun F => isIso_baseChangeMap_app_of_flat A (IsPullback.of_hasPullback c.g f) F
  letI : IsIso (baseChangeMap (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback c.g f).toCommSq) := NatIso.isIso_of_isIso_app _
  have h := graph_baseChange_unit
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) f inferInstance)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (pullback.snd c.g f))
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
      (pullback.fst c.g f) inferInstance)
    (asIso (baseChangeMap (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback c.g f).toCommSq)) M
    ((etaleLowerShriekBaseChangeIso A (IsPullback.of_hasPullback c.g f)).inv.app M ≫
      (delta A f c).app M)
  simp only [etaleLowerShriekBaseChangeIso, Iso.hom_inv_id_app_assoc,
    Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc] at h ⊢
  exact h

end GraphSheaf
end AlgebraicGeometry.Etale

private theorem comparison_normalization_diagram
    {H C D : Type*} [Category H] [Category C] [Category D]
    (Q : H ⥤ D) (R : C ⥤ D) {M N P : H} {X : D} {Y Z : C}
    (e : Y ≅ Z) (x : X ⟶ Q.obj M) (a : M ⟶ N) (b : N ⟶ P)
    (y : Q.obj P ⟶ R.obj Z) (σ : X ⟶ R.obj Y)
    (h : σ = x ≫ Q.map a ≫ Q.map b ≫ y ≫ R.map e.inv) :
    σ ≫ R.map e.hom = x ≫ Q.map (a ≫ b) ≫ y := by
  rw [h]
  simp only [Functor.map_comp, Category.assoc]
  rw [← R.map_comp, e.inv_hom_id, R.map_id, Category.comp_id]

private theorem normalized_unit_diagram
    {C D E W : Type*} [Category C] [Category D] [Category E] [Category W]
    (F : D ⥤ C) (R : E ⥤ D) (V : E ⥤ W) (Q : W ⥤ C)
    (β : R ⋙ F ⟶ V ⋙ Q)
    {K : C} {E₀ H : D} {J₀ J₁ : E} {P T : W} {S : C}
    (η : K ⟶ F.obj E₀) (ζ : K ⟶ Q.obj P)
    (σ : E₀ ⟶ R.obj J₀) (j : J₀ ⟶ J₁) (v : V.obj J₁ ⟶ T)
    (a : E₀ ⟶ H) (r : H ⟶ R.obj J₁) (κ : F.obj H ⟶ S)
    (b : S ⟶ Q.obj T) (τ : P ⟶ V.obj J₀) (t : P ⟶ T)
    [IsIso j] [IsIso v]
    (hσ : σ ≫ R.map j = a ≫ r)
    (hβ : F.map r ≫ β.app J₁ ≫ Q.map v = κ ≫ b)
    (hτ : τ ≫ V.map j ≫ v = t)
    (h : η ≫ F.map a ≫ κ ≫ b = ζ ≫ Q.map t) :
    η ≫ F.map σ ≫ β.app J₀ = ζ ≫ Q.map τ := by
  rw [← cancel_mono (Q.map (V.map j ≫ v))]
  simp only [Functor.map_comp, Category.assoc]
  have hn := β.naturality j
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [← Functor.map_comp_assoc, hσ]
  simp only [Functor.map_comp, Category.assoc]
  rw [hβ]
  rw [← Functor.map_comp, ← Functor.map_comp, hτ]
  exact h
private theorem quotient_unit_diagram
    {C D W HC HD HW : Type*}
    [Category C] [Category D] [Category W]
    [Category HC] [Category HD] [Category HW]
    (F : D ⥤ C) (Q : W ⥤ C)
    (QC : HC ⥤ C) (QD : HD ⥤ D) (QW : HW ⥤ W)
    (FH : HD ⥤ HC) (QH : HW ⥤ HC)
    (κ : QD ⋙ F ⟶ FH ⋙ QC) (ρ : QH ⋙ QC ⟶ QW ⋙ Q)
    {K : HC} {E H : HD} {P T : HW}
    {E₀ : D} {P₀ : W}
    (η : QC.obj K ⟶ F.obj E₀) (ζ : QC.obj K ⟶ Q.obj P₀)
    (e : E₀ ⟶ QD.obj E) (p : P₀ ⟶ QW.obj P)
    (a : E ⟶ H) (b : FH.obj H ⟶ QH.obj T) (t : P ⟶ T)
    (ηH : K ⟶ FH.obj E) (ζH : K ⟶ QH.obj P)
    (hη : η ≫ F.map e ≫ κ.app E = QC.map ηH)
    (hζ : ζ ≫ Q.map p = QC.map ζH ≫ ρ.app P)
    (h : ηH ≫ FH.map a ≫ b = ζH ≫ QH.map t) :
    η ≫ F.map (e ≫ QD.map a) ≫ κ.app H ≫ QC.map b ≫ ρ.app T =
      ζ ≫ Q.map (p ≫ QW.map t) := by
  simp only [Functor.map_comp, Category.assoc]
  have hn := κ.naturality a
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [reassoc_of% hη]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [h]
  simp only [Functor.map_comp, Category.assoc]
  have ht := ρ.naturality t
  simp only [Functor.comp_map] at ht
  rw [ht]
  rw [← Category.assoc, ← hζ]
  simp only [Category.assoc]

private theorem double_unit_diagram
    {C D E W HC HD HW : Type*}
    [Category C] [Category D] [Category E] [Category W]
    [Category HC] [Category HD] [Category HW]
    (F : D ⥤ C) (R : E ⥤ D) (V : E ⥤ W) (Q : W ⥤ C)
    (QC : HC ⥤ C) (QD : HD ⥤ D) (QW : HW ⥤ W)
    (FH : HD ⥤ HC) (QH : HW ⥤ HC)
    (κ : QD ⋙ F ⟶ FH ⋙ QC) (ρ : QH ⋙ QC ⟶ QW ⋙ Q)
    (β : R ⋙ F ⟶ V ⋙ Q)
    {K : HC} {EH H : HD} {P T : HW}
    {E₀ : D} {P₀ : W} {J₀ J₁ : E}
    (η : QC.obj K ⟶ F.obj E₀) (ζ : QC.obj K ⟶ Q.obj P₀)
    (σ : E₀ ⟶ R.obj J₀) (j : J₀ ⟶ J₁) (v : V.obj J₁ ⟶ QW.obj T)
    (a : EH ⟶ H) (r : QD.obj H ⟶ R.obj J₁)
    (e : E₀ ⟶ QD.obj EH) (p : P₀ ⟶ QW.obj P)
    (b : FH.obj H ⟶ QH.obj T) (τ : P₀ ⟶ V.obj J₀) (t : P ⟶ T)
    (ηH : K ⟶ FH.obj EH) (ζH : K ⟶ QH.obj P)
    [IsIso j] [IsIso v]
    (hσ : σ ≫ R.map j = e ≫ QD.map a ≫ r)
    (hβ : F.map r ≫ β.app J₁ ≫ Q.map v = κ.app H ≫ QC.map b ≫ ρ.app T)
    (hτ : τ ≫ V.map j ≫ v = p ≫ QW.map t)
    (hη : η ≫ F.map e ≫ κ.app EH = QC.map ηH)
    (hζ : ζ ≫ Q.map p = QC.map ζH ≫ ρ.app P)
    (hH : ηH ≫ FH.map a ≫ b = ζH ≫ QH.map t) :
    η ≫ F.map σ ≫ β.app J₀ = ζ ≫ Q.map τ := by
  exact normalized_unit_diagram F R V Q β η ζ σ j v
    (e ≫ QD.map a) r (κ.app H) (QC.map b ≫ ρ.app T) τ (p ≫ QW.map t)
    (by simpa only [Category.assoc] using hσ) hβ hτ
    (quotient_unit_diagram F Q QC QD QW FH QH κ ρ η ζ e p a b t ηH ζH hη hζ hH)

private theorem normalized_section_diagram
    {H C : Type*} [Category H] [Category C] (Q : H ⥤ C)
    {J P T : H} (t : J ⟶ P) [IsIso t] (d : J ⟶ T)
    {M N Z : C} (a : M ⟶ N) (b : N ⟶ Q.obj J)
    (c₀ : M ⟶ Z) (c₁ : Z ⟶ Q.obj P) (i : N ⟶ Q.obj T)
    (ψ : M ⟶ Q.obj T)
    (hψ : ψ = a ≫ i) (ha : a ≫ b ≫ Q.map t = c₀ ≫ c₁)
    (hi : i = b ≫ Q.map d) :
    ψ = c₀ ≫ c₁ ≫ Q.map (inv t ≫ d) := by
  rw [hψ, hi]
  have h := congrArg (fun z ↦ z ≫ Q.map (inv t ≫ d)) ha
  simp only [Functor.map_comp, Category.assoc] at h
  rw [← Functor.map_comp_assoc, IsIso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp] at h
  simpa only [Functor.map_comp, Category.assoc] using h

private theorem normalized_graph_diagram
    {H C D : Type*} [Category H] [Category C] [Category D]
    (Q : H ⥤ C) (S : D ⥤ C)
    {I I₁ J K L : H} (t₀ : I ⟶ I₁) (t₁ : I₁ ⟶ J) (j : J ⟶ K) (v : K ⟶ L)
    {X M N Z : C} {A B E : D}
    (ψ : X ⟶ S.obj A) (α : X ⟶ Q.obj J) (η : Q.obj J ⟶ M)
    (γ : M ⟶ S.obj A) (k : A ⟶ B) (l : B ⟶ E)
    (r : S.obj E ⟶ Q.obj L) (δ : M ⟶ N) (γ' : N ⟶ S.obj B)
    (p : N ⟶ Q.obj K) (z₀ : X ⟶ Z) (z₁ : Z ⟶ Q.obj I)
    (hψ : ψ = α ≫ η ≫ γ) (hα : α = z₀ ≫ z₁ ≫ Q.map (t₀ ≫ t₁))
    (hn : γ ≫ S.map k = δ ≫ γ')
    (hc : γ' ≫ S.map l ≫ r = p ≫ Q.map v)
    (hu : η ≫ δ ≫ p = Q.map j) :
    ψ ≫ S.map (k ≫ l) ≫ r = z₀ ≫ z₁ ≫ Q.map (t₀ ≫ t₁ ≫ j ≫ v) := by
  rw [hψ]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, hc, reassoc_of% hu, hα]
  simp only [Functor.map_comp, Category.assoc]

namespace AlgebraicGeometry.Etale.GraphExchange
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
end AlgebraicGeometry.Etale.GraphExchange
namespace AlgebraicGeometry.Etale.GraphExchange
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
private theorem clopenTransfer_fac
    {X W : Scheme.{u}} (s : X ⟶ W) [IsOpenImmersion s] [IsClosedImmersion s]
    (M N : HomotopyCategory (Sheaf W.smallEtaleTopology A) (.up ℤ))
    {T₁ T₂ : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A)}
    (x : T₁ ⟶ DerivedCategory.Qh.obj M) (y : T₂ ⟶ DerivedCategory.Qh.obj N)
    [IsIso x] [IsIso y]
    (ψ : ((upperStar A s).mapHomotopyCategory (.up ℤ)).obj M ⟶
      ((upperStar A s).mapHomotopyCategory (.up ℤ)).obj N)
    (ψD : L((s)^*[A]).obj T₁ ⟶ L((s)^*[A]).obj T₂)
    (hψ : ψD ≫ L((s)^*[A]).map y ≫ (upperStar A s).leftDerivedFunctorCounit.app N =
      L((s)^*[A]).map x ≫ (upperStar A s).leftDerivedFunctorCounit.app M ≫
        DerivedCategory.Qh.map ψ) :
    clopenTransfer A ψD ≫ y = x ≫ DerivedCategory.Qh.map
      (((sheafClopenAdjunction A s).mapHomotopyCategory (.up ℤ)).unit.app M ≫
        ((openImmersionLowerShriek A s).mapHomotopyCategory (.up ℤ)).map ψ ≫
        ((openImmersionLowerShriekUpperStarAdjunction A s).mapHomotopyCategory
          (.up ℤ)).counit.app N) := by
  unfold clopenTransfer graphOpenAdjunction
    derivedOpenImmersionLowerShriekUpperStarAdjunction clopenUpperStarLowerShriekAdjunction
  simp only [Category.assoc]
  apply transported_transfer_fac
    (openImmersionLowerShriekUpperStarAdjunction A s)
    (sheafClopenAdjunction A s) (leftDerivedUpperStarIsoMapDerivedCategory A s)
    M N x y ψ ψD
  have hc := (upperStar A s).leftDerivedFunctorIsoMapDerivedCategory_hom_fac
  have hcM := NatTrans.congr_app hc M
  have hcN := NatTrans.congr_app hc N
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hcM hcN
  dsimp only [leftDerivedUpperStarIsoMapDerivedCategory]
  rw [hcN, reassoc_of% hcM]
  exact hψ

end AlgebraicGeometry.Etale.GraphExchange
namespace AlgebraicGeometry.Etale
variable (A : Type (u + 1)) [CommRing A]
private instance cachedColimits (X : Scheme.{u}) :
    HasColimitsOfShape ℤ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance
private instance cachedCoproducts (X : Scheme.{u}) :
    HasCountableCoproducts (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance
private instance cachedExactColimits (X : Scheme.{u}) :
    HasExactColimitsOfShape ℤ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance
end AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale.GraphExchange
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
end AlgebraicGeometry.Etale.GraphExchange
namespace AlgebraicGeometry.Etale
variable (A : Type (u + 1)) [CommRing A]
attribute [local irreducible] derivedEtaleLowerShriekAdjunction
  derivedUpperStarLowerStarAdjunction
  derivedBaseChangeMap

end AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

end AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale.GraphExchange
attribute [local irreducible] AlgebraicGeometry.Etale.derivedUpperStarLowerStarAdjunction
  AlgebraicGeometry.Etale.mapDerivedUpperStarLowerStarAdjunction
private theorem transfer_normalization_diagram
    {H C : Type*} [Category H] [Category C] (Q : H ⥤ C)
    {X Y : C} {M N : H} (g g' : X ⟶ Y) (y : Y ⟶ Q.obj N)
    (x : X ⟶ Q.obj M) (t t' : M ⟶ N)
    (hg : g = g') (h : g' ≫ y = x ≫ Q.map t') (ht : t = t') :
    g ≫ y = x ≫ Q.map t := by
  rw [hg, h, ht]

private theorem graph_transfer_homotopy_fac
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
    [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    (c : Compactification f)
    (K : HomotopyCategory (Sheaf U.smallEtaleTopology A) (.up ℤ)) :
    (compactificationEtaleGraphMap A f c).app (DerivedCategory.Qh.obj K) ≫
      (upperStar A (pullback.fst c.g f)).leftDerivedFunctor.map
        ((openImmersionLowerShriek A c.i).mapDerivedCategoryFactorsh.hom.app K) ≫
      (upperStar A (pullback.fst c.g f)).leftDerivedFunctorCounit.app
        (((openImmersionLowerShriek A c.i).mapHomotopyCategory (.up ℤ)).obj K) =
    (upperStar A (pullback.snd c.g f)).leftDerivedFunctorCounit.app K ≫
      DerivedCategory.Qh.map
        (((GraphSheaf.transfer A f c).mapHomotopyCategory (.up ℤ) ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl
            (openImmersionLowerShriek A c.i ⋙ upperStar A (pullback.fst c.g f)))
              (.up ℤ)).inv).app K) := by
  have hh := homotopy_transfer_diagram
      (upperStar (A) (pullback.snd c.g f))
      (upperStar (A) (GraphSheaf.sectionMap f c))
      (openImmersionLowerShriek (A) (GraphSheaf.sectionMap f c))
      (upperStar (A) (pullback.fst c.g f))
      (openImmersionLowerShriek (A) c.i)
      (upperStar (A) c.i)
      (upperStar (A) (𝟙 U))
      (openImmersionLowerShriekUpperStarAdjunction (A) (GraphSheaf.sectionMap f c))
      (GraphSheaf.clopenAdjunction A f c)
      (openImmersionLowerShriekUpperStarAdjunction (A) c.i)
      (upperStarComp _ _ _ (𝟙 U) (GraphSheaf.section_snd f c).symm)
      (upperStarId (A) U)
      (upperStarComp _ _ _ c.i (GraphSheaf.section_fst f c).symm)
      (GraphSheaf.transfer A f c)
      (fun M => by
        simpa only [GraphSheaf.sectionIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
          Functor.map_comp, Category.assoc] using GraphSheaf.transfer_clopen A f c M) K
  apply transfer_normalization_diagram DerivedCategory.Qh _ _ _ _ _ _
    (compactificationEtaleGraphMap_app A f c (DerivedCategory.Qh.obj K)) _ hh
  exact clopenTransfer_fac A c.graphExchangeSection
    (((upperStar A (pullback.snd c.g f)).mapHomotopyCategory (.up ℤ)).obj K)
    (((upperStar A (pullback.fst c.g f)).mapHomotopyCategory (.up ℤ)).obj
      (((openImmersionLowerShriek A c.i).mapHomotopyCategory (.up ℤ)).obj K))
    ((upperStar A (pullback.snd c.g f)).leftDerivedFunctorCounit.app K)
    ((upperStar A (pullback.fst c.g f)).leftDerivedFunctor.map
        ((openImmersionLowerShriek A c.i).mapDerivedCategoryFactorsh.hom.app K) ≫
      (upperStar A (pullback.fst c.g f)).leftDerivedFunctorCounit.app
        (((openImmersionLowerShriek A c.i).mapHomotopyCategory (.up ℤ)).obj K))
    _ _ (by
      try dsimp only
      refine normalized_graph_diagram DerivedCategory.Qh
        (upperStar (A) c.graphExchangeSection).leftDerivedFunctor
        _ _ _ _ _
        ((leftDerivedUpperStarCompSectionIso (A)
          c.graphExchangeSection (pullback.snd c.g f) c.graphExchangeSection_snd).hom.app
            (DerivedCategory.Qh.obj K))
        ((graphOpenAdjunction A c.i).unit.app (DerivedCategory.Qh.obj K))
        _ _ _ _ _
        ((leftDerivedUpperStarComp A c.graphExchangeSection (pullback.fst c.g f)
          c.i c.graphExchangeSection_fst.symm).hom.app
          (DerivedCategory.Qh.obj
            (((openImmersionLowerShriek A c.i).mapHomotopyCategory (.up ℤ)).obj K))) _ _ _
        (compactificationEtaleGraphIso_hom_app A f c (DerivedCategory.Qh.obj K))
        (by
          try dsimp only
          exact normalized_section_diagram DerivedCategory.Qh _ _
            ((leftDerivedUpperStarComp A c.graphExchangeSection (pullback.snd c.g f)
              (𝟙 U) c.graphExchangeSection_snd.symm).inv.app
              (DerivedCategory.Qh.obj K))
            ((upperStar (A) (𝟙 U)).leftDerivedFunctorCounit.app K)
            _ _ _ _ rfl
            (leftDerivedUpperStarComp_inv_app_Qh_obj_comp_counit
              A c.graphExchangeSection (pullback.snd c.g f) (𝟙 U)
              c.graphExchangeSection_snd.symm K)
            (leftDerivedUpperStarId_hom_app_Qh_obj (A) K)) ?_ ?_ (by
          unfold graphOpenAdjunction derivedOpenImmersionLowerShriekUpperStarAdjunction
          exact transported_unit_fac (openImmersionLowerShriekUpperStarAdjunction
              (A) c.i)
              (leftDerivedUpperStarIsoMapDerivedCategory (A) c.i)
              (upperStar (A) c.i).leftDerivedFunctorCounit
              (by
                dsimp only [leftDerivedUpperStarIsoMapDerivedCategory]
                exact (upperStar (A) c.i).leftDerivedFunctorIsoMapDerivedCategory_hom_fac) K)
      · exact ((leftDerivedUpperStarComp (A)
          c.graphExchangeSection (pullback.fst c.g f) c.i
          c.graphExchangeSection_fst.symm).hom.naturality
          ((openImmersionLowerShriek (A) c.i).mapDerivedCategoryFactorsh.hom.app K)).symm
      · exact leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit (A)
          c.graphExchangeSection (pullback.fst c.g f) c.i c.graphExchangeSection_fst.symm
          (((openImmersionLowerShriek (A) c.i).mapHomotopyCategory (.up ℤ)).obj K))

/-- Proper base change is used only through its invertibility, proved below for finite rings. -/
private def GraphProperBaseChange (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A] : Prop :=
  ∀ {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X}, (sq : IsPullback g' f' f g) → IsProper f →
      IsIso (derivedBaseChangeMap A sq.toCommSq)

variable (Λ : Type u') [Category.{u + 1} Λ] [Abelian Λ]
  [IsGrothendieckAbelian.{u + 1} Λ] [HasSmallSiteSheafify Λ]
  [MonoidalCategory Λ] [MonoidalPreadditive Λ] [SymmetricCategory Λ]
  [MonoidalClosed Λ] [Abelian.HasFunctorialFlatResolution Λ] [Fact (GraphProperBaseChange Λ)]
section Construction
variable {X Y : Scheme.{u}} (e : X ⟶ Y) [_root_.AlgebraicGeometry.Etale e]
  (c : Compactification e)
private instance graphProperExchangeIso : IsIso (derivedBaseChangeMap (Λ)
    (IsPullback.of_hasPullback c.g e).toCommSq) :=
  (@Fact.out (GraphProperBaseChange Λ) inferInstance) (IsPullback.of_hasPullback c.g e) c.isProper

/-- The candidate unit `𝟭 ⟶ Rf_!(c) ⋙ Le^*` of an adjunction `Rf_!(c) ⊣ Le^*`:
`K ⟶ Rq_* Lq^* K ⟶ Rq_* Lq_Z^* Dj_! K ≅ Le^* Rp_* Dj_! K`. -/
@[irreducible]
private noncomputable def compactificationEtaleUnit :
    𝟭 _ ⟶ Rf_!(c)[Λ] ⋙ L((e)^*[Λ]) :=
  graph_unit_from_exchange
    L((pullback.snd c.g e)^*[Λ]) R((pullback.snd c.g e)_*[Λ])
    (derivedUpperStarLowerStarAdjunction Λ (pullback.snd c.g e))
    D((c.i)_!open[Λ]) L((pullback.fst c.g e)^*[Λ]) R((c.g)_*[Λ]) L((e)^*[Λ])
    (compactificationEtaleGraphMap Λ e c)
    (derivedBaseChangeMap Λ (IsPullback.of_hasPullback c.g e).toCommSq)

/-- The comparison `De_! ⟶ Rf_!(c)`: the transpose of
`AlgebraicGeometry.Etale.compactificationEtaleUnit` under `De_! ⊣ Le^*`. -/
@[irreducible]
private noncomputable def compactificationEtaleComparison :
    D(etaleLowerShriek (Λ) e inferInstance) ⟶ Rf_!(c)[Λ] :=
  transpose_natTrans (derivedEtaleLowerShriekAdjunction Λ e) Rf_!(c)[Λ]
    (compactificationEtaleUnit Λ e c)

end Construction
section Unfold
variable {X Y : Scheme.{u}} (e : X ⟶ Y) [_root_.AlgebraicGeometry.Etale e]
  (c : Compactification e)
private lemma compactificationEtaleUnit_app
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (Λ))) :
    (compactificationEtaleUnit Λ e c).app N =
      (derivedUpperStarLowerStarAdjunction _ (pullback.snd c.g e)).unit.app N ≫
        R((pullback.snd c.g e)_*[Λ]).map
          ((compactificationEtaleGraphMap Λ e c).app N) ≫
        inv ((derivedBaseChangeMap (Λ)
          (IsPullback.of_hasPullback c.g e).toCommSq).app
            (D((c.i)_!open[Λ]).obj N)) := by
  unfold compactificationEtaleUnit
  exact graph_unit_from_exchange_app
    L((pullback.snd c.g e)^*[Λ]) R((pullback.snd c.g e)_*[Λ])
    (derivedUpperStarLowerStarAdjunction Λ (pullback.snd c.g e))
    D((c.i)_!open[Λ]) L((pullback.fst c.g e)^*[Λ]) R((c.g)_*[Λ]) L((e)^*[Λ])
    (compactificationEtaleGraphMap Λ e c)
    (derivedBaseChangeMap Λ (IsPullback.of_hasPullback c.g e).toCommSq) N

private lemma compactificationEtaleUnit_fac
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology Λ)) :
    (compactificationEtaleUnit Λ e c).app N ≫
      (derivedBaseChangeMap Λ (IsPullback.of_hasPullback c.g e).toCommSq).app
        (D((c.i)_!open[Λ]).obj N) =
    (derivedUpperStarLowerStarAdjunction Λ (pullback.snd c.g e)).unit.app N ≫
      R((pullback.snd c.g e)_*[Λ]).map
        ((compactificationEtaleGraphMap Λ e c).app N) := by
  rw [compactificationEtaleUnit_app]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

end Unfold
section BaseChange
variable {X Y X' Y' : Scheme.{u}} {e : X ⟶ Y} {g : Y' ⟶ Y}
  {e' : X' ⟶ Y'} {g' : X' ⟶ X}
  (sq : IsPullback g' e' e g) (c : Compactification e)
  [_root_.AlgebraicGeometry.Etale e] [_root_.AlgebraicGeometry.Etale e']
omit [Fact (GraphProperBaseChange Λ)] [_root_.AlgebraicGeometry.Etale e]
  [_root_.AlgebraicGeometry.Etale e'] in
/-- The compact-support base change `Ex_!(c)` at `N`, with the squares of the base-changed
compactification typed by its scheme. -/
private lemma rightDerivedLowerShriekOfCompactificationBaseChangeMap_app_eq
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (Λ))) :
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap (Λ) sq c).app N =
      (derivedBaseChangeMap (Λ)
          (c.isPullback_graphExchangeBaseFst sq).toCommSq).app
          (D((c.i)_!open[Λ]).obj N) ≫
        R(((c.ofIsPullback sq).g)_*[Λ]).map
          ((derivedOpenImmersionLowerShriekBaseChangeIso _
            (c.graphExchangeOpenSquare sq)).inv.app N) := by
  simp only [rightDerivedLowerShriekOfCompactificationBaseChangeMap, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.id_comp]
  erw [Category.comp_id]

-- the derived functors involved are large terms
/-- **The candidate unit of `Rf_!(c) ⊣ Le^*` commutes with base change**: for a cartesian square
`g' ≫ e = e' ≫ g` and the base change `c'` of the compactification `c`, the unit at
`Lg'^* N` for `c'` is `Lg'^*` of the unit at `N` for `c`, followed by the canonical isomorphism
`Lg'^* Le^* ≅ Le'^* Lg^*` and `Le'^*` of the compact-support base change `Ex_!(c)`. -/
private theorem compactificationEtaleUnit_baseChange
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (Λ))) :
    L((g')^*[Λ]).map ((compactificationEtaleUnit Λ e c).app N) ≫
      (derivedSquareUpperStarIso _ sq.toCommSq).inv.app (Rf_!(c)[Λ].obj N) ≫
      L((e')^*[Λ]).map
        ((rightDerivedLowerShriekOfCompactificationBaseChangeMap _ sq c).app N) =
    (compactificationEtaleUnit Λ e' (c.ofIsPullback sq)).app
      (L((g')^*[Λ]).obj N) := by
  exact unit_cube_diagram
    L((g')^*[Λ]) R((pullback.snd c.g e)_*[Λ])
    L((c.graphExchangeSectionBaseChange sq)^*[Λ])
    R((pullback.snd (c.ofIsPullback sq).g e')_*[Λ])
    L((e')^*[Λ]) L((pullback.fst (c.ofIsPullback sq).g e')^*[Λ])
    R(((c.ofIsPullback sq).g)_*[Λ])
    (derivedBaseChangeMap Λ (c.isPullback_graphExchangeSectionBaseChange sq).toCommSq)
    (derivedBaseChangeMap Λ (IsPullback.of_hasPullback (c.ofIsPullback sq).g e').toCommSq)
    ((derivedBaseChangeMap Λ (IsPullback.of_hasPullback c.g e).toCommSq).app
      (D((c.i)_!open[Λ]).obj N))
    ((derivedBaseChangeMap Λ (c.isPullback_graphExchangeBaseFst sq).toCommSq).app
      (D((c.i)_!open[Λ]).obj N))
    ((derivedSquareUpperStarIso Λ sq.toCommSq).inv.app (Rf_!(c)[Λ].obj N))
    ((derivedSquareUpperStarIso Λ (⟨c.graphExchangeSectionBaseChange_fst sq⟩ :
      CommSq (c.graphExchangeSectionBaseChange sq)
        (pullback.fst (c.ofIsPullback sq).g e') (pullback.fst c.g e)
        (c.graphExchangeBaseFst sq))).inv.app (D((c.i)_!open[Λ]).obj N))
    ((derivedSquareUpperStarIso Λ
      (c.isPullback_graphExchangeSectionBaseChange sq).toCommSq).hom.app N)
    ((derivedOpenImmersionLowerShriekBaseChangeIso Λ
      (c.graphExchangeOpenSquare sq)).inv.app N)
    ((compactificationEtaleGraphMap Λ e c).app N)
    ((compactificationEtaleGraphMap Λ e' (c.ofIsPullback sq)).app (L((g')^*[Λ]).obj N))
    ((derivedUpperStarLowerStarAdjunction Λ (pullback.snd c.g e)).unit.app N)
    ((derivedUpperStarLowerStarAdjunction Λ (pullback.snd (c.ofIsPullback sq).g e')).unit.app
      (L((g')^*[Λ]).obj N))
    ((compactificationEtaleUnit Λ e c).app N)
    ((compactificationEtaleUnit Λ e' (c.ofIsPullback sq)).app (L((g')^*[Λ]).obj N))
    ((rightDerivedLowerShriekOfCompactificationBaseChangeMap Λ sq c).app N)
    (compactificationEtaleUnit_app Λ e c N)
    (compactificationEtaleUnit_app Λ e' (c.ofIsPullback sq) (L((g')^*[Λ]).obj N))
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap_app_eq Λ sq c N)
    (derivedBaseChangeMap_cube Λ
      (IsPullback.of_hasPullback c.g e).toCommSq
      (c.isPullback_graphExchangeBaseFst sq).toCommSq
      (c.isPullback_graphExchangeSectionBaseChange sq).toCommSq
      (IsPullback.of_hasPullback (c.ofIsPullback sq).g e').toCommSq sq.toCommSq
      (⟨c.graphExchangeSectionBaseChange_fst sq⟩ :
        CommSq (c.graphExchangeSectionBaseChange sq)
          (pullback.fst (c.ofIsPullback sq).g e') (pullback.fst c.g e)
          (c.graphExchangeBaseFst sq)) (D((c.i)_!open[Λ]).obj N))
    (map_unit_derivedBaseChangeMap_app Λ
      (c.isPullback_graphExchangeSectionBaseChange sq).toCommSq N)
    (compactificationEtaleGraphMap_baseChange Λ sq c N)

end BaseChange
section Transpose
variable {X Y : Scheme.{u}} (e : X ⟶ Y) [_root_.AlgebraicGeometry.Etale e]
  (c : Compactification e)
/-- The comparison `De_! ⟶ Rf_!(c)` is the transpose of the candidate unit under `De_! ⊣ Le^*`. -/
@[reassoc]
private lemma unit_map_compactificationEtaleComparison
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (Λ))) :
    (derivedEtaleLowerShriekAdjunction _ e).unit.app N ≫
        L((e)^*[Λ]).map ((compactificationEtaleComparison Λ e c).app N) =
      (compactificationEtaleUnit Λ e c).app N := by
  unfold compactificationEtaleComparison
  exact unit_transpose_natTrans (derivedEtaleLowerShriekAdjunction Λ e) Rf_!(c)[Λ]
    (compactificationEtaleUnit Λ e c) N

end Transpose
section BaseChange
variable {X Y X' Y' : Scheme.{u}} {e : X ⟶ Y} {g : Y' ⟶ Y}
  {e' : X' ⟶ Y'} {g' : X' ⟶ X}
  (sq : IsPullback g' e' e g) (c : Compactification e)
  [_root_.AlgebraicGeometry.Etale e] [_root_.AlgebraicGeometry.Etale e']
/-- **The comparison `De_! ⟶ Rf_!(c)` commutes with base change**: for a cartesian square
`g' ≫ e = e' ≫ g`, the comparison for the base change `c'` of `c` at `Lg'^* N` is `Lg^*` of
the comparison at `N`, read through the base change isomorphisms `De'_! Lg'^* ≅ Lg^* De_!` and
`Ex_!(c)`. -/
private theorem compactificationEtaleComparison_baseChange
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (Λ))) :
    (derivedEtaleLowerShriekBaseChangeIso _ sq).hom.app N ≫
      L((g)^*[Λ]).map ((compactificationEtaleComparison Λ e c).app N) ≫
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap _ sq c).app N =
    (compactificationEtaleComparison Λ e' (c.ofIsPullback sq)).app
      (L((g')^*[Λ]).obj N) := by
  exact transpose_baseChange_diagram
    D(etaleLowerShriek Λ e inferInstance) L((e)^*[Λ])
    D(etaleLowerShriek Λ e' inferInstance) L((e')^*[Λ])
    (derivedEtaleLowerShriekAdjunction Λ e) (derivedEtaleLowerShriekAdjunction Λ e')
    L((g')^*[Λ]) L((g)^*[Λ]) Rf_!(c)[Λ] Rf_!(c.ofIsPullback sq)[Λ]
    (derivedSquareUpperStarIso Λ sq.toCommSq)
    (derivedEtaleLowerShriekBaseChangeIso Λ sq).hom
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap Λ sq c)
    (compactificationEtaleComparison Λ e c)
    (compactificationEtaleComparison Λ e' (c.ofIsPullback sq))
    (compactificationEtaleUnit Λ e c)
    (compactificationEtaleUnit Λ e' (c.ofIsPullback sq))
    (unit_map_compactificationEtaleComparison Λ e c)
    (unit_map_compactificationEtaleComparison Λ e' (c.ofIsPullback sq))
    (unit_map_derivedEtaleLowerShriekBaseChangeIso Λ sq)
    (compactificationEtaleUnit_baseChange Λ sq c) N

end BaseChange
end AlgebraicGeometry.Etale.GraphExchange

namespace AlgebraicGeometry.Etale.GraphExchange
private instance finiteRingGraphProperBaseChange
    (A : Type (u + 1)) [CommRing A] [Finite A] :
    Fact (GraphProperBaseChange (ModuleCat.{u + 1} A)) := by
  constructor
  intro X Y X' Y' f g f' g' sq hp
  letI := hp
  exact isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring A
    isAddTorsion_of_finite sq
end AlgebraicGeometry.Etale.GraphExchange

private theorem localized_adjunction_ext
    {C D H : Type*} [Category C] [Category D] [Category H]
    (Q : H ⥤ C) (W : MorphismProperty H) [Q.IsLocalization W]
    (E : C ⥤ D) (F : D ⥤ C) (a : E ⊣ F) (T : C ⥤ D)
    (σ φ : E ⟶ T) (ν : 𝟭 C ⟶ T ⋙ F)
    (Z : H → C) (β : ∀ K, F.obj (T.obj (Q.obj K)) ⟶ Z K)
    [∀ K, IsIso (β K)] (χ : ∀ K, Q.obj K ⟶ Z K)
    (hφ : ∀ K, a.unit.app (Q.obj K) ≫ F.map (φ.app (Q.obj K)) = ν.app (Q.obj K))
    (hν : ∀ K, ν.app (Q.obj K) ≫ β K = χ K)
    (hσ : ∀ K, a.unit.app (Q.obj K) ≫ F.map (σ.app (Q.obj K)) ≫ β K = χ K) :
    σ = φ := by
  apply Localization.natTrans_ext Q W
  intro K
  apply (a.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  rw [hφ K, ← cancel_mono (β K)]
  simpa only [Category.assoc] using (hσ K).trans (hν K).symm

namespace AlgebraicGeometry.Etale.GraphExchange
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

end AlgebraicGeometry.Etale.GraphExchange
namespace AlgebraicGeometry.Etale.GraphExchange

private theorem baseChange_homotopy_fac
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
    [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (K : HomotopyCategory (Sheaf X.smallEtaleTopology A) (.up ℤ)) :
    (upperStar A g).leftDerivedFunctor.map ((lowerStar A f).rightDerivedFunctorUnit.app K) ≫
      (derivedBaseChangeMap A sq).app (DerivedCategory.Qh.obj K) ≫
      (lowerStar A f').rightDerivedFunctor.map ((upperStar A g').leftDerivedFunctorCounit.app K) =
    (upperStar A g).leftDerivedFunctorCounit.app
        (((lowerStar A f).mapHomotopyCategory (.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map (((baseChangeMap A sq).mapHomotopyCategory (.up ℤ)).app K) ≫
      (lowerStar A f').rightDerivedFunctorUnit.app
        (((upperStar A g').mapHomotopyCategory (.up ℤ)).obj K) := by
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  simpa only [NatTrans.mapHomotopyCategory_app, HomotopyCategory.quotient_obj_as] using
    derivedBaseChangeMap_app_fac A sq M

private theorem graph_comparison_unit_fac
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
    [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    (c : Compactification f)
    (a : etaleLowerShriek A f inferInstance ⟶
      openImmersionLowerShriek A c.i ⋙ lowerStar A c.g)
    (σ : (etaleLowerShriek A f inferInstance).mapDerivedCategory ⟶
      rightDerivedLowerShriekOfCompactification A c)
    (hσ : ∀ K : HomotopyCategory (Sheaf U.smallEtaleTopology A) (.up ℤ),
      σ.app (DerivedCategory.Qh.obj K) =
      (etaleLowerShriek A f inferInstance).mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).app K) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl
            (openImmersionLowerShriek A c.i ⋙ lowerStar A c.g)) (.up ℤ)).inv.app K) ≫
        (lowerStar A c.g).rightDerivedFunctorUnit.app
          (((openImmersionLowerShriek A c.i).mapHomotopyCategory (.up ℤ)).obj K) ≫
        (lowerStar A c.g).rightDerivedFunctor.map
          ((openImmersionLowerShriek A c.i).mapDerivedCategoryFactorsh.inv.app K))
    (hH : ∀ M, (etaleLowerShriekUpperStarAdjunction A f inferInstance).unit.app M ≫
        (upperStar A f).map (a.app M) ≫
        (baseChangeMap A (IsPullback.of_hasPullback c.g f).toCommSq).app
          ((openImmersionLowerShriek A c.i).obj M) =
      (upperStarLowerStarAdjunction A (pullback.snd c.g f)).unit.app M ≫
        (lowerStar A (pullback.snd c.g f)).map ((GraphSheaf.transfer A f c).app M))
    (K : HomotopyCategory (Sheaf U.smallEtaleTopology A) (.up ℤ)) :
    (derivedEtaleLowerShriekAdjunction A f).unit.app (DerivedCategory.Qh.obj K) ≫
      (upperStar A f).leftDerivedFunctor.map (σ.app (DerivedCategory.Qh.obj K)) ≫
      (derivedBaseChangeMap A (IsPullback.of_hasPullback c.g f).toCommSq).app
        ((openImmersionLowerShriek A c.i).mapDerivedCategory.obj (DerivedCategory.Qh.obj K)) =
    (derivedUpperStarLowerStarAdjunction A (pullback.snd c.g f)).unit.app
        (DerivedCategory.Qh.obj K) ≫
      (lowerStar A (pullback.snd c.g f)).rightDerivedFunctor.map
        ((compactificationEtaleGraphMap A f c).app (DerivedCategory.Qh.obj K)) := by
  let τH := (GraphSheaf.transfer (A) f c).mapHomotopyCategory (.up ℤ) ≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl
      (openImmersionLowerShriek (A) c.i ⋙
        upperStar (A) (pullback.fst c.g f))) (.up ℤ)).inv
  let E := etaleLowerShriek (A) f inferInstance
  let F := upperStar (A) f
  let J := openImmersionLowerShriek (A) c.i
  let R := lowerStar (A) c.g
  let V := upperStar (A) (pullback.fst c.g f)
  let Q := lowerStar (A) (pullback.snd c.g f)
  let P := upperStar (A) (pullback.snd c.g f)
  let JK := (J.mapHomotopyCategory (.up ℤ)).obj K
  let aH := (a.mapHomotopyCategory (.up ℤ)).app K ≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (J ⋙ R)) (.up ℤ)).inv.app K
  let bcH := (baseChangeMap A
    (IsPullback.of_hasPullback c.g f).toCommSq).mapHomotopyCategory (.up ℤ)
  refine double_unit_diagram F.leftDerivedFunctor R.rightDerivedFunctor
    V.leftDerivedFunctor Q.rightDerivedFunctor
    DerivedCategory.Qh DerivedCategory.Qh DerivedCategory.Qh
    (F.mapHomotopyCategory (.up ℤ)) (Q.mapHomotopyCategory (.up ℤ))
    F.leftDerivedFunctorCounit Q.rightDerivedFunctorUnit
    (derivedBaseChangeMap A (IsPullback.of_hasPullback c.g f).toCommSq)
    ((derivedEtaleLowerShriekAdjunction A f).unit.app (DerivedCategory.Qh.obj K))
    ((derivedUpperStarLowerStarAdjunction A (pullback.snd c.g f)).unit.app
      (DerivedCategory.Qh.obj K))
    (σ.app (DerivedCategory.Qh.obj K))
    (J.mapDerivedCategoryFactorsh.hom.app K) (V.leftDerivedFunctorCounit.app JK)
    aH (R.rightDerivedFunctorUnit.app JK)
    (E.mapDerivedCategoryFactorsh.hom.app K) (P.leftDerivedFunctorCounit.app K)
    (bcH.app JK) ((compactificationEtaleGraphMap A f c).app (DerivedCategory.Qh.obj K)) (τH.app K)
    (((etaleLowerShriekUpperStarAdjunction A f inferInstance).mapHomotopyCategory
      (.up ℤ)).unit.app K)
    (((upperStarLowerStarAdjunction A (pullback.snd c.g f)).mapHomotopyCategory
      (.up ℤ)).unit.app K)
    (comparison_normalization_diagram DerivedCategory.Qh R.rightDerivedFunctor
          (J.mapDerivedCategoryFactorsh.app K)
          (E.mapDerivedCategoryFactorsh.hom.app K)
          ((a.mapHomotopyCategory (.up ℤ)).app K)
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (J ⋙ R)) (.up ℤ)).inv.app K)
          (R.rightDerivedFunctorUnit.app JK) (σ.app (DerivedCategory.Qh.obj K)) (hσ K)) ?_ ?_
    (by
      unfold derivedEtaleLowerShriekAdjunction derivedEtaleLowerShriekMapAdjunction
      exact transported_unit_fac (etaleLowerShriekUpperStarAdjunction
          (A) f inferInstance)
          (leftDerivedUpperStarIsoMapDerivedCategory (A) f)
          (upperStar (A) f).leftDerivedFunctorCounit
          (by
            dsimp only [leftDerivedUpperStarIsoMapDerivedCategory]
            exact (upperStar (A) f).leftDerivedFunctorIsoMapDerivedCategory_hom_fac) K)
    (by
      unfold derivedUpperStarLowerStarAdjunction
      exact ((upperStarLowerStarAdjunction (A) (pullback.snd c.g f)).mapHomotopyCategory
        (.up ℤ)).derivedη_fac_app (HomotopyCategory.quasiIso _ (.up ℤ))
          (upperStar (A) (pullback.snd c.g f)).leftDerivedFunctorCounit
          (lowerStar (A) (pullback.snd c.g f)).rightDerivedFunctorUnit K)
    (by
      exact homotopy_unit_diagram
          (etaleLowerShriek A f inferInstance)
          (upperStar A f)
          (openImmersionLowerShriek A c.i)
          (lowerStar A c.g)
          (upperStar A (pullback.fst c.g f))
          (lowerStar A (pullback.snd c.g f))
          (upperStar A (pullback.snd c.g f))
          (etaleLowerShriekUpperStarAdjunction A f inferInstance)
          (upperStarLowerStarAdjunction A (pullback.snd c.g f))
          a (GraphSheaf.transfer A f c)
          (baseChangeMap A (IsPullback.of_hasPullback c.g f).toCommSq)
          hH K)
  · exact baseChange_homotopy_fac A (IsPullback.of_hasPullback c.g f).toCommSq JK
  · exact graph_transfer_homotopy_fac A f c K

private theorem graph_comparison_eq_of_normalizations
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
    [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [Fact (GraphProperBaseChange A)]
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    (c : Compactification f)
    (a : etaleLowerShriek A f inferInstance ⟶
      openImmersionLowerShriek A c.i ⋙ lowerStar A c.g)
    (σ : (etaleLowerShriek A f inferInstance).mapDerivedCategory ⟶
      rightDerivedLowerShriekOfCompactification A c)
    (hσ : ∀ K : HomotopyCategory (Sheaf U.smallEtaleTopology A) (.up ℤ),
      σ.app (DerivedCategory.Qh.obj K) =
      (etaleLowerShriek A f inferInstance).mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).app K) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl
            (openImmersionLowerShriek A c.i ⋙ lowerStar A c.g)) (.up ℤ)).inv.app K) ≫
        (lowerStar A c.g).rightDerivedFunctorUnit.app
          (((openImmersionLowerShriek A c.i).mapHomotopyCategory (.up ℤ)).obj K) ≫
        (lowerStar A c.g).rightDerivedFunctor.map
          ((openImmersionLowerShriek A c.i).mapDerivedCategoryFactorsh.inv.app K))
    (hH : ∀ M, (etaleLowerShriekUpperStarAdjunction A f inferInstance).unit.app M ≫
        (upperStar A f).map (a.app M) ≫
        (baseChangeMap A (IsPullback.of_hasPullback c.g f).toCommSq).app
          ((openImmersionLowerShriek A c.i).obj M) =
      (upperStarLowerStarAdjunction A (pullback.snd c.g f)).unit.app M ≫
        (lowerStar A (pullback.snd c.g f)).map ((GraphSheaf.transfer A f c).app M))
    : σ = compactificationEtaleComparison A f c := by
  exact localized_adjunction_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf U.smallEtaleTopology (A)) (.up ℤ))
    _ _ (derivedEtaleLowerShriekAdjunction (A) f) _
    (σ)
    (compactificationEtaleComparison (A) f c)
    (compactificationEtaleUnit (A) f c)
    (fun K ↦ R((pullback.snd c.g f)_*[A]).obj
      (L((pullback.fst c.g f)^*[A]).obj
        (D((c.i)_!open[A]).obj (DerivedCategory.Qh.obj K))))
    (fun K ↦ (derivedBaseChangeMap (A)
      (IsPullback.of_hasPullback c.g f).toCommSq).app
        (D((c.i)_!open[A]).obj (DerivedCategory.Qh.obj K)))
    (fun K ↦ (derivedUpperStarLowerStarAdjunction (A)
      (pullback.snd c.g f)).unit.app (DerivedCategory.Qh.obj K) ≫
        R((pullback.snd c.g f)_*[A]).map
          ((compactificationEtaleGraphMap (A) f c).app
            (DerivedCategory.Qh.obj K)))
    (fun K ↦ unit_map_compactificationEtaleComparison
      (A) f c (DerivedCategory.Qh.obj K))
    (fun K ↦ compactificationEtaleUnit_fac
      (A) f c (DerivedCategory.Qh.obj K)) (fun K ↦ graph_comparison_unit_fac A f c a σ hσ hH K)

private theorem graph_comparison_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    (c : Compactification f) :
    compactSupportDerivedComparison A f c (etaleCompactificationGraphMap A f c) =
      compactificationEtaleComparison (ModuleCat.{u + 1} A) f c := by
  exact graph_comparison_eq_of_normalizations (ModuleCat.{u + 1} A) f c
    (etaleCompactificationGraphMap A f c)
    (compactSupportDerivedComparison A f c (etaleCompactificationGraphMap A f c))
    (fun K ↦ compactSupportDerivedComparison_app A f c
      (etaleCompactificationGraphMap A f c) K)
    (GraphSheaf.comparison_unit A f c)

end AlgebraicGeometry.Etale.GraphExchange

namespace AlgebraicGeometry.Etale.GraphExchange
private theorem generic_sum_exchange_transport
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
    [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {U X X' : Scheme.{u}} (f : U ⟶ X) [Etale f] (g : X' ⟶ X) :
    ((Functor.mapDerivedCategoryCompIso
        (etaleLowerShriek A f inferInstance) (upperStar A g)) ≪≫
      Functor.mapDerivedCategoryNatIso (@asIso _ _ _ _ _
        (isIso_etaleLowerShriekSquareBaseChangeMap A
          (IsPullback.of_hasPullback g f).flip)).symm ≪≫
      (Functor.mapDerivedCategoryCompIso (upperStar A (pullback.snd g f))
        (etaleLowerShriek A (pullback.fst g f) inferInstance)).symm).hom =
      Functor.whiskerLeft (etaleLowerShriek A f
        inferInstance).mapDerivedCategory
        (leftDerivedUpperStarIsoMapDerivedCategory A g).inv ≫
      (derivedEtaleLowerShriekBaseChangeIso A
        (IsPullback.of_hasPullback g f).flip).inv ≫
      Functor.whiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory A
          (pullback.snd g f)).hom _ := by
  have hb :
      (Functor.mapDerivedCategoryCompIso
        (etaleLowerShriek A f inferInstance) (upperStar A g)) ≪≫
      Functor.mapDerivedCategoryNatIso (@asIso _ _ _ _ _
        (isIso_etaleLowerShriekSquareBaseChangeMap A
          (IsPullback.of_hasPullback g f).flip)).symm ≪≫
      (Functor.mapDerivedCategoryCompIso (upperStar A (pullback.snd g f))
        (etaleLowerShriek A (pullback.fst g f) inferInstance)).symm =
      (mapDerivedCategoryEtaleLowerShriekBaseChangeIso A
        (IsPullback.of_hasPullback g f).flip).symm := by
    simp only [mapDerivedCategoryEtaleLowerShriekBaseChangeIso,
      Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc,
      mapDerivedCategoryNatIso_symm_iso]
  rw [hb]
  exact (iso_conjugation_cancel
    (Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory A
        (pullback.snd g f)) _)
    (mapDerivedCategoryEtaleLowerShriekBaseChangeIso A
      (IsPullback.of_hasPullback g f).flip)
    (Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory A g).symm)).symm

private theorem sum_exchange_transport
    (A : Type (u + 1)) [CommRing A]
    {U X X' : Scheme.{u}} (f : U ⟶ X) [Etale f] (g : X' ⟶ X) :
    (exactEtaleSumExchange A f g).hom =
      Functor.whiskerLeft (etaleLowerShriek (ModuleCat.{u + 1} A) f
        inferInstance).mapDerivedCategory
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).inv ≫
      (derivedEtaleLowerShriekBaseChangeIso (ModuleCat.{u + 1} A)
        (IsPullback.of_hasPullback g f).flip).inv ≫
      Functor.whiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
          (pullback.snd g f)).hom _ := by
  exact generic_sum_exchange_transport (ModuleCat.{u + 1} A) f g

private theorem comparison_exact_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X X' : Scheme.{u}} (f : U ⟶ X) [Etale f] (c : Compactification f) (g : X' ⟶ X) :
    Functor.whiskerRight (compactificationEtaleComparison (ModuleCat.{u + 1} A) f c)
        (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ≫
      exactCompactSupportExchange A c g =
    (exactEtaleSumExchange A f g).hom ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) (pullback.snd g f)).mapDerivedCategory
        (compactificationEtaleComparison (ModuleCat.{u + 1} A) (pullback.fst g f)
          (c.ofIsPullback (IsPullback.of_hasPullback g f).flip)) := by
  rw [sum_exchange_transport]
  simpa only [exactCompactSupportExchange, Category.assoc] using
    (transport_baseChange_diagram
    D(etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance) Rf_!(c)[ModuleCat.{u + 1} A]
    D(etaleLowerShriek (ModuleCat.{u + 1} A) (pullback.fst g f) inferInstance)
    Rf_!(c.ofIsPullback (IsPullback.of_hasPullback g f).flip)[ModuleCat.{u + 1} A]
    L((g)^*[ModuleCat.{u + 1} A]) D((g)^*[ModuleCat.{u + 1} A])
    L((pullback.snd g f)^*[ModuleCat.{u + 1} A])
    D((pullback.snd g f)^*[ModuleCat.{u + 1} A])
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (pullback.snd g f))
    (derivedEtaleLowerShriekBaseChangeIso (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback g f).flip)
    (compactificationEtaleComparison (ModuleCat.{u + 1} A) f c)
    (compactificationEtaleComparison (ModuleCat.{u + 1} A) (pullback.fst g f)
      (c.ofIsPullback (IsPullback.of_hasPullback g f).flip))
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback g f).flip c)
    (compactificationEtaleComparison_baseChange (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback g f).flip c))

end AlgebraicGeometry.Etale.GraphExchange
attribute [-instance] AlgebraicGeometry.Etale.GraphExchange.graphUpperAdditive
  AlgebraicGeometry.Etale.GraphExchange.graphUpperPreservesFiniteLimits
  AlgebraicGeometry.Etale.GraphExchange.graphUpperPreservesFiniteColimits
  AlgebraicGeometry.Etale.GraphExchange.graphLowerAdditive
  AlgebraicGeometry.Etale.GraphExchange.graphLowerPreservesFiniteLimits
  AlgebraicGeometry.Etale.GraphExchange.graphOpenAdditive
  AlgebraicGeometry.Etale.GraphExchange.graphOpenPreservesFiniteLimits
  AlgebraicGeometry.Etale.GraphExchange.graphOpenPreservesFiniteColimits
  AlgebraicGeometry.Etale.GraphExchange.graphEtaleAdditive
  AlgebraicGeometry.Etale.GraphExchange.graphEtalePreservesFiniteLimits
  AlgebraicGeometry.Etale.GraphExchange.graphEtalePreservesFiniteColimits
  AlgebraicGeometry.Etale.GraphExchange.graphSheafLocalization
attribute [-instance] AlgebraicGeometry.Etale.GraphExchange.graphSheafColimits
  AlgebraicGeometry.Etale.GraphExchange.graphSheafCountableCoproducts
  AlgebraicGeometry.Etale.GraphExchange.graphSheafExactColimits
  AlgebraicGeometry.Etale.GraphExchange.graphSheafFlatResolution
  AlgebraicGeometry.Etale.GraphExchange.graphSheafKInjective
  AlgebraicGeometry.Etale.GraphExchange.graphSheafGrothendieck
  AlgebraicGeometry.Etale.cachedColimits
  AlgebraicGeometry.Etale.cachedCoproducts
  AlgebraicGeometry.Etale.cachedExactColimits
end

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The forward graph map commutes with the specified compact-support exchange at a
geometric point over an arbitrary scheme. This is equality of unbounded derived
transformations; neither scheme needs to be Noetherian or quasi-compact.
Source: SGA 4 XVII 5.2.2 and 6.2.11; Stacks Project Tags 03S6, 07A7, 0E46 and 0E47.
(auxiliary; not a blueprint node).

Proof:
Construct the derived transfer through the open and closed graph of the compactification.
Pullback composition coherence and the open-extension adjunction identify its base change;
the proper base-change cube gives the corresponding equation for its adjoint comparison.
On homotopy representatives, the unit and counit formulas identify this transfer with the
termwise sheaf graph transfer. The sheaf graph-unit equation and proper base-change
normalization therefore identify the comparison with the specified descended graph map.
Localization full faithfulness extends the identification to unbounded derived categories.
Finally transport the base-change equation along the canonical exact-functor comparisons
and specialize the base morphism to the geometric point. The argument includes empty
fibres and the zero ring -/
theorem compactSupportGraphDerivedComparison_geometric_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    (c : Compactification f) (y : X) :
    Functor.whiskerRight
        (compactSupportDerivedComparison A f c (etaleCompactificationGraphMap A f c))
        (upperStar (ModuleCat.{u + 1} A) (X.algClosurePoint y)).mapDerivedCategory ≫
      exactCompactSupportExchange A c (X.algClosurePoint y) =
    (exactEtaleSumExchange A f (X.algClosurePoint y)).hom ≫
      Functor.whiskerLeft
        (upperStar (ModuleCat.{u + 1} A)
          (pullback.snd (X.algClosurePoint y) f)).mapDerivedCategory
        (compactSupportDerivedComparison A (pullback.fst (X.algClosurePoint y) f)
          (c.ofIsPullback (IsPullback.of_hasPullback (X.algClosurePoint y) f).flip)
          (etaleCompactificationGraphMap A (pullback.fst (X.algClosurePoint y) f)
            (c.ofIsPullback (IsPullback.of_hasPullback (X.algClosurePoint y) f).flip))) := by
  rw [GraphExchange.graph_comparison_eq A f c,
    GraphExchange.graph_comparison_eq A (pullback.fst (X.algClosurePoint y) f)
      (c.ofIsPullback (IsPullback.of_hasPullback (X.algClosurePoint y) f).flip)]
  exact GraphExchange.comparison_exact_baseChange A f c (X.algClosurePoint y)

end AlgebraicGeometry.Etale
