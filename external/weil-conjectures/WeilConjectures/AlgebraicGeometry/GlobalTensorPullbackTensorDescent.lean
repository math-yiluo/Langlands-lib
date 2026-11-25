/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.GlobalTensorPullbackMatesIsIso
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo
import WeilConjectures.Mathlib.CategoryTheory.Whiskering

/-! # Descent of the normalized global tensor comparison

Source: Stacks Project, Tag 079U. (blueprint: lem-sc-global-tensor-pullback-tensor-descent).
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable (X : Scheme.{u})
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

local instance globalTensorDescentDataCommRing :
    CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))
local instance globalTensorDescentDataMonoidal :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.toRingedSpace.sheaf
local instance globalTensorDescentDataSymmetric :
    SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.toRingedSpace.sheaf
attribute [local instance] globalPullbackMatesColimits
local instance globalTensorDescentDataPreadditive :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).1
local instance globalTensorDescentDataClosed :
    MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).2.1
local instance globalTensorDescentDataFlatResolution : Abelian.HasFunctorialFlatResolution
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  schemeModule_hasFunctorialFlatResolution X

private theorem exists_leftDerivedTensorIso
    {A₁ A₂ B₁ B₂ E : Type*}
    [Category* A₁] [Category* A₂] [Category* B₁] [Category* B₂] [Category* E]
    (W₁ : MorphismProperty A₁) (W₂ : MorphismProperty A₂)
    [W₁.ContainsIdentities] [W₂.ContainsIdentities]
    (Q₁ : A₁ ⥤ B₁) (Q₂ : A₂ ⥤ B₂) [Q₁.IsLocalization W₁] [Q₂.IsLocalization W₂]
    (U V : B₁ ⥤ B₂ ⥤ E) (F G : A₁ ⥤ A₂ ⥤ E)
    (βU : (((Functor.whiskeringLeft₂ E).obj Q₁).obj Q₂).obj U ⟶ F)
    (βV : (((Functor.whiskeringLeft₂ E).obj Q₁).obj Q₂).obj V ⟶ G)
    [U.IsLeftDerivedFunctor₂ βU W₁ W₂] [V.IsLeftDerivedFunctor₂ βV W₁ W₂]
    (τ : F ≅ G) :
    ∃ δ : U ≅ V, ∀ K M,
      ((δ.app (Q₁.obj K)).app (Q₂.obj M)).hom ≫ (βV.app K).app M =
        (βU.app K).app M ≫ ((τ.app K).app M).hom := by
  refine ⟨Functor.leftDerived₂NatIso V βV W₁ W₂ U βU τ, ?_⟩
  intro K M
  exact Functor.leftDerived₂NatTrans_app_app V βV W₁ W₂ U βU τ.hom K M

private theorem tensorComparison_of_kflat
    {C D DC DD : Type*}
    [Category* C] [Category* D] [Category* DC] [Category* DD]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalCategory DC] [MonoidalCategory DD]
    (W : MorphismProperty C) [W.RespectsIso] [W.ContainsIdentities]
    [W.localizerMorphismKFlat.IsLeftDerivabilityStructure]
    (Q : C ⥤ DC) [Q.IsLocalization W] [Q.LaxMonoidal]
    (R : D ⥤ DD) [R.LaxMonoidal] (Ph : C ⥤ D) (L : DC ⥤ DD)
    (α : Q ⋙ L ⟶ Ph ⋙ R)
    (hα : ∀ K, W.kFlat K → IsIso (α.app K))
    (hμQ : ∀ K M, W.kFlat K → W.kFlat M → IsIso (Functor.LaxMonoidal.μ Q K M))
    (hμR : ∀ K M, W.kFlat K → W.kFlat M →
      IsIso (Functor.LaxMonoidal.μ R (Ph.obj K) (Ph.obj M)))
    (B : Type*) (q : B → C) (good : B → Prop)
    (τ : (Functor.postcompose₂.obj Ph).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj Ph).obj Ph).obj (curriedTensor D))
    [IsIso τ] :
    ∃ δ : ∀ A B, L.obj (A ⊗ B) ≅ L.obj A ⊗ L.obj B,
      (∀ A A' B B' (f : A ⟶ A') (g : B ⟶ B'),
        L.map (f ⊗ₘ g) ≫ (δ A' B').hom =
          (δ A B).hom ≫ (L.map f ⊗ₘ L.map g)) ∧
      ∀ K M : B, good K → good M →
        L.map (Functor.LaxMonoidal.μ Q (q K) (q M)) ≫ α.app (q K ⊗ q M) ≫
          R.map ((τ.app (q K)).app (q M)) =
        (δ (Q.obj (q K)) (Q.obj (q M))).hom ≫
          (α.app (q K) ⊗ₘ α.app (q M)) ≫
          Functor.LaxMonoidal.μ R (Ph.obj (q K)) (Ph.obj (q M)) := by
  classical
  let F := Ph ⋙ R
  let U : DC ⥤ DC ⥤ DD :=
    (Functor.postcompose₂.obj L).obj (curriedTensor _)
  let V : DC ⥤ DC ⥤ DD :=
    (((Functor.whiskeringLeft₂ _).obj L).obj L).obj (curriedTensor _)
  let βU : (((Functor.whiskeringLeft₂ _).obj Q).obj
      Q).obj U ⟶
      (Functor.postcompose₂.obj F).obj (curriedTensor _) :=
    (Functor.postcompose₂.obj L).map (Functor.LaxMonoidal.μNatTrans Q) ≫
      (Functor.postcompose₂.map α).app (curriedTensor _)
  let βV : (((Functor.whiskeringLeft₂ _).obj Q).obj
      Q).obj V ⟶
      (((Functor.whiskeringLeft₂ _).obj Ph).obj Ph).obj
        ((Functor.postcompose₂.obj R).obj (curriedTensor _)) :=
    (((Functor.whiskeringLeft₂ _).map α).app
        (Q ⋙ L)).app (curriedTensor _) ≫
      (((Functor.whiskeringLeft₂ _).obj (Ph ⋙ R)).map
        α).app (curriedTensor _) ≫
      (((Functor.whiskeringLeft₂ _).obj Ph).obj Ph).map
        (Functor.LaxMonoidal.μNatTrans R)
  have hU : U.IsLeftDerivedFunctor₂ βU W W := by
    apply LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
      W.localizerMorphismKFlat W.localizerMorphismKFlat
    intro K M
    have hμ := hμQ K.obj M.obj K.property M.property
    have ha : IsIso (α.app (K.obj ⊗ M.obj)) :=
      hα (K.obj ⊗ M.obj) (W.kFlat.prop_tensor K.property M.property)
    change IsIso (L.map (Functor.LaxMonoidal.μ Q K.obj M.obj) ≫
      α.app (K.obj ⊗ M.obj))
    exact IsIso.comp_isIso' (Functor.map_isIso L _) ha
  have hV : V.IsLeftDerivedFunctor₂ βV W W := by
    apply LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
      W.localizerMorphismKFlat W.localizerMorphismKFlat
    intro K M
    have := hα K.obj K.property
    have := hα M.obj M.property
    have hμ := hμR K.obj M.obj K.property M.property
    change IsIso ((α.app K.obj ▷ L.obj (Q.obj M.obj)) ≫
      (R.obj (Ph.obj K.obj) ◁ α.app M.obj) ≫
      Functor.LaxMonoidal.μ R (Ph.obj K.obj) (Ph.obj M.obj))
    exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance hμ)
  let := hU
  let := hV
  let τ' := Functor.postcompose₂MapWhiskeringLeft₂ τ R
  obtain ⟨δ, hδ⟩ := exists_leftDerivedTensorIso W W Q
    Q U V _ _ βU βV (asIso τ')
  refine ⟨fun A B ↦ (δ.app A).app B, ?_, ?_⟩
  · intro A A' B B' f g
    have h₁ := congr_app (δ.hom.naturality f) B
    have h₂ := (δ.hom.app A').naturality g
    change L.map (f ▷ B) ≫ (δ.hom.app A').app B =
      (δ.hom.app A).app B ≫ (L.map f ▷ L.obj B) at h₁
    change L.map (A' ◁ g) ≫ (δ.hom.app A').app B' =
      (δ.hom.app A').app B ≫ (L.obj A' ◁ L.map g) at h₂
    change L.map (f ⊗ₘ g) ≫ (δ.hom.app A').app B' =
      (δ.hom.app A).app B ≫ (L.map f ⊗ₘ L.map g)
    rw [tensorHom_def, L.map_comp, Category.assoc, h₂, reassoc_of% h₁, tensorHom_def]
  · intro K₀ M₀ _ _
    let K := q K₀
    let M := q M₀
    have hβU : (βU.app K).app M =
        L.map (Functor.LaxMonoidal.μ Q K M) ≫ α.app (K ⊗ M) := rfl
    have hβV : (βV.app K).app M = (α.app K ⊗ₘ α.app M) ≫
        Functor.LaxMonoidal.μ R (Ph.obj K) (Ph.obj M) := by
      rw [tensorHom_def, Category.assoc]
      rfl
    have hτ : (τ'.app K).app M = R.map ((τ.app K).app M) := rfl
    have heq := hδ K M
    change _ ≫ (βV.app K).app M = (βU.app K).app M ≫ (τ'.app K).app M at heq
    rw [hβV, hβU, hτ, Category.assoc] at heq
    exact heq.symm

private theorem tensorComparison_of_additive_monoidal
    {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B]
    [MonoidalCategory A] [MonoidalCategory B]
    [SymmetricCategory A] [SymmetricCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [MonoidalClosed A] [MonoidalClosed B]
    [IsGrothendieckAbelian A] [IsGrothendieckAbelian B]
    [HasColimitsOfSize.{0, 0} A] [HasColimitsOfSize.{0, 0} B]
    [Abelian.HasFunctorialFlatResolution A] [Abelian.HasFunctorialFlatResolution B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (P : A ⥤ B) [P.Additive] [P.Monoidal] [P.IsLeftAdjoint]
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ L ⟶ P.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hα : ∀ K, (HomotopyCategory.quasiIso A (.up ℤ)).kFlat K → IsIso (α.app K))
    (hPh : ∀ K, (HomotopyCategory.quasiIso A (.up ℤ)).kFlat K →
      (HomotopyCategory.quasiIso B (.up ℤ)).kFlat
        ((P.mapHomotopyCategory (.up ℤ)).obj K)) :
    ∃ δ : ∀ K M, L.obj (K ⊗ M) ≅ L.obj K ⊗ L.obj M,
      (∀ K K' M M' (f : K ⟶ K') (g : M ⟶ M'),
        L.map (f ⊗ₘ g) ≫ (δ K' M').hom =
          (δ K M).hom ≫ (L.map f ⊗ₘ L.map g)) ∧
      ∀ K M : HomotopyCategory A (.up ℤ),
        L.map (Functor.LaxMonoidal.μ DerivedCategory.Qh K M) ≫ α.app (K ⊗ M) ≫
          DerivedCategory.Qh.map
            (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) P).app K).app M) =
          (δ (DerivedCategory.Qh.obj K) (DerivedCategory.Qh.obj M)).hom ≫
            (α.app K ⊗ₘ α.app M) ≫
              Functor.LaxMonoidal.μ DerivedCategory.Qh
                ((P.mapHomotopyCategory (.up ℤ)).obj K)
                ((P.mapHomotopyCategory (.up ℤ)).obj M) := by
  classical
  have (Z : A) : PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj Z) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft Z)
      (NatIso.ofComponents (fun Y ↦ β_ Z Y) (by intros; simp [curriedTensor]))
  have (Z : B) : PreservesColimitsOfShape ℤ ((curriedTensor B).flip.obj Z) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft Z)
      (NatIso.ofComponents (fun Y ↦ β_ Z Y) (by intros; simp [curriedTensor]))
  simpa using (tensorComparison_of_kflat
    (HomotopyCategory.quasiIso A (.up ℤ)) DerivedCategory.Qh DerivedCategory.Qh
    (P.mapHomotopyCategory (.up ℤ)) L α hα
    (fun K M hK _ ↦ DerivedMonoidal.isIso_counit_app_app_of_kFlat_left
      DerivedCategory.Qh _ K M hK)
    (fun K M hK _ ↦ DerivedMonoidal.isIso_counit_app_app_of_kFlat_left
      DerivedCategory.Qh _ _ _ (hPh K hK))
    (HomotopyCategory A (.up ℤ)) id (fun _ ↦ True)
    (Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) P))

/-- Descend the tensor comparison once the derived pair is fixed.
Source: Stacks Project, Tag 079U; uniqueness of left derived bifunctors.
(blueprint: lem-sc-global-tensor-pullback-tensor-descent)

Proof: form the bifunctors U(A,B)=L(A tensor B) and V(A,B)=LA tensor LB.
Their comparison counits are respectively L(mu) followed by alpha on the tensor,
and alpha on both factors followed by mu. On two K-flat objects all these arrows
are isomorphisms: their tensor is K-flat, alpha is invertible there, and P preserves
K-flatness. The K-flat derivability structure therefore makes both bifunctors left
derived bifunctors. Totalize P's inverse tensor constraint and localize it to obtain
an isomorphism between their underived bifunctors. Uniqueness of left derived
bifunctors yields U isomorphic to V. Naturality in each argument gives simultaneous
tensor naturality. The defining counit equation gives exactly the normalization
on quotient cochain objects. This works for zero objects and unbounded complexes.
The private generic tensorComparison_of_kflat above proves the abstract descent.
The additive monoidal specialization registers the K-flat derivability prerequisites;
applying it to modules and sheaves gives the asserted quotient normalization. -/
theorem globalTensorPullback_tensorDescent
    (P : ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [P.Additive] [P.Monoidal] [P.IsLeftAdjoint]
    (L : DerivedCategory
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (α : DerivedCategory.Qh ⋙ L ⟶
      P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hα : ∀ K, (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).kFlat K →
      IsIso (α.app K))
    (hPh : ∀ K, (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).kFlat K →
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).kFlat
        ((P.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) :
    ∃ δ : ∀ A B, L.obj (A ⊗ B) ≅ L.obj A ⊗ L.obj B,
          (∀ A A' B B' (f : A ⟶ A') (g : B ⟶ B'),
            L.map (f ⊗ₘ g) ≫ (δ A' B').hom =
              (δ A B).hom ≫ (L.map f ⊗ₘ L.map g)) ∧
          ∀ K M : CochainComplex
              (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) ℤ,
            (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)).kFlat K →
            (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)).kFlat M →
              (let K' := (HomotopyCategory.quotient _ _).obj K
               let M' := (HomotopyCategory.quotient _ _).obj M
               L.map (Functor.LaxMonoidal.μ DerivedCategory.Qh K' M') ≫
                   α.app (K' ⊗ M') ≫ DerivedCategory.Qh.map
                     (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans
                       (ComplexShape.up ℤ) P).app K').app M') =
                 (δ (DerivedCategory.Qh.obj K') (DerivedCategory.Qh.obj M')).hom ≫
                   (α.app K' ⊗ₘ α.app M') ≫
                     Functor.LaxMonoidal.μ DerivedCategory.Qh
                       ((P.mapHomotopyCategory (ComplexShape.up ℤ)).obj K')
                       ((P.mapHomotopyCategory (ComplexShape.up ℤ)).obj M')) := by
  classical
  have : IsGrothendieckAbelian.{u}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  obtain ⟨δ, hδ, hnorm⟩ := tensorComparison_of_additive_monoidal P L α hα hPh
  refine ⟨δ, hδ, ?_⟩
  intro K M _ _
  exact hnorm ((HomotopyCategory.quotient _ _).obj K)
    ((HomotopyCategory.quotient _ _).obj M)

end
end AlgebraicGeometry.Scheme.Modules
