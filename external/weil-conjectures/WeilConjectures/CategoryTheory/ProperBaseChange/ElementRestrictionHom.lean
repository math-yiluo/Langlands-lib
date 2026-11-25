/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedPresentationData

import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.CategoryTheory.ProperBaseChange.ElementSiteDescent
import WeilConjectures.CategoryTheory.ProperBaseChange.ContinuousCocontinuousRingedRestriction
import WeilConjectures.CategoryTheory.Ringed.RingedEquivalenceModuleHom
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-! # Auxiliary ringed presentation comparisons -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
private theorem restriction_map_bijective
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (F : C ⥤ D) [F.IsEquivalence] (R : Dᵒᵖ ⥤ RingCat.{u})
    (M N : PresheafOfModules.{u} R) :
    Function.Bijective (fun f : M ⟶ N ↦ (PresheafOfModules.pushforward₀ F R).map f) := by
  let W := (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ AddCommGrpCat.{u}).obj F.op
  have hi : Function.Injective (fun f : M ⟶ N ↦
      (PresheafOfModules.pushforward₀ F R).map f) := by
    intro f g h
    apply (PresheafOfModules.toPresheaf R).map_injective
    apply W.map_injective
    exact congrArg ((PresheafOfModules.toPresheaf (F.op ⋙ R)).map) h
  refine ⟨hi, ?_⟩
  intro α
  let β : M.presheaf ⟶ N.presheaf :=
    W.preimage ((PresheafOfModules.toPresheaf (F.op ⋙ R)).map α)
  have hb (X : Cᵒᵖ) (x : M.obj (F.op.obj X)) :
      β.app (F.op.obj X) x = α.app X x :=
    ConcreteCategory.congr_hom (NatTrans.congr_app
      (W.map_preimage (X := M.presheaf) (Y := N.presheaf)
        ((PresheafOfModules.toPresheaf (F.op ⋙ R)).map α)) X) x
  have hs (Y : Dᵒᵖ) (r : R.obj Y) (x : M.obj Y) :
      β.app Y (r • x) = r • β.app Y x := by
    let e := F.op.objObjPreimageIso Y
    apply (ConcreteCategory.bijective_of_isIso (N.presheaf.map e.inv)).1
    change N.map e.inv (β.app Y (r • x)) = N.map e.inv (r • β.app Y x)
    have hn (z : M.obj Y) :
        N.map e.inv (β.app Y z) = β.app _ (M.map e.inv z) :=
      (β.naturality_apply e.inv z).symm
    rw [hn, M.map_smul, hb, map_smul, N.map_smul, hn, hb]
  refine ⟨PresheafOfModules.homMk β hs, ?_⟩
  ext X x
  exact hb X x

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def restrictionHomMap
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (F : C ⥤ D) (R : Dᵒᵖ ⥤ CommRingCat.{u})
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    (PresheafOfModules.pushforward₀ F (R ⋙ forget₂ _ _)).obj
        (PresheafOfModules.homObj M N) ⟶
      PresheafOfModules.homObj (R := F.op ⋙ R)
        ((PresheafOfModules.pushforward₀ F (R ⋙ forget₂ _ _)).obj M)
        ((PresheafOfModules.pushforward₀ F (R ⋙ forget₂ _ _)).obj N) where
  app X := ModuleCat.ofHom
    (X := (PresheafOfModules.homObj (R := R) M N).obj (F.op.obj X))
    (Y := (PresheafOfModules.homObj (R := F.op ⋙ R)
      ((PresheafOfModules.pushforward₀ F (R ⋙ forget₂ _ _)).obj M)
      ((PresheafOfModules.pushforward₀ F (R ⋙ forget₂ _ _)).obj N)).obj X)
    { toFun := fun φ ↦ (PresheafOfModules.pushforward₀
        (Over.post (X := X.unop) F) _).map φ
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  naturality f := by
    ext φ : 2
    apply PresheafOfModules.hom_ext
    intro W
    ext x
    change φ.app (op (Over.mk (F.map W.unop.hom ≫ F.map f.unop))) x =
      φ.app (op (Over.mk (F.map (W.unop.hom ≫ f.unop)))) x
    exact PresheafOfModules.restrictOver_hom_app_congr φ (F.map_comp _ _).symm x

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[irreducible] private def restrictionHomIso
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (F : C ⥤ D) (hF : ∀ X : C, (Over.post (X := X) F).IsEquivalence)
    (R : Dᵒᵖ ⥤ CommRingCat.{u})
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    (PresheafOfModules.pushforward₀ F (R ⋙ forget₂ _ _)).obj
        (PresheafOfModules.homObj M N) ≅
      PresheafOfModules.homObj (R := F.op ⋙ R)
        ((PresheafOfModules.pushforward₀ F (R ⋙ forget₂ _ _)).obj M)
        ((PresheafOfModules.pushforward₀ F (R ⋙ forget₂ _ _)).obj N) := by
  let α := restrictionHomMap F R M N
  have ha (X : Cᵒᵖ) : IsIso (α.app X) := by
    let := hF X.unop
    rw [ConcreteCategory.isIso_iff_bijective]
    exact restriction_map_bijective (Over.post (X := X.unop) F) _ _ _
  exact PresheafOfModules.isoMk (fun X ↦ asIso (α.app X)) (fun _ _ f ↦ α.naturality f)

private theorem restrictionHomIso_hom
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (F : C ⥤ D) (hF : ∀ X : C, (Over.post (X := X) F).IsEquivalence)
    (R : Dᵒᵖ ⥤ CommRingCat.{u})
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    (restrictionHomIso F hF R M N).hom = restrictionHomMap F R M N := by
  unfold restrictionHomIso
  rfl

section Restriction
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {J : GrothendieckTopology D}
  (F : C ⥤ D) [Functor.IsContinuous F K J] (R : Sheaf J CommRingCat.{u})

private abbrev restrictedCommRing :=
  (F.sheafPushforwardContinuous CommRingCat K J).obj R

private abbrev restrictModules :
    PresentationModules R ⥤ PresentationModules (restrictedCommRing (K := K) F R) :=
  SheafOfModules.pushforward.{u} (F := F)
    (𝟙 ((F.sheafPushforwardContinuous RingCat K J).obj (localCoefficientRings R)))

private instance restrictModules_additive : (restrictModules (K := K) F R).Additive := by
  constructor
  intro M N f g
  ext X x
  rfl

private theorem restrictionHomObj_eq (M N : PresentationModules R) :
    PresheafOfModules.homObj (R := F.op ⋙ R.obj)
        ((PresheafOfModules.pushforward₀ F (R.obj ⋙ forget₂ _ _)).obj M.val)
        ((PresheafOfModules.pushforward₀ F (R.obj ⋙ forget₂ _ _)).obj N.val) =
      PresheafOfModules.homObj (R := F.op ⋙ R.obj)
        ((restrictModules (K := K) F R).obj M).val
        ((restrictModules (K := K) F R).obj N).val := by
  congr 1

private def sheafHomIso (hF : ∀ X : C, (Over.post (X := X) F).IsEquivalence)
    (M N : PresentationModules R) :
    (restrictModules (K := K) F R).obj (SheafOfModules.homObj (R := R) M N) ≅
      SheafOfModules.homObj (R := restrictedCommRing (K := K) F R)
        ((restrictModules (K := K) F R).obj M)
        ((restrictModules (K := K) F R).obj N) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    (Iso.refl _ : ((restrictModules (K := K) F R).obj
        (SheafOfModules.homObj (R := R) M N)).val ≅
      (PresheafOfModules.pushforward₀ F (R.obj ⋙ forget₂ _ _)).obj
        (PresheafOfModules.homObj M.val N.val)) ≪≫
    restrictionHomIso F hF R.obj M.val N.val ≪≫
    eqToIso (restrictionHomObj_eq F R M N)

private theorem factor_naturality
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A A' B B' : C} {X X' Y Y' : D}
    (f : A ⟶ A') (g : X ⟶ X') (p : A ⟶ B) (p' : A' ⟶ B')
    (q : X ⟶ Y) (q' : X' ⟶ Y') (a : F.obj A ⟶ X) (a' : F.obj A' ⟶ X')
    (b : F.obj B ⟶ Y) (b' : F.obj B' ⟶ Y') (h : B ⟶ B') (k : Y ⟶ Y')
    (hf : f ≫ p' = p ≫ h) (hg : g ≫ q' = q ≫ k)
    (ha : a ≫ q = F.map p ≫ b) (ha' : a' ≫ q' = F.map p' ≫ b')
    (hb : F.map h ≫ b' = b ≫ k) :
    (F.map f ≫ a') ≫ q' = (a ≫ g) ≫ q' := by
  rw [Category.assoc, ha', ← Category.assoc, ← F.map_comp, hf,
    F.map_comp, Category.assoc, hb, ← Category.assoc, ← ha,
    Category.assoc, ← hg, ← Category.assoc]

private theorem factor_differential
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive]
    {Hn Hm A B E : C} {Kn Km A' B' E' : D}
    (dH : Hn ⟶ Hm) (dK : Kn ⟶ Km)
    (a : Hn ⟶ A) (b : Hn ⟶ B) (c : Hm ⟶ E)
    (α : A ⟶ E) (β : B ⟶ E)
    (a' : Kn ⟶ A') (b' : Kn ⟶ B') (c' : Km ⟶ E')
    (α' : A' ⟶ E') (β' : B' ⟶ E')
    (en : F.obj Hn ⟶ Kn) (em : F.obj Hm ⟶ Km)
    (sa : F.obj A ⟶ A') (sb : F.obj B ⟶ B') (sc : F.obj E ⟶ E') (t : ℤ)
    (hH : dH ≫ c = a ≫ α - t • (b ≫ β))
    (hK : dK ≫ c' = a' ≫ α' - t • (b' ≫ β'))
    (ha : en ≫ a' = F.map a ≫ sa) (hb : en ≫ b' = F.map b ≫ sb)
    (hc : em ≫ c' = F.map c ≫ sc)
    (hα : F.map α ≫ sc = sa ≫ α') (hβ : F.map β ≫ sc = sb ≫ β') :
    (en ≫ dK) ≫ c' = (F.map dH ≫ em) ≫ c' := by
  simp only [Category.assoc, hK, Preadditive.comp_sub,
    Preadditive.comp_zsmul]
  rw [← Category.assoc en a', ha, Category.assoc,
    ← Category.assoc en b', hb, Category.assoc]
  rw [hc, ← Category.assoc (F.map dH), ← F.map_comp, hH]
  simp only [Functor.map_sub, Functor.map_zsmul, Functor.map_comp,
    Preadditive.sub_comp, Preadditive.zsmul_comp, Category.assoc, hα, hβ]

-- Categorical comparisons elaborate several nested restriction and localization functors.
set_option backward.isDefEq.respectTransparency false in
private theorem sheafHomIso_naturality
    (hF : ∀ X : C, (Over.post (X := X) F).IsEquivalence)
    {M M' N N' : PresentationModules R} (f : M' ⟶ M) (g : N ⟶ N') :
    (restrictModules (K := K) F R).map (SheafOfModules.homObjMap (R := R) f g) ≫
        (sheafHomIso F R hF M' N').hom =
      (sheafHomIso F R hF M N).hom ≫
        SheafOfModules.homObjMap (R := restrictedCommRing (K := K) F R)
          ((restrictModules (K := K) F R).map f)
          ((restrictModules (K := K) F R).map g) := by
  apply SheafOfModules.hom_ext
  simp only [SheafOfModules.comp_val, sheafHomIso,
    Functor.FullyFaithful.preimageIso_hom, SheafOfModules.fullyFaithfulForget,
    Iso.trans_hom, Iso.refl_hom, restrictionHomIso_hom]
  have he (P Q : PresentationModules R) :
      (eqToIso (restrictionHomObj_eq (K := K) F R P Q)).hom =
        𝟙 (PresheafOfModules.homObj (R := F.op ⋙ R.obj)
          ((restrictModules (K := K) F R).obj P).val
          ((restrictModules (K := K) F R).obj Q).val) :=
    eqToHom_refl
      (PresheafOfModules.homObj (R := F.op ⋙ R.obj)
        ((restrictModules (K := K) F R).obj P).val
        ((restrictModules (K := K) F R).obj Q).val)
      (restrictionHomObj_eq F R P Q)
  rw [he, he]
  ext X φ : 3
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  rfl

private theorem restrictModules_products :
    PreservesLimitsOfShape (Discrete ℤ) (restrictModules (K := K) F R) := by
  let T := SheafOfModules.forget (localCoefficientRings (restrictedCommRing (K := K) F R)) ⋙
    PresheafOfModules.toPresheaf _
  have : PreservesLimitsOfShape (Discrete ℤ) (restrictModules (K := K) F R ⋙ T) := by
    change PreservesLimitsOfShape (Discrete ℤ)
      ((SheafOfModules.forget (localCoefficientRings R) ⋙
        PresheafOfModules.toPresheaf _) ⋙
        (Functor.whiskeringLeft _ _ _).obj F.op)
    infer_instance
  have : ReflectsLimitsOfShape (Discrete ℤ) T :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves _ T

end Restriction

private theorem fanIso {E : Type*} [Category E] {ι : Type*}
    {A B : E} {f g : ι → E} (π : ∀ i, A ⟶ f i) (τ : ∀ i, B ⟶ g i)
    (hπ : IsLimit (Fan.mk A π)) (hτ : IsLimit (Fan.mk B τ)) (e : ∀ i, f i ≅ g i) :
    ∃ a : A ≅ B, ∀ i, a.hom ≫ τ i = π i ≫ (e i).hom := by
  let a := Fan.IsLimit.lift hτ (fun i ↦ π i ≫ (e i).hom)
  let b := Fan.IsLimit.lift hπ (fun i ↦ τ i ≫ (e i).inv)
  have ha (i) : a ≫ τ i = π i ≫ (e i).hom := Fan.IsLimit.fac hτ _ i
  have hb (i) : b ≫ π i = τ i ≫ (e i).inv := Fan.IsLimit.fac hπ _ i
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · apply Fan.IsLimit.hom_ext hπ
    intro i
    change (a ≫ b) ≫ π i = (𝟙 A) ≫ π i
    rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · apply Fan.IsLimit.hom_ext hτ
    intro i
    change (b ≫ a) ≫ τ i = (𝟙 B) ≫ τ i
    rw [Category.assoc, ha, ← Category.assoc, hb, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp]

private abbrev complexMap
    {A B : Type*} [Category A] [Category B] [HasZeroMorphisms A] [HasZeroMorphisms B]
    (T : A ⥤ B) [T.PreservesZeroMorphisms] := T.mapHomologicalComplex (.up ℤ)

attribute [local irreducible] homComplexFunctor

-- Categorical comparisons elaborate several nested restriction and localization functors.
-- Projection formulas require reducing the local Hom-complex abbreviations.
set_option backward.isDefEq.respectTransparency true in
private theorem homComplexFromComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (T : PresentationModules R ⥤ PresentationModules S) [T.Additive]
    [PreservesLimitsOfShape (Discrete ℤ) T]
    (γ : ∀ M N : PresentationModules R,
      T.obj (SheafOfModules.homObj (R := R) M N) ≅
        SheafOfModules.homObj (R := S) (T.obj M) (T.obj N))
    (hγ : ∀ {M M' N N' : PresentationModules R} (f : M' ⟶ M) (g : N ⟶ N'),
      T.map (SheafOfModules.homObjMap (R := R) f g) ≫ (γ M' N').hom =
        (γ M N).hom ≫ SheafOfModules.homObjMap (R := S) (T.map f) (T.map g)) :
    Nonempty (Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙
      complexMap T ≅
      ((complexMap T).op.prod (complexMap T)) ⋙
        Functor.uncurry.obj (homComplexFunctor (R := S))) := by
  classical
  obtain ⟨π, hπ, dπ, nπ⟩ := homComplex_projections_exists (R := R)
  obtain ⟨τ, hτ, dτ, nτ⟩ := homComplex_projections_exists (R := S)
  have hi (L M : CochainComplex (PresentationModules R) ℤ) (n : ℤ) :
      ∃ a : T.obj ((homComplex (R := R) L M).X n) ≅
          (homComplex (R := S) ((complexMap T).obj L) ((complexMap T).obj M)).X n,
        ∀ p : ℤ, a.hom ≫ τ ((complexMap T).obj L) ((complexMap T).obj M) n p (p + n) rfl =
          T.map (π L M n p (p + n) rfl) ≫
            (γ (L.X p) (M.X (p + n))).hom :=
    fanIso _ _
      (isLimitFanMkObjOfIsLimit T _ _ (hπ L M n).some)
      (hτ ((complexMap T).obj L) ((complexMap T).obj M) n).some
      (fun p ↦ γ (L.X p) (M.X (p + n)))
  dsimp only [homComplex] at hi
  obtain ⟨a, ha⟩ : ∃ a : ∀ (L M : CochainComplex (PresentationModules R) ℤ) (n : ℤ),
      T.obj ((((homComplexFunctor (R := R)).obj (op L)).obj M).X n) ≅
        (((homComplexFunctor (R := S)).obj (op ((complexMap T).obj L))).obj ((complexMap T).obj
          M)).X n,
      ∀ L M n p, (a L M n).hom ≫ τ ((complexMap T).obj L) ((complexMap T).obj M) n p (p + n) rfl =
        T.map (π L M n p (p + n) rfl) ≫
          (γ (L.X p) (M.X (p + n))).hom := by
    choose a ha using hi
    exact ⟨a, ha⟩
  have ha' (L M : CochainComplex (PresentationModules R) ℤ)
      (n p q : ℤ) (hpq : p + n = q) :
      (a L M n).hom ≫ τ ((complexMap T).obj L) ((complexMap T).obj M) n p q hpq =
        T.map (π L M n p q hpq) ≫ (γ (L.X p) (M.X q)).hom := by
    subst q
    exact ha L M n p
  have comm (L M : CochainComplex (PresentationModules R) ℤ)
      (n m : ℤ) (hnm : n + 1 = m) :
      (a L M n).hom ≫ (homComplex (R := S) ((complexMap T).obj L) ((complexMap T).obj M)).d n m =
        T.map ((homComplex (R := R) L M).d n m) ≫ (a L M m).hom := by
    apply (hτ ((complexMap T).obj L) ((complexMap T).obj M) m).some.hom_ext
    rintro ⟨p⟩
    change ((a L M n).hom ≫ _) ≫ τ ((complexMap T).obj L) ((complexMap T).obj M) m p (p + m) rfl =
      (T.map _ ≫ (a L M m).hom) ≫ τ ((complexMap T).obj L) ((complexMap T).obj M) m p (p + m) rfl
    have hH := dπ L M n m p (p + m) (p + n) (p + 1)
      hnm rfl rfl (by omega)
    have hK := dτ ((complexMap T).obj L) ((complexMap T).obj M) n m p (p + m) (p + n) (p + 1)
      hnm rfl rfl (by omega)
    simp only [Units.smul_def] at hH hK
    dsimp only [homComplex]
    have hh := factor_differential (C := PresentationModules R) (D := PresentationModules S) T
      ((((homComplexFunctor (R := R)).obj (op L)).obj M).d n m)
      ((((homComplexFunctor (R := S)).obj (op ((complexMap T).obj L))).obj ((complexMap T).obj
        M)).d n m)
      (π L M n p (p + n) rfl)
      (π L M n (p + 1) (p + m) (by omega))
      (π L M m p (p + m) rfl)
      (SheafOfModules.homObjMap (R := R) (𝟙 (L.X p)) (M.d (p + n) (p + m)))
      (SheafOfModules.homObjMap (R := R) (L.d p (p + 1)) (𝟙 (M.X (p + m))))
      (τ ((complexMap T).obj L) ((complexMap T).obj M) n p (p + n) rfl)
      (τ ((complexMap T).obj L) ((complexMap T).obj M) n (p + 1) (p + m) (by omega))
      (τ ((complexMap T).obj L) ((complexMap T).obj M) m p (p + m) rfl)
      (SheafOfModules.homObjMap (R := S) (𝟙 (((complexMap T).obj L).X p))
        (((complexMap T).obj M).d (p + n) (p + m)))
      (SheafOfModules.homObjMap (R := S) (((complexMap T).obj L).d p (p + 1))
        (𝟙 (((complexMap T).obj M).X (p + m))))
      (a L M n).hom (a L M m).hom
      (γ (L.X p) (M.X (p + n))).hom
      (γ (L.X (p + 1)) (M.X (p + m))).hom
      (γ (L.X p) (M.X (p + m))).hom (n.negOnePow : ℤ) hH hK
      (ha' L M n p (p + n) rfl)
      (ha' L M n (p + 1) (p + m) (by omega))
      (ha' L M m p (p + m) rfl)
    apply hh
    · dsimp only [complexMap, Functor.mapHomologicalComplex]
      simpa only [Functor.map_id] using
        hγ (𝟙 (L.X p)) (M.d (p + n) (p + m))
    · dsimp only [complexMap, Functor.mapHomologicalComplex]
      simpa only [Functor.map_id] using
        hγ (L.d p (p + 1)) (𝟙 (M.X (p + m)))
  let e (L M : CochainComplex (PresentationModules R) ℤ) :
      (complexMap T).obj (homComplex (R := R) L M) ≅
        homComplex (R := S) ((complexMap T).obj L) ((complexMap T).obj M) :=
    HomologicalComplex.Hom.isoOfComponents (a L M) (comm L M)
  refine ⟨NatIso.ofComponents (fun X ↦ e X.1.unop X.2) ?_⟩
  intro X Y f
  apply HomologicalComplex.hom_ext
  intro n
  apply (hτ ((complexMap T).obj Y.1.unop) ((complexMap T).obj Y.2) n).some.hom_ext
  rintro ⟨p⟩
  change (T.map ((((homComplexFunctor (R := R)).map f.1).app X.2 ≫
      ((homComplexFunctor (R := R)).obj Y.1).map f.2).f n) ≫
      (a Y.1.unop Y.2 n).hom) ≫
      τ ((complexMap T).obj Y.1.unop) ((complexMap T).obj Y.2) n p (p + n) rfl =
    ((a X.1.unop X.2 n).hom ≫
      ((((homComplexFunctor (R := S)).map ((complexMap T).op.map f.1)).app ((complexMap T).obj
        X.2) ≫
        ((homComplexFunctor (R := S)).obj (op ((complexMap T).obj Y.1.unop))).map ((complexMap
          T).map f.2)).f n)) ≫
      τ ((complexMap T).obj Y.1.unop) ((complexMap T).obj Y.2) n p (p + n) rfl
  have hH := nπ X.1.unop Y.1.unop X.2 Y.2 f.1.unop f.2 n p (p + n) rfl
  have hK := nτ ((complexMap T).obj X.1.unop) ((complexMap T).obj Y.1.unop) ((complexMap T).obj
    X.2) ((complexMap T).obj Y.2)
    ((complexMap T).map f.1.unop) ((complexMap T).map f.2) n p (p + n) rfl
  refine factor_naturality (C := PresentationModules R) (D := PresentationModules S) T
    ((((homComplexFunctor (R := R)).map f.1).app X.2 ≫
      ((homComplexFunctor (R := R)).obj Y.1).map f.2).f n)
    ((((homComplexFunctor (R := S)).map ((complexMap T).op.map f.1)).app ((complexMap T).obj X.2) ≫
      ((homComplexFunctor (R := S)).obj (op ((complexMap T).obj Y.1.unop))).map ((complexMap
        T).map f.2)).f n)
    (π X.1.unop X.2 n p (p + n) rfl) (π Y.1.unop Y.2 n p (p + n) rfl)
    (τ ((complexMap T).obj X.1.unop) ((complexMap T).obj X.2) n p (p + n) rfl)
    (τ ((complexMap T).obj Y.1.unop) ((complexMap T).obj Y.2) n p (p + n) rfl)
    (a X.1.unop X.2 n).hom (a Y.1.unop Y.2 n).hom
    (γ (X.1.unop.X p) (X.2.X (p + n))).hom
    (γ (Y.1.unop.X p) (Y.2.X (p + n))).hom
    (SheafOfModules.homObjMap (R := R) (f.1.unop.f p) (f.2.f (p + n)))
    (SheafOfModules.homObjMap (R := S)
      (((complexMap T).map f.1.unop).f p) (((complexMap T).map f.2).f (p + n)))
    ?_ ?_ ?_ ?_ ?_
  · exact hH
  · exact hK
  · exact ha X.1.unop X.2 n p
  · exact ha Y.1.unop Y.2 n p
  · dsimp only [complexMap, Functor.mapHomologicalComplex]
    exact hγ (f.1.unop.f p) (f.2.f (p + n))

private theorem homComplexRestriction
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {J : GrothendieckTopology D}
    (F : C ⥤ D) [Functor.IsContinuous F K J] (R : Sheaf J CommRingCat.{u})
    (hF : ∀ X : C, (Over.post (X := X) F).IsEquivalence) :
    let T := restrictModules (K := K) F R
    let S := restrictedCommRing (K := K) F R
    let Tc := T.mapHomologicalComplex (.up ℤ)
    Nonempty (Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙ Tc ≅
      (Tc.op.prod Tc) ⋙ Functor.uncurry.obj (homComplexFunctor (R := S))) := by
  let := restrictModules_products (K := K) F R
  exact homComplexFromComparison R _ _ (sheafHomIso F R hF)
    (fun f g ↦ sheafHomIso_naturality F R hF f g)

-- Categorical comparisons elaborate several nested restriction and localization functors.
set_option backward.isDefEq.respectTransparency true in
private theorem derivedHomRestriction
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {J : GrothendieckTopology D}
    (F : C ⥤ D) [Functor.IsContinuous F K J] (R : Sheaf J CommRingCat.{u})
    (hF : ∀ X : C, (Over.post (X := X) F).IsEquivalence)
    (hl : PreservesFiniteLimits (restrictModules (K := K) F R))
    (hc : PreservesFiniteColimits (restrictModules (K := K) F R))
    (hk : ∀ I : CochainComplex (PresentationModules R) ℤ,
      I.IsKInjective →
        CochainComplex.IsKInjective
        (((restrictModules (K := K) F R).mapHomologicalComplex (.up ℤ)).obj I)) :
    let T := restrictModules (K := K) F R
    let S := restrictedCommRing (K := K) F R
    let Df := presentationDerivedMap (R := R) (S := S) T (restrictModules_additive F R) hl hc
    Nonempty (presentationRHom R ⋙ Df ≅ (Df.op.prod Df) ⋙ presentationRHom S) := by
  classical
  intro T S Df
  let := hl
  let := hc
  let := HasDerivedCategory.standard (PresentationModules R)
  let := HasDerivedCategory.standard (PresentationModules S)
  let : IsGrothendieckAbelian.{u} (PresentationModules R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, u, u}
      J R).1
  let : IsGrothendieckAbelian.{u} (PresentationModules S) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, u, u}
      K S).1
  let Tc := T.mapHomologicalComplex (.up ℤ)
  let QR := DerivedCategory.Q (C := PresentationModules R)
  let QS := DerivedCategory.Q (C := PresentationModules S)
  let IR := CochainComplex.kInjectiveResolutionFunctor.{u} (PresentationModules R)
  let IS := CochainComplex.kInjectiveResolutionFunctor.{u} (PresentationModules S)
  let ηR := CochainComplex.toKInjectiveResolution.{u} (PresentationModules R)
  let ηS := CochainComplex.toKInjectiveResolution.{u} (PresentationModules S)
  let HR := Functor.uncurry.obj (homComplexFunctor (R := R))
  let HS := Functor.uncurry.obj (homComplexFunctor (R := S))
  have qR (M) : QuasiIso (ηR.app M) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ M).2
  have qS (M) : QuasiIso (ηS.app M) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ M).2
  have kR (M) : (IR.obj M).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} _ M
  have kS (M) : (IS.obj M).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} _ M
  obtain ⟨cR⟩ := derivedInternalHomOfUniverses_comparison.{u, u, u, u + 1}
    J R IR ηR (fun M ↦ ⟨qR M, kR M⟩)
  obtain ⟨cS⟩ := derivedInternalHomOfUniverses_comparison.{u, u, u, u + 1}
    K S IS ηS (fun M ↦ ⟨qS M, kS M⟩)
  obtain ⟨ec⟩ := homComplexRestriction (K := K) F R hF
  have left : (QR.op.prod QR) ⋙ (presentationRHom R ⋙ Df) ≅
      (Tc.op.prod (IR ⋙ Tc)) ⋙ HS ⋙ QS :=
    Functor.isoWhiskerRight cR Df ≪≫
      Functor.isoWhiskerLeft ((𝟭 _).prod IR ⋙ HR) T.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft ((𝟭 _).prod IR) ec) QS
  have right : (QR.op.prod QR) ⋙ ((Df.op.prod Df) ⋙ presentationRHom S) ≅
      (Tc.op.prod (Tc ⋙ IS)) ⋙ HS ⋙ QS := by
    let eQ : (QR.op.prod QR) ⋙ (Df.op.prod Df) ≅
        (Tc.op.prod Tc) ⋙ (QS.op.prod QS) :=
      NatIso.ofComponents (fun X ↦
        ((T.mapDerivedCategoryFactors.app X.1.unop).symm.op).prod
          (T.mapDerivedCategoryFactors.app X.2)) (by
        intro X Y f
        apply Prod.ext
        · exact congrArg Quiver.Hom.op
            (T.mapDerivedCategoryFactors.inv.naturality f.1.unop).symm
        · exact T.mapDerivedCategoryFactors.hom.naturality f.2)
    exact Functor.isoWhiskerRight eQ (presentationRHom S) ≪≫
      Functor.isoWhiskerLeft (Tc.op.prod Tc) cS
  have hinv (P Q : CochainComplex (PresentationModules R) ℤ ⥤
      CochainComplex (PresentationModules S) ℤ) (γ : P ⟶ Q)
      (hγ : ∀ M, QuasiIso (γ.app M))
      (hP : ∀ M, (P.obj M).IsKInjective) (hQ : ∀ M, (Q.obj M).IsKInjective) :
      IsIso (Functor.whiskerRight (NatTrans.prod (𝟙 Tc.op) γ) (HS ⋙ QS)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    have := hγ X.2
    have := hP X.2
    have := hQ X.2
    change IsIso (QS.map
      (((homComplexFunctor (R := S)).map (𝟙 (op (Tc.obj X.1.unop)))).app (P.obj X.2) ≫
        ((homComplexFunctor (R := S)).obj (op (Tc.obj X.1.unop))).map (γ.app X.2)))
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
    exact quasiIso_homComplex_mapOfUniverses.{u, u, u}
      (γ.app X.2) (𝟙 (Tc.obj X.1.unop))
  let α := Functor.whiskerRight
    (NatTrans.prod (𝟙 Tc.op) (Functor.whiskerLeft (IR ⋙ Tc) ηS)) (HS ⋙ QS)
  let β := Functor.whiskerRight
    (NatTrans.prod (𝟙 Tc.op) (Functor.whiskerRight (Functor.whiskerRight ηR Tc) IS))
      (HS ⋙ QS)
  have : IsIso α := hinv _ _ _ (fun M ↦ qS (Tc.obj (IR.obj M)))
    (fun M ↦ hk _ (kR M)) (fun M ↦ kS _)
  have : IsIso β := hinv _ _ _ (fun M ↦ by
      have : QuasiIso (ηR.app M) := qR M
      have h : QuasiIso (Tc.map (ηR.app M)) := inferInstance
      have : QuasiIso (ηS.app (Tc.obj M)) := qS _
      have : QuasiIso (ηS.app (Tc.obj (IR.obj M))) := qS _
      change QuasiIso (IS.map (Tc.map (ηR.app M)))
      apply (quasiIso_iff_comp_left (ηS.app (Tc.obj M)) _).mp
      have hn : Tc.map (ηR.app M) ≫ ηS.app (Tc.obj (IR.obj M)) =
          ηS.app (Tc.obj M) ≫ IS.map (Tc.map (ηR.app M)) :=
        ηS.naturality (Tc.map (ηR.app M))
      have hcomp : QuasiIso (Tc.map (ηR.app M) ≫ ηS.app (Tc.obj (IR.obj M))) :=
        inferInstance
      exact hn ▸ hcomp)
    (fun M ↦ kS _) (fun M ↦ kS _)
  let W := (HomologicalComplex.quasiIso (PresentationModules R) (.up ℤ)).op.prod
    (HomologicalComplex.quasiIso (PresentationModules R) (.up ℤ))
  exact ⟨(Localization.fullyFaithfulWhiskeringLeft (QR.op.prod QR) W _).preimageIso
    (left ≪≫ asIso α ≪≫ (asIso β).symm ≪≫ right.symm)⟩

private instance projectionFaithful
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (A : Sheaf J (Type u)) : (elementProjection A).Faithful where
  map_injective {X Y} f g h := by
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    exact congrArg Quiver.Hom.op h

private abbrev fibreSheaf
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {A B : Sheaf J (Type u)} (b : B ⟶ A) : Sheaf (elementTopology A) (Type u) where
  obj := (elementFibrePresheafFunctor A).obj (Over.mk b)
  property := by
    obtain ⟨e, ⟨q⟩⟩ := (element_site_descent A).2.2.1
    exact (Presheaf.isSheaf_of_iso_iff (q.app (Over.mk b))).mp
      (e.inverse.obj (Over.mk b)).property

private def flattenElements
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {A B : Sheaf J (Type u)} (b : B ⟶ A) :
    (fibreSheaf b).obj.Elementsᵒᵖ ⥤ B.obj.Elementsᵒᵖ where
  obj X := op (B.obj.elementsMk X.unop.1.unop.unop.1 X.unop.2.val)
  map {X Y} f := (Functor.Elements.homMk
    (x := B.obj.elementsMk Y.unop.1.unop.unop.1 Y.unop.2.val)
    (y := B.obj.elementsMk X.unop.1.unop.unop.1 X.unop.2.val)
    f.unop.hom.unop.unop.hom (congrArg Subtype.val f.unop.map_val)).op

private instance flattenElementsFaithful
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {A B : Sheaf J (Type u)} (b : B ⟶ A) : (flattenElements b).Faithful where
  map_injective {X Y} f g h := by
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    apply Quiver.Hom.unop_inj
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    exact congrArg (fun k ↦ k.unop.hom) h

set_option backward.isDefEq.respectTransparency false in
private instance flattenElementsFull
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {A B : Sheaf J (Type u)} (b : B ⟶ A) : (flattenElements b).Full where
  map_surjective {X Y} f := by
    have hA : A.obj.map f.unop.hom Y.unop.1.unop.unop.2 =
        X.unop.1.unop.unop.2 := by
      rw [← Y.unop.2.property]
      change A.obj.map f.unop.hom (b.hom.app _ Y.unop.2.val) = _
      rw [← NatTrans.naturality_apply]
      change b.hom.app _ (B.obj.map f.unop.hom Y.unop.2.val) = _
      have hf : B.obj.map f.unop.hom Y.unop.2.val = X.unop.2.val := f.unop.map_val
      rw [hf]
      exact X.unop.2.property
    let g : X.unop.1.unop ⟶ Y.unop.1.unop :=
      (Functor.Elements.homMk (F := A.obj) f.unop.hom hA).op
    refine ⟨(Functor.Elements.homMk (x := Y.unop) (y := X.unop) g.op ?_).op, ?_⟩
    · apply Subtype.ext
      exact f.unop.map_val
    · rfl

private instance flattenElementsEssSurj
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {A B : Sheaf J (Type u)} (b : B ⟶ A) : (flattenElements b).EssSurj where
  mem_essImage Y := by
    let X := op (op (A.obj.elementsMk Y.unop.1 (b.hom.app _ Y.unop.2)))
    exact ⟨op ((fibreSheaf b).obj.elementsMk X ⟨Y.unop.2, rfl⟩), ⟨Iso.refl _⟩⟩

private instance flattenElementsEquivalence
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {A B : Sheaf J (Type u)} (b : B ⟶ A) : (flattenElements b).IsEquivalence := {}

private theorem element_cover_iff
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (A : Sheaf J (Type u)) {X : A.obj.Elementsᵒᵖ} (S : Sieve X) :
    S ∈ elementTopology A X ↔
      S.functorPushforward (elementProjection A) ∈ J ((elementProjection A).obj X) := by
  constructor
  · exact (CoverPreserving.of_isContinuous (elementProjection A) _ _).cover_preserve
  · intro h
    rw [(element_site_descent A).1]
    exact (elementProjection A).mem_restrictedTopology_of_functorPushforward_mem h

private instance flattenElementsDense
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {A B : Sheaf J (Type u)} (b : B ⟶ A) :
    (flattenElements b).IsDenseSubsite (elementTopology (fibreSheaf b))
      (elementTopology B) where
  functorPushforward_mem_iff {X S} := by
    rw [element_cover_iff, element_cover_iff, element_cover_iff]
    rw [← Sieve.functorPushforward_comp, ← Sieve.functorPushforward_comp]
    rfl

private theorem bijective_of_pointwise_heq {α β : Type u} (h : α = β)
    (f : α → β) (hf : ∀ x, HEq (f x) x) : Function.Bijective f := by
  subst β
  have he : f = id := funext (fun x ↦ eq_of_heq (hf x))
  rw [he]
  exact Function.bijective_id

private theorem restrictionEquivalenceCore
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {J : GrothendieckTopology D}
    (F : C ⥤ D) [Functor.IsContinuous F K J] [Functor.IsCocontinuous F K J]
    [(F.sheafPushforwardContinuous (Type u) K J).IsEquivalence]
    (R : Sheaf J CommRingCat.{u}) :
    ∃ T : RingedPresentationEquivalenceCore R (restrictedCommRing (K := K) F R),
      Nonempty (restrictModules (K := K) F R ≅ T.modules.functor) := by
  obtain ⟨e, hi, hr, ⟨adj⟩⟩ := continuous_cocontinuous_ringed_restriction
    K J F (localCoefficientRings R)
  have : e.inverse.IsEquivalence := by rw [hi]; infer_instance
  have : IsIso e.ringMap := by
    have h : IsIso ((sheafToPresheaf K (Type u)).map e.ringMap) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro X
      rw [ConcreteCategory.isIso_iff_bijective]
      apply bijective_of_pointwise_heq _ _ (hr X)
      rw [hi]
      rfl
    exact isIso_of_reflects_iso _ (sheafToPresheaf K (Type u))
  obtain ⟨T, ⟨q⟩, _, _⟩ := ringed_equivalence_module_hom (R := restrictedCommRing F R)
    (S := R) e
  exact ⟨T, ⟨Adjunction.leftAdjointUniq adj (T.modules.toAdjunction.ofNatIsoRight q)⟩⟩

private def pushforwardCompare
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : GrothendieckTopology E} (F : C ⥤ D) (G : D ⥤ E) (P : C ⥤ E)
    [F.IsContinuous J K] [G.IsContinuous K L] [P.IsContinuous J L]
    [(F ⋙ G).IsContinuous J L]
    {R : Sheaf L RingCat.{u}} {S : Sheaf K RingCat.{u}} {T : Sheaf J RingCat.{u}}
    (φ : T ⟶ (F.sheafPushforwardContinuous RingCat J K).obj S)
    (ψ : S ⟶ (G.sheafPushforwardContinuous RingCat K L).obj R)
    (θ : T ⟶ (P.sheafPushforwardContinuous RingCat J L).obj R)
    (e : F ⋙ G ≅ P)
    (he : (φ ≫ (F.sheafPushforwardContinuous RingCat J K).map ψ) ≫
      (Functor.sheafPushforwardContinuousNatTrans e.inv RingCat J L).app R = θ) :
    SheafOfModules.pushforward.{u} ψ ⋙ SheafOfModules.pushforward.{u} φ ≅
      SheafOfModules.pushforward.{u} θ :=
  SheafOfModules.pushforwardComp φ ψ ≪≫
    SheafOfModules.pushforwardCongr₂ _ e.symm he

set_option backward.isDefEq.respectTransparency false in
-- Transport through flattening compares two presentations of the same section fibres.
private theorem flattenRestrictionEquivalence
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) {A B : Sheaf J (Type u)} (b : B ⟶ A) :
    ∃ E : PresentationModules (presentationElementRing R B) ≌
        PresentationModules (presentationElementRing (presentationElementRing R A) (fibreSheaf b)),
      Nonempty (elementModulePullbackOver.{u, u} (localCoefficientRings R) b
        (presentationElementRestriction_continuous b) ⋙ E.functor ≅
          elementModulePullback.{u, u} (localCoefficientRings (presentationElementRing R A))
            (fibreSheaf b)) := by
  let F := elementModulePullbackOver.{u, u} (localCoefficientRings R) b
    (presentationElementRestriction_continuous b)
  let Q := elementModulePullback.{u, u}
    (localCoefficientRings (presentationElementRing R A)) (fibreSheaf b)
  have h : F ⋙ restrictModules (K := elementTopology (fibreSheaf b))
      (flattenElements b) (presentationElementRing R B) ≅ Q := by
    let G := flattenElements b ⋙ elementMap b
    let P := elementProjection (fibreSheaf b)
    let α : G ≅ P := NatIso.ofComponents (fun X ↦
      (Functor.Elements.isoMk (x := (P.obj X).unop) (y := (G.obj X).unop) (Iso.refl _)
        (by
          change A.obj.map (𝟙 _) X.unop.1.unop.unop.2 = b.hom.app _ X.unop.2.val
          rw [A.obj.map_id_apply]
          exact X.unop.2.property.symm)).op) (by
        intro X Y f
        apply Quiver.Hom.unop_inj
        apply Functor.Elements.hom_ext
        change (𝟙 _) ≫ f.unop.hom.unop.unop.hom =
          f.unop.hom.unop.unop.hom ≫ (𝟙 _)
        simp)
    let : P.IsContinuous (elementTopology (fibreSheaf b)) (elementTopology A) :=
      elementProjection_isContinuous (fibreSheaf b)
    let := presentationElementRestriction_continuous b
    let := Functor.isContinuous_comp (flattenElements b) (elementMap b)
      (elementTopology (fibreSheaf b)) (elementTopology B) (elementTopology A)
    let R₀ := localCoefficientRings (presentationElementRing R A)
    let R₁ := localCoefficientRings (presentationElementRing R B)
    let R₂ := localCoefficientRings
      (presentationElementRing (presentationElementRing R A) (fibreSheaf b))
    let c := pushforwardCompare
      (J := elementTopology (fibreSheaf b)) (K := elementTopology B)
      (L := elementTopology A) (flattenElements b) (elementMap b) P
      (R := R₀) (S := R₁) (T := R₂) (𝟙 R₂) (𝟙 R₁) (𝟙 R₂) α (by
        ext X r
        change R.obj.map (𝟙 _) r = r
        exact R.obj.map_id_apply _ _)
    convert c using 1 <;> congr 1
  obtain ⟨T, ⟨q⟩⟩ := restrictionEquivalenceCore
    (K := elementTopology (fibreSheaf b)) (flattenElements b) (presentationElementRing R B)
  exact ⟨T.modules, ⟨Functor.isoWhiskerLeft F q.symm ≪≫ h⟩⟩

private def representableElements
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (U : C) :
    Over U ⥤ ((presheafToSheaf J (Type u)).obj (yoneda.obj U)).obj.Elementsᵒᵖ where
  obj X := op (((presheafToSheaf J (Type u)).obj (yoneda.obj U)).obj.elementsMk
    (op X.left) ((toSheafify J (yoneda.obj U)).app _ X.hom))
  map f := (Functor.Elements.homMk f.left.op (by
    rw [← NatTrans.naturality_apply]
    exact congrArg ((toSheafify J (yoneda.obj U)).app _) (Over.w f))).op

private instance representableElementsFaithful
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (U : C) :
    (representableElements J U).Faithful where
  map_injective {X Y} f g h := by
    ext
    exact congrArg (fun k ↦ k.unop.hom.unop) h

private theorem representableElements_cover_iff
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (U : C)
    {X : Over U} (S : Sieve X) :
    S.functorPushforward (representableElements J U) ∈
        elementTopology ((presheafToSheaf J (Type u)).obj (yoneda.obj U)) _ ↔
      S ∈ J.over U X := by
  rw [element_cover_iff, ← Sieve.functorPushforward_comp, J.mem_over_iff]
  rfl

private instance representableElementsCoverDense
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (U : C) :
    (representableElements J U).IsCoverDense
      (elementTopology ((presheafToSheaf J (Type u)).obj (yoneda.obj U))) where
  is_cover X := by
    rw [element_cover_iff]
    let η := toSheafify J (yoneda.obj U)
    apply J.superset_covering _ (Presheaf.imageSieve_mem J η X.unop.2)
    intro V f hf
    obtain ⟨a, ha⟩ := hf
    let Y := Over.mk a
    let g : (representableElements J U).obj Y ⟶ X :=
      (Functor.Elements.homMk f.op ha.symm).op
    exact ⟨_, g, 𝟙 _, Presieve.in_coverByImage _ g, by simp [g, representableElements,
      elementProjection, opOpEquivalence]⟩

set_option backward.isDefEq.respectTransparency false in
private instance representableElementsLocallyFull
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (U : C) :
    (representableElements J U).IsLocallyFull
      (elementTopology ((presheafToSheaf J (Type u)).obj (yoneda.obj U))) where
  functorPushforward_imageSieve_mem {X Y} f := by
    rw [representableElements_cover_iff, J.mem_over_iff]
    let η := toSheafify J (yoneda.obj U)
    have he : η.app (op X.left) (f.unop.hom.unop ≫ Y.hom) = η.app (op X.left) X.hom := by
      change η.app _ ((yoneda.obj U).map f.unop.hom Y.hom) = _
      rw [NatTrans.naturality_apply]
      exact f.unop.map_val
    apply J.superset_covering _ (Presheaf.equalizerSieve_mem J η _ _ he)
    intro V k hk
    change k ≫ (f.unop.hom.unop ≫ Y.hom) = k ≫ X.hom at hk
    rw [Sieve.overEquiv_iff]
    let l : Over.mk (k ≫ X.hom) ⟶ Y := Over.homMk (k ≫ f.unop.hom.unop)
      (by change (k ≫ f.unop.hom.unop) ≫ Y.hom = k ≫ X.hom
          simpa only [Category.assoc] using hk)
    refine ⟨l, ?_⟩
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    rfl

private instance representableElementsDense
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (U : C) :
    (representableElements J U).IsDenseSubsite (J.over U)
      (elementTopology ((presheafToSheaf J (Type u)).obj (yoneda.obj U))) where
  functorPushforward_mem_iff := representableElements_cover_iff J U _

private def inverseHomComparison
    {A B : Type*} [Category A] [Category B] (E : A ≌ B)
    (H : Aᵒᵖ × A ⥤ A) (K : Bᵒᵖ × B ⥤ B)
    (a : H ⋙ E.functor ≅ (E.functor.op.prod E.functor) ⋙ K) :
    K ⋙ E.inverse ≅ (E.inverse.op.prod E.inverse) ⋙ H :=
  (Iso.isoCompInverse (H := E)
    (Functor.associator _ _ _ ≪≫
      Iso.inverseCompIso (G := E.op.prod E) a)).symm

private def inverseEquivalenceCore
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (T : RingedPresentationEquivalenceCore R S) : RingedPresentationEquivalenceCore S R where
  modules := T.modules.symm
  forwardUnit := T.modules.inverse.mapIso T.forwardUnit.symm ≪≫ T.modules.unitIso.symm.app _
  forwardHom := by
    let := HasDerivedCategory.standard (PresentationModules R)
    let := HasDerivedCategory.standard (PresentationModules S)
    let := Functor.additive_of_preserves_binary_products T.modules.functor
    let := Functor.additive_of_preserves_binary_products T.modules.inverse
    exact T.forwardHom.map (fun a ↦ inverseHomComparison T.modules.mapDerivedCategory _ _ a)

private theorem ordinarySliceComparison
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (U : C) :
    ∃ E : RingedPresentationEquivalenceCore (R.over U)
        (presentationElementRing R ((presheafToSheaf J (Type u)).obj (yoneda.obj U))),
      Nonempty (SheafOfModules.overFunctor (localCoefficientRings R) U ⋙ E.modules.functor ≅
        elementModulePullback.{u, u} (localCoefficientRings R)
          ((presheafToSheaf J (Type u)).obj (yoneda.obj U))) := by
  let A := (presheafToSheaf J (Type u)).obj (yoneda.obj U)
  obtain ⟨T, ⟨q⟩⟩ := restrictionEquivalenceCore (K := J.over U) (representableElements J U)
    (presentationElementRing R A)
  let E := inverseEquivalenceCore T
  refine ⟨E, ⟨?_⟩⟩
  have z : elementModulePullback.{u, u} (localCoefficientRings R) A ⋙ T.modules.functor ≅
      SheafOfModules.overFunctor (localCoefficientRings R) U :=
    Functor.isoWhiskerLeft (elementModulePullback.{u, u} (localCoefficientRings R) A) q.symm ≪≫
      NatIso.ofComponents (fun M ↦ Iso.refl _) (by intro M N f; ext X x; rfl)
  exact Iso.compInverseIso (H := T.modules) z.symm

end CategoryTheory
