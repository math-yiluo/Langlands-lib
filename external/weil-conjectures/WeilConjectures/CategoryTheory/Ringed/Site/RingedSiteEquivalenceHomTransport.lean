/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.NativeRingedRestrictionHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.Ringed.RingedHomComplexTransport
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedHomTransport
import WeilConjectures.CategoryTheory.NativeRingedRestrictionEquivalence
import WeilConjectures.CategoryTheory.NativeRingedRestrictionHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Homology.HomComplexProjections
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.Scalar.ScalarIsoInternalHom

/-! # Derived Hom under a site equivalence and coefficient identification

Source: Stacks Project, Tags 03CR, 03D7, 08J7 and 0A95
(blueprint: lem-weil-pbc-ringed-site-equivalence-hom-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe c d vc vd r w w'
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.NativeRestriction
/-! Private copies of the restriction Hom comparison of
`WeilConjectures.CategoryTheory.NativeRingedRestrictionHom`, which keeps them private. -/

set_option backward.isDefEq.respectTransparency false in
private theorem restriction_map_bijective
    {C : Type c} {D : Type d} [Category.{vc} C] [Category.{vd} D]
    (F : C ⥤ D) [F.IsEquivalence] (R : Dᵒᵖ ⥤ RingCat.{max c d vc vd r})
    (M N : PresheafOfModules.{max c d vc vd r} R) :
    Function.Bijective (fun f : M ⟶ N ↦ (PresheafOfModules.pushforward₀ F R).map f) := by
  let W := (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ AddCommGrpCat.{max c d vc vd r}).obj F.op
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
    {C : Type c} {D : Type d} [Category.{vc} C] [Category.{vd} D]
    (F : C ⥤ D) (R : Dᵒᵖ ⥤ CommRingCat.{max c d vc vd r})
    (M N : PresheafOfModules.{max c d vc vd r} (R ⋙ forget₂ _ _)) :
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
    {C : Type c} {D : Type d} [Category.{vc} C] [Category.{vd} D]
    (F : C ⥤ D) (hF : ∀ X : C, (Over.post (X := X) F).IsEquivalence)
    (R : Dᵒᵖ ⥤ CommRingCat.{max c d vc vd r})
    (M N : PresheafOfModules.{max c d vc vd r} (R ⋙ forget₂ _ _)) :
    (PresheafOfModules.pushforward₀ F (R ⋙ forget₂ _ _)).obj
        (PresheafOfModules.homObj M N) ≅
      PresheafOfModules.homObj (R := F.op ⋙ R)
        ((PresheafOfModules.pushforward₀ F (R ⋙ forget₂ _ _)).obj M)
        ((PresheafOfModules.pushforward₀ F (R ⋙ forget₂ _ _)).obj N) := by
  let α := restrictionHomMap.{_, _, _, _, r} F R M N
  have ha (X : Cᵒᵖ) : IsIso (α.app X) := by
    let := hF X.unop
    rw [ConcreteCategory.isIso_iff_bijective]
    exact restriction_map_bijective.{_, _, _, _, r} (Over.post (X := X.unop) F) _ _ _
  exact PresheafOfModules.isoMk (fun X ↦ asIso (α.app X)) (fun _ _ f ↦ α.naturality f)

private theorem restrictionHomIso_hom
    {C : Type c} {D : Type d} [Category.{vc} C] [Category.{vd} D]
    (F : C ⥤ D) (hF : ∀ X : C, (Over.post (X := X) F).IsEquivalence)
    (R : Dᵒᵖ ⥤ CommRingCat.{max c d vc vd r})
    (M N : PresheafOfModules.{max c d vc vd r} (R ⋙ forget₂ _ _)) :
    (restrictionHomIso.{_, _, _, _, r} F hF R M N).hom = restrictionHomMap.{_, _, _, _, r} F R M N
      := by
  unfold restrictionHomIso
  rfl

section Restriction
variable {C : Type c} {D : Type d} [Category.{vc} C] [Category.{vd} D]
  {K : GrothendieckTopology C} {J : GrothendieckTopology D}
  (F : C ⥤ D) [Functor.IsContinuous F K J] (R : Sheaf J CommRingCat.{max c d vc vd r})

private def sheafHomIso (hF : ∀ X : C, (Over.post (X := X) F).IsEquivalence)
    (M N : NativeModules.{max c d vc vd r, d, vd} R) :
    (restrictModules.{_, _, _, _, r} (K := K) F R).obj (SheafOfModules.homObj (R := R) M N) ≅
      SheafOfModules.homObj (R := restrictedCommRing.{_, _, _, _, r} (K := K) F R)
        ((restrictModules.{_, _, _, _, r} (K := K) F R).obj M)
        ((restrictModules.{_, _, _, _, r} (K := K) F R).obj N) :=
  { hom := ⟨restrictionHomMap.{_, _, _, _, r} F R.obj M.val N.val⟩
    inv := ⟨(restrictionHomIso.{_, _, _, _, r} F hF R.obj M.val N.val).inv⟩
    hom_inv_id := by
      apply SheafOfModules.hom_ext
      change restrictionHomMap.{_, _, _, _, r} F R.obj M.val N.val ≫ _ = _
      rw [← restrictionHomIso_hom.{_, _, _, _, r} F hF R.obj M.val N.val]
      exact Iso.hom_inv_id _
    inv_hom_id := by
      apply SheafOfModules.hom_ext
      change _ ≫ restrictionHomMap.{_, _, _, _, r} F R.obj M.val N.val = _
      rw [← restrictionHomIso_hom.{_, _, _, _, r} F hF R.obj M.val N.val]
      exact Iso.inv_hom_id _ }


-- Categorical comparisons elaborate several nested restriction and localization functors.
set_option backward.isDefEq.respectTransparency false in
private theorem sheafHomIso_naturality
    (hF : ∀ X : C, (Over.post (X := X) F).IsEquivalence)
    {M M' N N' : NativeModules.{max c d vc vd r, d, vd} R} (f : M' ⟶ M) (g : N ⟶ N') :
    (restrictModules.{_, _, _, _, r} (K := K) F R).map (SheafOfModules.homObjMap (R := R) f g) ≫
        (sheafHomIso.{_, _, _, _, r} F R hF M' N').hom =
      (sheafHomIso.{_, _, _, _, r} F R hF M N).hom ≫
        SheafOfModules.homObjMap (R := restrictedCommRing.{_, _, _, _, r} (K := K) F R)
          ((restrictModules.{_, _, _, _, r} (K := K) F R).map f)
          ((restrictModules.{_, _, _, _, r} (K := K) F R).map g) := by
  apply SheafOfModules.hom_ext
  ext X φ : 3
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  rfl

end Restriction


private def scalarRoundTrip {C : Type c} [Category.{vc} C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{r}} (a : R ≅ S) :
    SheafOfModules.restrictScalars.{r} a.hom ⋙
      SheafOfModules.restrictScalars a.inv ≅ 𝟭 (SheafOfModules.{r} S) :=
  SheafOfModules.pushforwardComp (F := 𝟭 C) (G := 𝟭 C) a.inv a.hom ≪≫
    SheafOfModules.pushforwardCongr a.inv_hom_id ≪≫ SheafOfModules.pushforwardId S

private def scalarEquivalence {C : Type c} [Category.{vc} C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{r}} (a : R ≅ S) :
    SheafOfModules.{r} S ≌ SheafOfModules.{r} R where
  functor := SheafOfModules.restrictScalars a.hom
  inverse := SheafOfModules.restrictScalars a.inv
  unitIso := (scalarRoundTrip a).symm
  counitIso := scalarRoundTrip a.symm
  functor_unitIso_comp M := by ext V x; rfl

-- The unbounded derived comparisons require elaborating several functor structures.
/-- A site equivalence with an identified coefficient sheaf gives a module
 equivalence compatible with the actual derived internal Hom.
Source: Stacks Project, Tags 03CR, 03D7, 08J7 and 0A95
(blueprint: lem-weil-pbc-ringed-site-equivalence-hom-transport).

Proof: take direct restriction along the inverse site equivalence, followed by
scalar restriction along the given ring isomorphism. Both are additive
equivalences. The first preserves sheaf Hom by equivalence on every slice, and
the second by scalar surjectivity. Compose their ordinary comparisons and their
naturality squares. Countable products give the natural Hom-complex comparison;
functorial K-injective resolutions then give the natural derived comparison.
The composite module functor is the actual structural pushforward: its section
modules, scalar action, restriction maps, and morphism maps agree. -/
theorem siteCoefficientEquivalence_derivedHom
    {C : Type c} {D : Type d} [Category.{vc} C] [Category.{vd} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (e : C ≌ D) [e.inverse.IsDenseSubsite K J]
    (R : Sheaf J CommRingCat.{max c d vc vd r})
    (S : Sheaf K CommRingCat.{max c d vc vd r})
    (a : S ≅ (e.inverse.sheafPushforwardContinuous CommRingCat K J).obj R)
    [HasSheafify J AddCommGrpCat.{max c d vc vd r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]
    [HasSheafify K AddCommGrpCat.{max c d vc vd r}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]
    [HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, c, vc} R)]
    [HasDerivedCategory.{w'} (NativeModules.{max c d vc vd r, d, vd} S)] :
    ∃ E : NativeModules.{max c d vc vd r, c, vc} R ≌
        NativeModules.{max c d vc vd r, d, vd} S,
      ∃ ha : E.functor.Additive,
        Nonempty (E.functor ≅ SheafOfModules.pushforward.{max c d vc vd r}
          ((sheafCompose K
            (forget₂ CommRingCat.{max c d vc vd r} RingCat.{max c d vc vd r})).map a.hom)) ∧
        letI := ha
        Nonempty (derivedInternalHomOfUniverses.{c, vc, max d vd r, w} J R ⋙
          E.functor.mapDerivedCategory ≅
          (E.functor.mapDerivedCategory.op.prod E.functor.mapDerivedCategory) ⋙
            derivedInternalHomOfUniverses.{d, vd, max c vc r, w'} K S) := by
  let R' := restrictedCommRing.{d, c, vd, vc, r} (K := K) e.inverse R
  let T := restrictModules.{d, c, vd, vc, r} (K := K) e.inverse R
  have : T.IsEquivalence := restrictModules_isEquivalence.{c, d, vc, vd, r} e R
  have : T.Additive := restrictModules_additive.{d, c, vd, vc, r} e.inverse R
  let a' := (sheafCompose K
    (forget₂ CommRingCat.{max c d vc vd r} RingCat.{max c d vc vd r})).mapIso a
  let G := scalarEquivalence a'
  have : G.functor.Additive :=
    inferInstanceAs (SheafOfModules.restrictScalars a'.hom).Additive
  let E := T.asEquivalence.trans G
  have ha : E.functor.Additive := by
    change (T ⋙ G.functor).Additive
    infer_instance
  obtain ⟨δ, hδ⟩ := scalarIso_internalHom.{d, vd, max c vc r} R' S a
  have hF (X : D) : (Over.post (X := X) e.inverse).IsEquivalence := inferInstance
  let γ (M N : NativeModules.{max c d vc vd r, c, vc} R) :
      E.functor.obj (SheafOfModules.homObj (R := R) M N) ≅
        SheafOfModules.homObj (R := S) (E.functor.obj M) (E.functor.obj N) :=
    G.functor.mapIso (sheafHomIso.{d, c, vd, vc, r} e.inverse R hF M N) ≪≫
      δ (T.obj M) (T.obj N)
  have hγ {M M' N N' : NativeModules.{max c d vc vd r, c, vc} R}
      (f : M' ⟶ M) (g : N ⟶ N') :
      E.functor.map (SheafOfModules.homObjMap (R := R) f g) ≫ (γ M' N').hom =
        (γ M N).hom ≫ SheafOfModules.homObjMap (R := S)
          (E.functor.map f) (E.functor.map g) := by
    let β (M N : NativeModules.{max c d vc vd r, c, vc} R) :
        T.obj (SheafOfModules.homObj (R := R) M N) ≅
          SheafOfModules.homObj (R := R') (T.obj M) (T.obj N) :=
      sheafHomIso.{d, c, vd, vc, r} e.inverse R hF M N
    have ht : T.map (SheafOfModules.homObjMap (R := R) f g) ≫ (β M' N').hom =
        (β M N).hom ≫ SheafOfModules.homObjMap (R := R') (T.map f) (T.map g) :=
      sheafHomIso_naturality.{d, c, vd, vc, r} e.inverse R hF f g
    have hs : G.functor.map (SheafOfModules.homObjMap (R := R') (T.map f) (T.map g)) ≫
        (δ (T.obj M') (T.obj N')).hom = (δ (T.obj M) (T.obj N)).hom ≫
          SheafOfModules.homObjMap (R := S) (G.functor.map (T.map f))
            (G.functor.map (T.map g)) := hδ (T.map f) (T.map g)
    change G.functor.map (T.map (SheafOfModules.homObjMap (R := R) f g)) ≫
        (G.functor.map (β M' N').hom ≫ (δ (T.obj M') (T.obj N')).hom) =
      (G.functor.map (β M N).hom ≫ (δ (T.obj M) (T.obj N)).hom) ≫
        SheafOfModules.homObjMap (R := S) (G.functor.map (T.map f))
          (G.functor.map (T.map g))
    calc
      _ = G.functor.map (T.map (SheafOfModules.homObjMap (R := R) f g) ≫
          (β M' N').hom) ≫ (δ (T.obj M') (T.obj N')).hom :=
        (G.functor.map_comp_assoc _ _ _).symm
      _ = G.functor.map ((β M N).hom ≫
          SheafOfModules.homObjMap (R := R') (T.map f) (T.map g)) ≫
            (δ (T.obj M') (T.obj N')).hom :=
        congrArg (fun k ↦ G.functor.map k ≫ (δ (T.obj M') (T.obj N')).hom) ht
      _ = G.functor.map (β M N).hom ≫
          (G.functor.map (SheafOfModules.homObjMap (R := R') (T.map f) (T.map g)) ≫
            (δ (T.obj M') (T.obj N')).hom) := G.functor.map_comp_assoc _ _ _
      _ = G.functor.map (β M N).hom ≫ ((δ (T.obj M) (T.obj N)).hom ≫
          SheafOfModules.homObjMap (R := S) (G.functor.map (T.map f))
            (G.functor.map (T.map g))) :=
        congrArg (fun k ↦ G.functor.map (β M N).hom ≫ k) hs
      _ = _ := (Category.assoc _ _ _).symm
  obtain ⟨γc⟩ := homComplex_transport.{c, d, vc, vd, r} R S E.functor γ hγ
  refine ⟨E, ha, ⟨?_, derivedHom_transport.{c, d, vc, vd, r, w, w'} R S E γc⟩⟩
  exact ⟨NatIso.ofComponents
    (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso (Iso.refl _))
    (by intro M N f; apply (SheafOfModules.fullyFaithfulForget _).map_injective; rfl)⟩

end CategoryTheory.NativeRestriction
