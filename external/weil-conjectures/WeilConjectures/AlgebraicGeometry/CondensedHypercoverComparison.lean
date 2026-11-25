/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianHypercoverTotal
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.CategoryTheory.SimplicialMatchingObject
public import Mathlib.Algebra.Homology.CochainComplexPlus
import WeilConjectures.AlgebraicGeometry.CondensedHypercoverInjectiveRow
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianHypercoverQuasiIso
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianHypercoverRowComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianEvaluationColimits
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjectiveResolution
import WeilConjectures.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex

/-! # Natural hypercover comparison for internal condensed module objects -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj Simplicial
namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false

private noncomputable def chainDerivedUnit
    {C B : Type*} [Category* C] [Category* B] [Abelian C] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ B) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
  (Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso B).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)) DerivedCategory.Qh ≪≫
    Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ)) F.rightDerivedFunctorUnit ≫
  ((Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C)
      F.rightDerivedFunctor).hom

private instance chainDerivedUnit_isIso
    {C B : Type*} [Category* C] [Category* B] [Abelian C] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ B) [F.Additive] (J : CochainComplex C ℤ) [J.IsKInjective] :
    IsIso ((chainDerivedUnit F).app J) := by
  dsimp only [chainDerivedUnit, NatTrans.comp_app, Functor.whiskerLeft_app]
  infer_instance

private noncomputable def chainHomologyCompIso
    {C B : Type*} [Category* C] [Category* B] [Abelian C] [Abelian B]
    (F : C ⥤ B) [F.Additive] [F.PreservesHomology] (q : ℤ) :
    F.mapHomologicalComplex (.up ℤ) ⋙ HomologicalComplex.homologyFunctor B (.up ℤ) q ≅
      HomologicalComplex.homologyFunctor C (.up ℤ) q ⋙ F :=
  NatIso.ofComponents (fun K ↦ (K.sc q).mapHomologyIso F) (by
    intro K L f
    exact ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor C (.up ℤ) q).map f) F)

private noncomputable def chainDerivedEvaluationUnit
    {C B E : Type*} [Category* C] [Category* B] [Category* E]
    [Abelian C] [Abelian B] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ B) [F.Additive] (ev : B ⥤ E) [ev.Additive] [ev.PreservesHomology]
    (q : ℤ) :
    (F ⋙ ev).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor E (.up ℤ) q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B q ⋙ ev :=
  (Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ ev)) (.up ℤ)).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (chainHomologyCompIso ev q) ≪≫
    Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors B q).symm ev ≪≫
        Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm).hom ≫
  Functor.whiskerRight (chainDerivedUnit F) (DerivedCategory.homologyFunctor B q ⋙ ev) ≫
  (Functor.associator _ _ _).hom

private instance chainDerivedEvaluationUnit_isIso
    {C B E : Type*} [Category* C] [Category* B] [Category* E]
    [Abelian C] [Abelian B] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ B) [F.Additive] (ev : B ⥤ E) [ev.Additive] [ev.PreservesHomology]
    (q : ℤ) (J : CochainComplex C ℤ) [J.IsKInjective] :
    IsIso ((chainDerivedEvaluationUnit F ev q).app J) := by
  dsimp only [chainDerivedEvaluationUnit, NatTrans.comp_app, Functor.whiskerRight_app]
  infer_instance

private theorem compare_via_resolution_naturality
    {C E : Type*} [Category* C] [Category* E] (G S T : C ⥤ E)
    (η : G ⟶ S) (α : G ⟶ T)
    {K L J M : C} (f : K ⟶ L) (i : K ⟶ J) (j : L ⟶ M) (l : J ⟶ M)
    [IsIso (η.app J)] [IsIso (η.app M)]
    [IsIso (T.map i)] [IsIso (T.map j)]
    (hS : S.map i ≫ S.map l = S.map f ≫ S.map j)
    (hT : T.map i ≫ T.map l = T.map f ≫ T.map j) :
    S.map f ≫ (S.map j ≫ inv (η.app M) ≫ α.app M ≫ inv (T.map j)) =
      (S.map i ≫ inv (η.app J) ≫ α.app J ≫ inv (T.map i)) ≫ T.map f := by
  have hη : S.map l ≫ inv (η.app M) = inv (η.app J) ≫ G.map l := by
    apply (cancel_epi (η.app J)).mp
    rw [IsIso.hom_inv_id_assoc, ← Category.assoc, ← η.naturality]
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  apply (cancel_mono (T.map j)).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← reassoc_of% hS, ← hT]
  simp only [IsIso.inv_hom_id_assoc]
  rw [reassoc_of% hη, α.naturality]

-- Internal module categories require deeper colimit and derived-category instance search.
set_option synthInstance.maxSize 4096 in
/-- On bounded-below complexes, the cohomology of pushforward evaluated at a weakly
contractible object is naturally the homology of its inverse-image hypercover total.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1), hypercover computation, and Stacks
Project, Tags 09A2 and 0946.
(auxiliary; not a blueprint node).
Proof: exact evaluation at the affine weakly contractible V identifies evaluated
pushforward cohomology with the homology of the evaluated pushforward complex.
The defining pushforward section formula evaluates this complex at W. The natural
unit from a complex to its derived pushforward is invertible on K-injectives.
Choose a bounded-below termwise-injective resolution for each bounded-below complex.
The injective-row descent theorem and bounded-below row total comparison make its
restriction augmentation into hypercover total sections a quasi-isomorphism.
Weakly contractible term evaluation makes the total carry bounded-below coefficient
quasi-isomorphisms to quasi-isomorphisms. Compose the resulting homology isomorphisms
with the inverses of the two resolution maps. For a coefficient map, lift it between
the K-injective resolutions up to homotopy. The natural derived unit and natural
restriction augmentation commute with this lift. A bounded-below cylinder argument
shows that any functor inverting bounded-below quasi-isomorphisms identifies homotopic
maps, proving naturality of the comparison. No colimit assertion is used here -/
theorem condensedHypercover_comparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (q : ℤ) (V : Y.ProEt) (hVaff : IsAffine V.left)
    (hV : ∀ (F G : Sheaf (Scheme.ProEt.topology Y) (Type (u + 1))) (g : F ⟶ G),
      Epi g → Function.Surjective (g.hom.app (op V)))
    (U : SimplicialObject (Over ((Scheme.proEtaleBaseChange f).obj V)))
    (haff : ∀ n : ℕ, IsAffine (U _⦋n⦌).left.left)
    (hweak : ∀ (n : ℕ) (F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op (U _⦋n⦌).left)))
    (hzero : Epi ((Scheme.ProEt.topology X).yoneda.map (U _⦋0⦌).hom))
    (hone : ∃ c : Fan (fun _ : Fin 2 ↦ U _⦋0⦌), Nonempty (IsLimit c) ∧
      ∃ μ : U _⦋1⦌ ⟶ c.pt,
        (∀ i : Fin 2, μ ≫ c.proj i = U.δ i) ∧
        Epi ((Scheme.ProEt.topology X).yoneda.map μ.left))
    (hhigher : ∀ n : ℕ,
      ∃ c : Cone (SimplicialObject.matchingBoundaryIndex U n).multicospan,
        Nonempty (IsLimit c) ∧ ∃ μ : U _⦋n + 2⦌ ⟶ c.pt,
          (∀ i : Fin (n + 3), μ ≫ c.π.app (WalkingMulticospan.left i) = U.δ i) ∧
          Epi ((Scheme.ProEt.topology X).yoneda.map μ.left)) :
    let A := Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ X)
    let ev := Mod.forget (condensedRingObj Λ Y) ⋙
      (sheafSections (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}).obj (op V)
    let T := (Mod.forget (condensedRingObj Λ X)).mapHomologicalComplex (.up ℤ) ⋙
      Scheme.ProEt.abelianHypercoverTotal X ((Scheme.proEtaleBaseChange f).obj V) U
    Nonempty ((CochainComplex.Plus.ι A ⋙ DerivedCategory.Q ⋙
      (CondensedRing.lowerStar Λ f).rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor _ q ⋙ ev) ≅
      (CochainComplex.Plus.ι A ⋙ T ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (.up ℤ) q)) := by
  classical
  let A := Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    (condensedRingObj Λ X)
  let B := Mod (Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1})
    (condensedRingObj Λ Y)
  let F : A ⥤ B := CondensedRing.lowerStar Λ f
  let W := (Scheme.proEtaleBaseChange f).obj V
  let forget : A ⥤ Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
    Mod.forget (condensedRingObj Λ X)
  let ev : B ⥤ AddCommGrpCat.{u + 1} := Mod.forget (condensedRingObj Λ Y) ⋙
    (sheafSections (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}).obj (op V)
  let evX := forget ⋙
    (sheafSections (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj (op W)
  have : ev.Additive := ⟨by intros; rfl⟩
  have : evX.Additive := ⟨by intros; rfl⟩
  let : IsAffine V.left := hVaff
  have : ((sheafSections (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}).obj
      (op V)).Additive := ⟨by intros; rfl⟩
  have hev := Scheme.ProEt.affine_weaklyContractible_abelian_evaluation_colimits Y V hV
  have : ((sheafSections (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}).obj
    (op V)).PreservesHomology := hev.1
  have : PreservesFiniteLimits
      ((sheafSections (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}).obj (op V)) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  have : PreservesFiniteColimits
      ((sheafSections (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}).obj (op V)) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  have : ev.PreservesHomology := by dsimp [ev]; infer_instance
  let S := DerivedCategory.Q ⋙ F.rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor B q ⋙ ev
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (.up ℤ) q
  let T := forget.mapHomologicalComplex (.up ℤ) ⋙
    Scheme.ProEt.abelianHypercoverTotal X W U
  let G := evX.mapHomologicalComplex (.up ℤ) ⋙ H
  let η : G ⟶ S := chainDerivedEvaluationUnit F ev q
  let α : G ⟶ T ⋙ H := Functor.whiskerRight
    (Functor.whiskerLeft (forget.mapHomologicalComplex (.up ℤ))
      (Scheme.ProEt.abelianHypercoverAugmentation X W U)) H
  let P : CochainComplex.Plus A ⥤
      CochainComplex.Plus (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) :=
    ObjectProperty.lift _ (CochainComplex.Plus.ι A ⋙ forget.mapHomologicalComplex (.up ℤ))
      (fun K ↦ by
        obtain ⟨n, hn⟩ := K.property
        have := hn
        refine ⟨n, ?_⟩
        change CochainComplex.IsStrictlyGE
          ((forget.mapHomologicalComplex (.up ℤ)).obj K.obj) n
        infer_instance)
  have hT (E L : CochainComplex.Plus A) (g : E ⟶ L) (hg : QuasiIso g.hom) :
      IsIso ((T ⋙ H).map g.hom) := by
    have := hg
    have : QuasiIso (P.map g).hom := by
      change QuasiIso ((forget.mapHomologicalComplex (.up ℤ)).map g.hom)
      infer_instance
    have hq := Scheme.ProEt.abelianHypercoverTotal_map_quasiIso_of_weaklyContractible
      X W U haff hweak (P.obj E) (P.obj L) (P.map g) this
    have : QuasiIso (T.map g.hom) := hq
    change IsIso (HomologicalComplex.homologyMap (T.map g.hom) q)
    infer_instance
  have hα (J : CochainComplex.Plus A) (hJ : ∀ n : ℤ, Injective (J.obj.X n)) :
      IsIso (α.app J.obj) := by
    have hrow (n : ℤ) : QuasiIso
        (Scheme.ProEt.abelianHypercoverRowAugmentationComplex X W U
          (forget.obj (J.obj.X n))) := by
      have := hJ n
      exact condensedHypercoverInjectiveRow Λ X W U hzero hone hhigher (J.obj.X n)
    have hq := Scheme.ProEt.abelianHypercoverAugmentation_quasiIso_of_rows X W U
      (P.obj J) hrow
    have : QuasiIso ((Scheme.ProEt.abelianHypercoverAugmentation X W U).app
        ((forget.mapHomologicalComplex (.up ℤ)).obj J.obj)) := hq
    change IsIso (HomologicalComplex.homologyMap
      ((Scheme.ProEt.abelianHypercoverAugmentation X W U).app
        ((forget.mapHomologicalComplex (.up ℤ)).obj J.obj)) q)
    infer_instance
  have hR (E : CochainComplex.Plus A) : ∃ R : E.obj.KInjectiveResolution,
      (∃ n : ℤ, R.I.IsStrictlyGE n) ∧ ∀ n : ℤ, Injective (R.I.X n) := by
    obtain ⟨n, hn⟩ := E.property
    have := hn
    obtain ⟨R, hR, hI⟩ := CochainComplex.KInjectiveResolution.exists_of_isStrictlyGE E.obj n
    exact ⟨R, ⟨n, hR⟩, hI⟩
  choose R hbound hinj using hR
  let J (E : CochainComplex.Plus A) : CochainComplex.Plus A := ⟨(R E).I, hbound E⟩
  let i (E : CochainComplex.Plus A) : E ⟶ J E := ObjectProperty.homMk (R E).ι
  have hS (E : CochainComplex.Plus A) : IsIso (S.map (i E).hom) := by
    dsimp [S, i]
    infer_instance
  have hTi (E : CochainComplex.Plus A) : IsIso ((T ⋙ H).map (i E).hom) :=
    hT E (J E) (i E) (R E).quasiIso_ι
  have hη (E : CochainComplex.Plus A) : IsIso (η.app (J E).obj) := by
    change IsIso ((chainDerivedEvaluationUnit F ev q).app (R E).I)
    infer_instance
  have hαi (E : CochainComplex.Plus A) : IsIso (α.app (J E).obj) := hα (J E) (hinj E)
  refine ⟨NatIso.ofComponents (fun E ↦
    asIso (S.map (i E).hom) ≪≫ (asIso (η.app (J E).obj)).symm ≪≫
      asIso (α.app (J E).obj) ≪≫ (asIso ((T ⋙ H).map (i E).hom)).symm) ?_⟩
  intro E L g
  let l : (J E).obj ⟶ (J L).obj := (R E).map (R L) g.hom
  have hh : Homotopy ((i E).hom ≫ l) (g.hom ≫ (i L).hom) :=
    (R E).mapHomotopy (R L) g.hom
  apply compare_via_resolution_naturality G S (T ⋙ H) η α g.hom (i E).hom (i L).hom l
  · rw [← S.map_comp, ← S.map_comp]
    change (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B q ⋙ ev).map
        (DerivedCategory.Q.map ((i E).hom ≫ l)) =
      (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B q ⋙ ev).map
        (DerivedCategory.Q.map (g.hom ≫ (i L).hom))
    exact congrArg _ (DerivedCategory.Q_map_eq_of_homotopy A hh)
  · rw [← (T ⋙ H).map_comp, ← (T ⋙ H).map_comp]
    exact Scheme.ProEt.map_eq_of_boundedBelow_homotopy
      (T ⋙ H) hT E (J L) _ _ hh

end AlgebraicGeometry.ProEtale
