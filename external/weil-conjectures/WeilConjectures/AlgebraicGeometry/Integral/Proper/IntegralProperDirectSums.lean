/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralConstructibleCompactness
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperBoundedBelowCoproducts
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import WeilConjectures.AlgebraicGeometry.Integral.Proper.IntegralProperCohomologicalBounds
import WeilConjectures.AlgebraicGeometry.Integral.IntegralIndConstructibleStability
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-!
# Integral proper direct image on localizing categories

The assertion bundle only expands the three conclusions. The theorem specializes it
at the actual ordinary unbounded module-object derived pushforward and the recorded
finite constant-model constructible predicates. IndCons is `ObjectProperty.ind`;
Dic is expanded by testing all cohomology objects. Coproduct preservation uses mapped
cofans, so all their legs are the images of the original coprojections.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe v u₁ u₂ u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The three integral proper direct-image assertions, expanded in ordinary derived
categories. `H₁.ind` and `H₂.ind` are ambient small filtered-colimit closures.
The two `IsIso` statements use the canonical arrows of the truncation zigzag.
For sums, a colimit cofan exists and remains a colimit after applying `F`; its
legs are exactly `F.map` of the source injections. Uniqueness of coproducts makes
this equivalent to invertibility of the canonical coproduct comparison. -/
def IntegralProperDirectImageAssertions
    {A : Type u₁} {B : Type u₂} [Category.{v} A] [Category.{v} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{v} A] [HasDerivedCategory.{v} B]
    (H₁ : ObjectProperty A) (H₂ : ObjectProperty B)
    (C₁ : ObjectProperty (DerivedCategory A)) (C₂ : ObjectProperty (DerivedCategory B))
    (F : DerivedCategory A ⥤ DerivedCategory B) (d : ℕ) : Prop :=
  (∀ N : A, H₁ N →
    C₂ (F.obj ((DerivedCategory.singleFunctor A 0).obj N)) ∧
    (F.obj ((DerivedCategory.singleFunctor A 0).obj N)).IsGE 0 ∧
    (F.obj ((DerivedCategory.singleFunctor A 0).obj N)).IsLE (2 * (d : ℤ) + 1)) ∧
  (∀ N : A, H₁.ind.{v} N →
    (∀ q : ℤ, H₂.ind.{v} ((DerivedCategory.homologyFunctor B q).obj
      (F.obj ((DerivedCategory.singleFunctor A 0).obj N)))) ∧
    (F.obj ((DerivedCategory.singleFunctor A 0).obj N)).IsGE 0 ∧
    (F.obj ((DerivedCategory.singleFunctor A 0).obj N)).IsLE (2 * (d : ℤ) + 1)) ∧
  (∀ K : DerivedCategory A,
    (∀ n : ℤ, H₁.ind.{v} ((DerivedCategory.homologyFunctor A n).obj K)) →
    ∀ q : ℤ,
      IsIso ((DerivedCategory.homologyFunctor B q).map
        (F.map ((DerivedCategory.TStructure.t.truncLEι q).app K))) ∧
      IsIso ((DerivedCategory.homologyFunctor B q).map
        (F.map ((DerivedCategory.TStructure.t.truncGEπ (q - 2 * (d : ℤ) - 1)).app
          ((DerivedCategory.TStructure.t.truncLE q).obj K))))) ∧
  (∀ (I : Type v) (K : I → DerivedCategory A),
    (∀ (i : I) (n : ℤ), H₁.ind.{v} ((DerivedCategory.homologyFunctor A n).obj (K i))) →
    ∃ c : Cofan K, Nonempty (IsColimit c) ∧ Nonempty (IsColimit (F.mapCocone c))) ∧
  (∀ K : DerivedCategory A, localizingClosure C₁ K → localizingClosure C₂ (F.obj K)) ∧
  (∀ (I : Type v) (K : I → DerivedCategory A),
    (∀ i : I, localizingClosure C₁ (K i)) →
    ∃ c : Cofan K, Nonempty (IsColimit c) ∧ Nonempty (IsColimit (F.mapCocone c)))

private theorem coproduct_isGE
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {I : Type*} [HasColimitsOfShape (Discrete I) (DerivedCategory A)]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n)]
    (K : I → DerivedCategory A) (a : ℤ)
    (hK : ∀ i, (K i).IsGE a) : (∐ K).IsGE a := by
  apply (DerivedCategory.isGE_iff (∐ K) a).2
  intro q hq
  exact (isColimitOfPreserves (DerivedCategory.homologyFunctor A q)
    (coproductIsCoproduct K)).isZero_pt
    (Functor.isZero _ fun i ↦ (DerivedCategory.isGE_iff (K i.as) a).1 (hK i.as) q hq)

private theorem truncGE_preservesCoproducts
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {I : Type*} [HasColimitsOfShape (Discrete I) (DerivedCategory A)]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n)]
    (a : ℤ) :
    PreservesColimitsOfShape (Discrete I) ((DerivedCategory.TStructure.t (C := A)).truncGE a) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let T := t.truncGE a
  let π := t.truncGEπ a
  have hK (K : I → DerivedCategory A) : PreservesColimit (Discrete.functor K) T := by
    let L := fun i ↦ T.obj (K i)
    have : (∐ L).IsGE a := coproduct_isGE L a (fun i ↦ inferInstance)
    let f : ∐ K ⟶ ∐ L := Sigma.desc (fun i ↦ π.app (K i) ≫ Sigma.ι L i)
    let r : T.obj (∐ K) ⟶ ∐ L := t.descTruncGE f a
    let c := sigmaComparison T K
    have hc : IsIso c := by
      refine ⟨⟨r, ?_, ?_⟩⟩
      · apply Sigma.hom_ext
        intro i
        change Sigma.ι L i ≫ (c ≫ r) = Sigma.ι L i ≫ 𝟙 _
        rw [← Category.assoc, ι_comp_sigmaComparison]
        apply t.from_truncGE_obj_ext
        simp only [Category.comp_id]
        rw [← Category.assoc]
        change (π.app (K i) ≫ T.map (Sigma.ι K i)) ≫ r =
          π.app (K i) ≫ Sigma.ι L i
        rw [← π.naturality (Sigma.ι K i)]
        change (Sigma.ι K i ≫ (t.truncGEπ a).app (∐ K)) ≫ t.descTruncGE f a = _
        rw [Category.assoc, t.π_descTruncGE, Sigma.ι_comp_desc]
      · apply t.from_truncGE_obj_ext
        dsimp only [r]
        rw [← Category.assoc, t.π_descTruncGE]
        apply Sigma.hom_ext
        intro i
        change Sigma.ι K i ≫ f ≫ c = Sigma.ι K i ≫ π.app (∐ K) ≫ 𝟙 _
        calc
          _ = π.app (K i) ≫ (Sigma.ι L i ≫ c) := by simp [f]
          _ = π.app (K i) ≫ T.map (Sigma.ι K i) := by
            rw [ι_comp_sigmaComparison]
          _ = _ := by simpa using (π.naturality (Sigma.ι K i)).symm
    exact PreservesCoproduct.of_iso_comparison T K
  let : ∀ K : I → DerivedCategory A, PreservesColimit (Discrete.functor K) T := hK
  exact preservesColimitsOfShape_of_discrete T

private theorem sumsOfLowerWindow
    {A : Type u₁} {B : Type u₂} [Category.{v} A] [Category.{v} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{v} A] [HasDerivedCategory.{v} B]
    [HasCoproducts.{v} (DerivedCategory A)] [HasCoproducts.{v} (DerivedCategory B)]
    [HasCoproducts.{v} B]
    [∀ (I : Type v) (q : ℤ),
      PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A q)]
    [∀ (I : Type v) (q : ℤ),
      PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor B q)]
    (S : ObjectProperty (DerivedCategory A))
    (F : DerivedCategory A ⥤ DerivedCategory B)
    (c : ℤ)
    (hS : ∀ (I : Type v) (K : I → DerivedCategory A), (∀ i, S (K i)) → S (∐ K))
    (hw : ∀ K, S K → ∀ q : ℤ,
      IsIso ((F ⋙ DerivedCategory.homologyFunctor B q).map
        ((DerivedCategory.TStructure.t.truncGEπ (q - c)).app K)))
    (hb : ∀ (I : Type v) (a : ℤ) (K : I → DerivedCategory A),
      (∀ i, (K i).IsGE a) → PreservesColimit (Discrete.functor K) F)
    (I : Type v) (K : I → DerivedCategory A) (hK : ∀ i, S (K i)) :
    ∃ c : Cofan K, Nonempty (IsColimit c) ∧ Nonempty (IsColimit (F.mapCocone c)) := by
  have hcomp : IsIso (sigmaComparison F K) := by
    apply (DerivedCategory.isIso_iff B _).2
    intro q
    let H := DerivedCategory.homologyFunctor B q
    let G := F ⋙ H
    let t := DerivedCategory.TStructure.t (C := A)
    let T := t.truncGE (q - c)
    let π := t.truncGEπ (q - c)
    have : PreservesColimitsOfShape (Discrete I) T := truncGE_preservesCoproducts _
    have : PreservesColimit (Discrete.functor (fun i ↦ T.obj (K i))) F :=
      hb I (q - c) _ (fun i ↦ inferInstance)
    have : PreservesColimit (Discrete.functor K ⋙ T) F :=
      preservesColimit_of_iso_diagram F (Discrete.natIso (fun _ ↦ Iso.refl _) :
        Discrete.functor (fun i ↦ T.obj (K i)) ≅ Discrete.functor K ⋙ T)
    have : PreservesColimit (Discrete.functor K) (T ⋙ G) := inferInstance
    let d := sigmaComparison (T ⋙ G) K
    let l := Limits.Sigma.map (fun i ↦ G.map (π.app (K i)))
    let r := G.map (π.app (∐ K))
    have hd : IsIso d := inferInstance
    have hl (i : I) : IsIso (G.map (π.app (K i))) := hw _ (hK i) q
    have : IsIso l := by dsimp only [l]; infer_instance
    have : IsIso r := hw _ (hS I K hK) q
    have square : sigmaComparison G K ≫ r = l ≫ d := by
      apply Sigma.hom_ext
      intro i
      simp only [l, d, r, ι_comp_sigmaComparison_assoc, Sigma.ι_map_assoc]
      change G.map (Sigma.ι K i) ≫ G.map (π.app (∐ K)) =
        G.map (π.app (K i)) ≫
          Sigma.ι (fun i ↦ (T ⋙ G).obj (K i)) i ≫ sigmaComparison (T ⋙ G) K
      rw [ι_comp_sigmaComparison]
      simpa only [Functor.comp_map, ← G.map_comp, Functor.id_map] using
        congrArg G.map (π.naturality (Sigma.ι K i))
    have : IsIso (sigmaComparison G K ≫ r) := by rw [square]; infer_instance
    have : IsIso (sigmaComparison G K) := IsIso.of_isIso_comp_right _ r
    have heq : sigmaComparison G K =
        sigmaComparison H (fun i ↦ F.obj (K i)) ≫ H.map (sigmaComparison F K) :=
      (sigmaComparison_map_desc H (fun i ↦ F.obj (K i)) _
        (fun i ↦ F.map (Sigma.ι K i))).symm
    have : IsIso (sigmaComparison H (fun i ↦ F.obj (K i)) ≫
        H.map (sigmaComparison F K)) := by rw [← heq]; infer_instance
    exact IsIso.of_isIso_comp_left (sigmaComparison H (fun i ↦ F.obj (K i))) _
  have : PreservesColimit (Discrete.functor K) F := PreservesCoproduct.of_iso_comparison F K
  exact ⟨Cofan.mk (∐ K) (Sigma.ι K), ⟨coproductIsCoproduct K⟩,
    ⟨isColimitOfPreserves F (coproductIsCoproduct K)⟩⟩

private theorem smallSupport
    {C : Type u₁} [Category.{v} C] [Preadditive C] [LocallySmall.{v} C]
    {I : Type u₂} (K : I → C) (t : Cofan K) (ht : IsColimit t) :
    Small.{v} {i // ¬ IsZero (K i)} := by
  classical
  let p (i : I) : t.pt ⟶ K i := ht.desc (Cofan.mk (K i) (Pi.single i (𝟙 (K i))))
  have hp (i j : I) : t.inj j ≫ p i =
      Pi.single (M := fun j ↦ K j ⟶ K i) i (𝟙 (K i)) j :=
    ht.fac (Cofan.mk (K i) (Pi.single i (𝟙 (K i)))) (Discrete.mk j)
  apply small_of_injective (f := fun i : {i // ¬ IsZero (K i)} ↦ p i.val ≫ t.inj i.val)
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have he := congrArg (fun f ↦ t.inj i.val ≫ f ≫ p i.val) hij
  have hi : t.inj i.val ≫ p i.val = 𝟙 (K i.val) := by simp [hp]
  have hj : t.inj i.val ≫ p j.val = 0 := by simp [hp, hne]
  have hid : 𝟙 (K i.val) = 0 := by
    simpa only [← Category.assoc, hi, hj, Category.id_comp, zero_comp] using he
  exact i.property ((IsZero.iff_id_eq_zero _).mpr hid)

private theorem preservesCofanOnClass
    {C : Type u₁} {D : Type u₂} [Category.{v} C] [Category.{v} D]
    [Preadditive C] [Preadditive D] [LocallySmall.{v} C]
    (S : ObjectProperty C) (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (hsmall : ∀ (J : Type v) (K : J → C), (∀ j, S (K j)) →
      ∃ c : Cofan K, Nonempty (IsColimit c) ∧ Nonempty (IsColimit (F.mapCocone c)))
    {I : Type u} (K : I → C) (hK : ∀ i, S (K i)) (t : Cofan K) (ht : IsColimit t) :
    Nonempty (IsColimit (F.mapCocone t)) := by
  classical
  have := smallSupport K t ht
  let J := {i // ¬ IsZero (K i)}
  let U : J → C := fun i ↦ K i.val
  let r : Cofan U := Cofan.mk t.pt (fun i ↦ t.inj i.val)
  have hr : IsColimit r := by
    refine Cofan.IsColimit.mk r (fun s ↦ ht.desc (Cofan.mk s.pt
      (fun i ↦ if hi : ¬ IsZero (K i) then s.inj ⟨i, hi⟩ else 0))) ?_ ?_
    · intro s i
      obtain ⟨i, hi⟩ := i
      change t.ι.app (Discrete.mk i) ≫ _ = _
      rw [ht.fac]
      simp only [Cofan.mk_ι_app, dite_eq_left hi]
    · intro s m hm
      apply ht.hom_ext
      intro ⟨i⟩
      rw [ht.fac]
      by_cases hi : ¬ IsZero (K i)
      · simpa only [r, cofan_mk_inj, Cofan.inj, Cofan.mk_ι_app, dite_eq_left hi]
          using hm ⟨i, hi⟩
      · exact (not_not.mp hi).eq_of_src _ _
  let e := (equivShrink.{v} J).symm
  let V : Shrink.{v} J → C := fun j ↦ U (e j)
  let r' : Cofan V := Cofan.mk t.pt (fun j ↦ r.inj (e j))
  have hr' : IsColimit r' := (Cofan.isColimitEquivOfEquiv e r) hr
  obtain ⟨c, ⟨hc⟩, ⟨hFc⟩⟩ := hsmall (Shrink.{v} J) V (fun j ↦ hK (e j).val)
  have : PreservesColimit (Discrete.functor V) F :=
    preservesColimit_of_preserves_colimit_cocone hc hFc
  let q : Cofan (fun j ↦ F.obj (U j)) :=
    Cofan.mk (F.obj t.pt) (fun j ↦ F.map (r.inj j))
  have hq' : IsColimit (Cofan.mk (F.obj t.pt) (fun j ↦ F.map (r'.inj j))) :=
    isColimitCofanMkObjOfIsColimit F V _ hr'
  have hq : IsColimit q := (Cofan.isColimitEquivOfEquiv e q).symm hq'
  refine ⟨{ desc := fun s ↦ hq.desc (Cofan.mk s.pt
      (fun j ↦ s.ι.app (Discrete.mk j.val))), fac := ?_, uniq := ?_ }⟩
  · intro s ⟨i⟩
    by_cases hi : ¬ IsZero (K i)
    · exact hq.fac (Cofan.mk s.pt (fun j ↦ s.ι.app (Discrete.mk j.val)))
        (Discrete.mk ⟨i, hi⟩)
    · exact (F.map_isZero (not_not.mp hi)).eq_of_src _ _
  · intro s m hm
    apply Cofan.IsColimit.hom_ext hq
    intro i
    exact (hm (Discrete.mk i.val)).trans
      (hq.fac (Cofan.mk s.pt (fun j ↦ s.ι.app (Discrete.mk j.val)))
        (Discrete.mk i)).symm

private theorem mapsLocalizingOfRelativeSums
    {C D : Type u₁} [Category.{v} C] [Category.{v} D] [LocallySmall.{v} C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (C₁ : ObjectProperty C) (C₂ : ObjectProperty D)
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (h₁ : IsLocalizingSubcategory (localizingClosure C₁))
    (h₂ : IsLocalizingSubcategory (localizingClosure C₂))
    (hsmall : ∀ (I : Type v) (K : I → C),
      (∀ i, localizingClosure C₁ (K i)) →
      ∃ c : Cofan K, Nonempty (IsColimit c) ∧ Nonempty (IsColimit (F.mapCocone c)))
    (hgen : ∀ K, C₁ K → localizingClosure C₂ (F.obj K)) :
    ∀ K, localizingClosure C₁ K → localizingClosure C₂ (F.obj K) := by
  let P : ObjectProperty C := localizingClosure C₁ ⊓
    (localizingClosure C₂).inverseImage F
  have := h₁.1
  have := h₁.2.1
  have := h₂.1
  have := h₂.2.1
  have hP : IsLocalizingSubcategory P := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro I G hG hGP
    let := hG
    refine ⟨h₁.2.2 G hG (fun i ↦ (hGP i).1), ?_⟩
    let K : I → C := fun i ↦ G.obj ⟨i⟩
    let e : G ≅ Discrete.functor K := Discrete.natIsoFunctor
    let t : Cofan K := (Cocone.precompose e.inv).obj (colimit.cocone G)
    have ht : IsColimit t := (IsColimit.precomposeInvEquiv e _).symm
      (colimit.isColimit G)
    obtain ⟨hf⟩ := preservesCofanOnClass (localizingClosure C₁) F hsmall K
      (fun i ↦ (hGP i).1) t ht
    have : PreservesColimit (Discrete.functor K) F :=
      preservesColimit_of_preserves_colimit_cocone ht hf
    have : PreservesColimit G F := preservesColimit_of_iso_diagram F e.symm
    have hf' : IsColimit (F.mapCocone (colimit.cocone G)) :=
      isColimitOfPreserves F (colimit.isColimit G)
    let hGF : HasColimit (G ⋙ F) := ⟨F.mapCocone (colimit.cocone G), hf'⟩
    let := hGF
    exact (localizingClosure C₂).prop_of_iso
      (hf'.coconePointUniqueUpToIso (colimit.isColimit (G ⋙ F))).symm
      (h₂.2.2 (G ⋙ F) hGF (fun i ↦ (hGP i).2))
  intro K hK
  exact (hK P hP (fun L hL ↦ ⟨fun Q hQ hCQ ↦ hCQ L hL, hgen L hL⟩)).2

private theorem rightDerivedPreservesLower
    {A : Type u₁} {B : Type u₂} [Category.{v} A] [Category.{v} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{v} A] [HasDerivedCategory.{v} B]
    [EnoughInjectives A] [Abelian.HasKInjectiveResolutions A]
    (G : A ⥤ B) [G.Additive]
    (L : DerivedCategory A) (a : ℤ) (hL : L.IsGE a) :
    (G.rightDerivedFunctor.obj L).IsGE a := by
  let K : DerivedCategory.Plus A := ⟨L, ⟨a, hL⟩⟩
  have : K.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff K a).mp hL
  apply (DerivedCategory.isGE_iff _ _).mpr
  intro q hq
  exact (G.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE K a hq).of_iso
    ((DerivedCategory.homologyFunctor B q).mapIso
      (G.rightDerivedFunctorPlusCompatibility.app K)).symm

private theorem lowerWindowOfBounds
    {A : Type u₁} {B : Type u₂} [Category.{v} A] [Category.{v} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{v} A] [HasDerivedCategory.{v} B]
    (S : ObjectProperty (DerivedCategory A))
    (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ] [F.IsTriangulated]
    (c : ℤ)
    (hupper : ∀ (L : DerivedCategory A) (b : ℤ), S L → L.IsLE b →
      (F.obj L).IsLE (b + c))
    (htrunc : ∀ (L : DerivedCategory A), S L → ∀ a : ℤ,
      S ((DerivedCategory.TStructure.t.truncLE a).obj L))
    (K : DerivedCategory A) (hK : S K) (q : ℤ) :
    IsIso ((F ⋙ DerivedCategory.homologyFunctor B q).map
      ((DerivedCategory.TStructure.t.truncGEπ (q - c)).app K)) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let T := (t.triangleLEGE (q - c - 1) (q - c) (by omega)).obj K
  let U := F.mapTriangle.obj T
  have hU : U ∈ distTriang _ :=
    F.map_distinguished T (t.triangleLEGE_distinguished _ _ (by omega) K)
  have hle := hupper ((t.truncLE (q - c - 1)).obj K) (q - c - 1)
    (htrunc K hK _) inferInstance
  have h₀ : IsZero ((DerivedCategory.homologyFunctor B q).obj U.obj₁) :=
    (DerivedCategory.isLE_iff _ _).1 hle _ (by omega)
  have h₁ : IsZero ((DerivedCategory.homologyFunctor B (q + 1)).obj U.obj₁) :=
    (DerivedCategory.isLE_iff _ _).1 hle _ (by omega)
  have : Mono ((DerivedCategory.homologyFunctor B q).map U.mor₂) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff U hU q).2
      (h₀.eq_of_src _ _)
  have : Epi ((DerivedCategory.homologyFunctor B q).map U.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
      U hU q (q + 1) rfl).2 (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor B q).map U.mor₂)

private theorem finiteWindowOfBounds
    {A : Type u₁} {B : Type u₂} [Category.{v} A] [Category.{v} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{v} A] [HasDerivedCategory.{v} B]
    (S : ObjectProperty (DerivedCategory A))
    (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ] [F.IsTriangulated]
    (c : ℤ)
    (hlower : ∀ (L : DerivedCategory A) (a : ℤ), L.IsGE a → (F.obj L).IsGE a)
    (hupper : ∀ (L : DerivedCategory A) (b : ℤ), S L → L.IsLE b →
      (F.obj L).IsLE (b + c))
    (htrunc : ∀ (L : DerivedCategory A), S L → ∀ a : ℤ,
      S ((DerivedCategory.TStructure.t.truncLE a).obj L))
    (K : DerivedCategory A) (hK : S K) (q : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor B q).map
      (F.map ((DerivedCategory.TStructure.t.truncLEι q).app K))) ∧
    IsIso ((DerivedCategory.homologyFunctor B q).map
      (F.map ((DerivedCategory.TStructure.t.truncGEπ (q - c)).app
        ((DerivedCategory.TStructure.t.truncLE q).obj K)))) := by
  let t := DerivedCategory.TStructure.t (C := A)
  constructor
  · let T := (t.triangleLEGE q (q + 1) rfl).obj K
    let U := F.mapTriangle.obj T
    have hU : U ∈ distTriang _ :=
      F.map_distinguished T (t.triangleLEGE_distinguished q (q + 1) rfl K)
    have hge : (F.obj ((t.truncGE (q + 1)).obj K)).IsGE (q + 1) :=
      hlower _ _ inferInstance
    have h₀ : IsZero ((DerivedCategory.homologyFunctor B (q - 1)).obj U.obj₃) :=
      (DerivedCategory.isGE_iff _ _).1 hge _ (by omega)
    have h₁ : IsZero ((DerivedCategory.homologyFunctor B q).obj U.obj₃) :=
      (DerivedCategory.isGE_iff _ _).1 hge _ (by omega)
    have : Mono ((DerivedCategory.homologyFunctor B q).map U.mor₁) :=
      (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
        U hU (q - 1) q (by omega)).2 (h₀.eq_of_src _ _)
    have : Epi ((DerivedCategory.homologyFunctor B q).map U.mor₁) :=
      (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff U hU q).2
        (h₁.eq_of_tgt _ _)
    exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor B q).map U.mor₁)
  · exact lowerWindowOfBounds S F c hupper htrunc _ (htrunc K hK q) q

/-- Integral proper direct image has the heart bound `[0,2d+1]`, the canonical
finite-window property, and preserves arbitrary sums on Dic and on Loc(Dbc). -/
theorem integralProperDirectSums
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d : WithBot ℕ∞)) :
    IntegralProperDirectImageAssertions
      (IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X)
      (IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) Y)
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X)
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) Y)
      (CondensedRing.lowerStar (Profinite.padicIntegersRingObj ℓ E) p).rightDerivedFunctor d := by
  let Λ := Profinite.padicIntegersRingObj ℓ E
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let B := Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)
  let F := (CondensedRing.lowerStar Λ p).rightDerivedFunctor
  let C₁ := constantModelBoundedConstructible Λ X
  let C₂ := constantModelBoundedConstructible Λ Y
  let S : ObjectProperty (DerivedCategory A) := fun K ↦ ∀ n : ℤ,
    ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
      ((DerivedCategory.homologyFunctor A n).obj K)
  have : HasColimitsOfSize.{u + 1, u + 1} A := IsGrothendieckAbelian.hasColimits A
  have : HasColimitsOfSize.{u + 1, u + 1} B := IsGrothendieckAbelian.hasColimits B
  have : HasCoproducts.{u + 1} A := fun I ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete I)
  have : HasCoproducts.{u + 1} B := fun I ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete I)
  have : HasCoproducts.{u + 1} (DerivedCategory A) := derived_hasCoproducts
  have : HasCoproducts.{u + 1} (DerivedCategory B) := derived_hasCoproducts
  obtain ⟨hC, hI, hgen, hupper⟩ :=
    integralProperCohomologicalBounds ℓ E k p₀ hp₀ hpℓ X Y p d hd
  obtain ⟨htrunc, hsum, hloc⟩ :=
    integralIndConstructibleStability ℓ E k p₀ hp₀ hpℓ X
  have hlower (K : DerivedCategory A) (a : ℤ) (hK : K.IsGE a) :
      (F.obj K).IsGE a := rightDerivedPreservesLower _ K a hK
  have hsums := sumsOfLowerWindow S F (2 * (d : ℤ) + 1)
    (fun I K hK ↦ hsum I K hK _ (coproductIsCoproduct K))
    (lowerWindowOfBounds S F _ hupper htrunc)
    (fun I a K hK ↦ CondensedRing.condensed_boundedBelow_preservesCoproduct Λ p I a K hK)
  have hlocsums (I : Type (u + 1)) (K : I → DerivedCategory A)
      (hK : ∀ i, localizingClosure C₁ (K i)) :
      ∃ c : Cofan K, Nonempty (IsColimit c) ∧ Nonempty (IsColimit (F.mapCocone c)) :=
    hsums I K (fun i ↦ hloc _ (hK i))
  have hX := (localizingClosure_exists Λ X C₁).2.2.2.1
  have hY := (localizingClosure_exists Λ Y C₂).2.2.2.1
  have hmaps := mapsLocalizingOfRelativeSums C₁ C₂ F hX hY hlocsums
    (fun K hK P hP hCP ↦ hCP _ (hgen K hK))
  refine ⟨?_, ?_, ?_, hsums, hmaps, hlocsums⟩
  · intro N hN
    obtain ⟨hc, hb⟩ := hC N hN
    exact ⟨hc, hlower _ 0 inferInstance, hb⟩
  · intro N hN
    obtain ⟨hi, hb⟩ := hI N hN
    exact ⟨hi, hlower _ 0 inferInstance, hb⟩
  · intro K hK q
    have he : q - (2 * (d : ℤ) + 1) = q - 2 * (d : ℤ) - 1 := by omega
    have hw := finiteWindowOfBounds S F (2 * (d : ℤ) + 1) hlower hupper htrunc K hK q
    refine ⟨hw.1, ?_⟩
    exact (congrArg (fun a : ℤ ↦ IsIso ((DerivedCategory.homologyFunctor B q).map
      (F.map ((DerivedCategory.TStructure.t.truncGEπ a).app
        ((DerivedCategory.TStructure.t.truncLE q).obj K))))) he).mp hw.2

end AlgebraicGeometry.ProEtale
