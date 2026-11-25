/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap
import WeilConjectures.AlgebraicGeometry.RawRestrictedResolutionEvaluation
import WeilConjectures.AlgebraicGeometry.Sites.TorsionAcyclic

/-! # Evaluation part of the raw restricted comparison

(blueprint: lem-sbc-raw-restricted-cohomology-comparison-evaluation-is-iso).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

private theorem evaluation_isIso_of_iso
    {E : Type*} [Category.{v + 1} E] [Preadditive E]
    (T : E ⥤ AddCommGrpCat.{v + 1}) [T.Additive] {A B B' : E}
    (x : T.obj A) (e : B ≅ B')
    [IsIso (RawRestrictedComparison.Evaluation.evaluate T x (B := B))] :
    IsIso (RawRestrictedComparison.Evaluation.evaluate T x (B := B')) := by
  let H := preadditiveCoyoneda.obj (op A)
  have he : H.map e.hom ≫ RawRestrictedComparison.Evaluation.evaluate T x =
      RawRestrictedComparison.Evaluation.evaluate T x ≫ T.map e.hom := by
    ext f
    change T.map (f ≫ e.hom) x = T.map e.hom (T.map f x)
    rw [T.map_comp]
    rfl
  have : IsIso (H.map e.hom ≫ RawRestrictedComparison.Evaluation.evaluate T x) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left (H.map e.hom) _

private theorem evaluation_isIso_on_injectives {S Y : Scheme.{v}}
    (h : Y ⟶ S) (U : S.Etale)
    (J : CochainComplex.Plus
      (InjectiveObject (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}))) :
    let W := (MorphismProperty.Over.pullback @Etale ⊤ h).obj U
    let A := (upperStar AddCommGrpCat.{v + 1} h).obj
      (RawRestrictedComparison.freeSheaf S U)
    let T := RawRestrictedComparison.sectionsFunctor W ⋙
      DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0
    let x := (RawRestrictedComparison.zeroIso W A).inv
      (RawRestrictedComparison.generator h U)
    IsIso (RawRestrictedComparison.Evaluation.evaluate T x
      (B := DerivedCategory.Plus.Q.obj
        ((InjectiveObject.ι _).mapCochainComplexPlus.obj J))) := by
  let W := (MorphismProperty.Over.pullback @Etale ⊤ h).obj U
  let A := (upperStar AddCommGrpCat.{v + 1} h).obj
    (RawRestrictedComparison.freeSheaf S U)
  let T := RawRestrictedComparison.sectionsFunctor W ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0
  let x := (RawRestrictedComparison.zeroIso W A).inv
    (RawRestrictedComparison.generator h U)
  let I := (InjectiveObject.ι _).mapCochainComplexPlus.obj J
  let LI : CochainComplex
      (Sheaf W.left.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ :=
    ((upperStar AddCommGrpCat.{v + 1} W.hom).mapHomologicalComplex (.up ℤ)).obj I.obj
  have (n : ℤ) : Injective (LI.X n) :=
    injective_upperStar_obj_of_etale_addCommGrp W.hom ((J.obj.X n).obj)
  obtain ⟨d, hd⟩ := J.property
  have : J.obj.IsStrictlyGE d := hd
  have : I.obj.IsStrictlyGE d := by
    change CochainComplex.IsStrictlyGE
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj) d
    infer_instance
  have : LI.IsStrictlyGE d := by dsimp only [LI]; infer_instance
  have : LI.IsKInjective := CochainComplex.isKInjective_of_injective LI d
  have (n : ℤ) : Injective (I.obj.X n) := by
    change Injective ((J.obj.X n).obj)
    exact (J.obj.X n).property
  have : I.obj.IsKInjective := CochainComplex.isKInjective_of_injective I.obj d
  obtain ⟨e, he⟩ := RawRestrictedComparison.exists_rawRestrictedHomotopySectionsIso h U I.obj
  let δ := RawRestrictedComparison.resolutionSectionsIso W I
  let K₀ := (HomotopyCategory.quotient _ (.up ℤ)).obj
    ((CochainComplex.singleFunctor _ 0).obj A)
  let K₁ := (HomotopyCategory.quotient _ (.up ℤ)).obj I.obj
  let α := (DerivedCategory.Plus.singleFunctor _ 0).obj A
  let β := DerivedCategory.Plus.Q.obj I
  let q : (K₀ ⟶ K₁) → (α ⟶ β) := fun g ↦
    DerivedCategory.Plus.ι.preimage (DerivedCategory.Qh.map g)
  have hq : Function.Bijective q := by
    exact (Functor.FullyFaithful.homEquiv
      (Functor.FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι)).symm.bijective.comp
        (CochainComplex.IsKInjective.Qh_map_bijective K₀ I.obj)
  have hc : ∀ g : K₀ ⟶ K₁,
      δ.hom (T.map (q g) x) = e.hom g := by
    intro g
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ (.up ℤ)).map_surjective g
    rw [he f]
    exact RawRestrictedComparison.rawRestricted_resolution_evaluation h U I f
  have hb : Function.Bijective (fun g : α ⟶ β ↦ δ.hom (T.map g x)) := by
    have hh : Function.Bijective (fun g : K₀ ⟶ K₁ ↦ δ.hom (T.map (q g) x)) := by
      simpa only [hc] using
        (ConcreteCategory.isIso_iff_bijective e.hom).mp (by infer_instance)
    exact (Function.Bijective.of_comp_iff _ hq).mp hh
  have hm : Function.Bijective (fun g : α ⟶ β ↦ T.map g x) :=
    (Function.Bijective.of_comp_iff'
      ((ConcreteCategory.isIso_iff_bijective δ.hom).mp (by infer_instance)) _).mp hb
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hm

/-- The evaluation at the represented identity is invertible before the explicit
shift identification.  This is the derived Yoneda and sections calculation.
Source: Stacks Project, Tag 03Q8 and Cohomology on Sites, Tags 072W, 0BKV and 0D6F.
(blueprint: lem-sbc-raw-restricted-cohomology-comparison-evaluation-is-iso).

Proof: choose a bounded-below injective resolution of `F`.  Restriction to the
etale pullback preserves injectives by exact extension by zero.  The derived
localization bijection identifies morphisms from the free represented sheaf
with homotopy classes of maps into that resolution, while the sheafification,
free-abelian Yoneda and sections adjunction identifies those classes with
cohomology classes of the restricted sections complex.  Evaluation at the
represented identity is exactly this identification, including degree zero and
the empty pullback.
-/
theorem isIso_rawRestrictedCohomologyComparisonEvaluation {S Y : Scheme.{v}}
    (h : Y ⟶ S) (p : ℕ) (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (U : S.Etale) :
    IsIso (let W := (MorphismProperty.Over.pullback @Etale ⊤ h).obj U
      let A := (upperStar AddCommGrpCat.{v + 1} h).obj
        (RawRestrictedComparison.freeSheaf S U)
      let x := (RawRestrictedComparison.zeroIso W A).inv
        (RawRestrictedComparison.generator h U)
      let T := RawRestrictedComparison.sectionsFunctor W ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0
      RawRestrictedComparison.Evaluation.evaluate T x :
        AddCommGrpCat.of
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
                ((upperStar AddCommGrpCat.{v + 1} h).obj
                  (RawRestrictedComparison.freeSheaf S U)) ⟶
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(p : ℤ)⟧) ⟶
          (RawRestrictedComparison.sectionsFunctor
            ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U) ⋙
            DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).obj
            (((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(p : ℤ)⟧)) := by
  let K := ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(p : ℤ)⟧
  obtain ⟨n, hn⟩ := K.property
  have : K.IsGE n := (K.isGE_ι_obj_iff n).mp hn
  obtain ⟨J, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K n
  have := evaluation_isIso_on_injectives h U J
  exact evaluation_isIso_of_iso _ _ e

end AlgebraicGeometry.Etale
