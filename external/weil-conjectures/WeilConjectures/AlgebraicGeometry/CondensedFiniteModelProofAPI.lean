/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # Shared proof API for finite coefficient descent

The private factorization and exact derived composition helpers formerly lived in the
two-colimit and flat-coefficient proofs. They are kept here so their earlier
support-induction dependencies can reuse them without a cycle. The composite of the
derived functors of exact functors commutes with the shifts
(`CategoryTheory.Functor.leftComp_shift`).
This module introduces no new mathematical obligation.
-/

@[expose] public section

universe u wC wD wE vC vD vE uC uD uE
open CategoryTheory Limits MonoidalCategory MonObj Abelian ZeroObject
open scoped CategoryTheory.Obj CategoryTheory.Functor

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.CommShift.ofIso CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory

section HomFactorization
set_option linter.unusedSectionVars false
universe v w uI vI
open CategoryTheory.Pretriangulated Preadditive
namespace CategoryTheory
variable {D : Type w} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {I : Type uI} [Category.{vI} I] [IsFiltered I] {N : I ⥤ D} (c : Cocone N)

private def factors (K : D) : Prop :=
  ∀ f : K ⟶ c.pt, ∃ (i : I) (g : K ⟶ N.obj i), f = g ≫ c.ι.app i
private lemma factors_iso {K L : D} (e : K ≅ L) (h : factors c K) : factors c L := by
  intro f
  obtain ⟨i, g, hg⟩ := h (e.hom ≫ f)
  refine ⟨i, e.inv ≫ g, ?_⟩
  rw [Category.assoc, ← hg]
  simp
private def shiftFactors : ObjectProperty D :=
  fun K ↦ ∀ n : ℤ, factors c (K⟦n⟧)

private lemma shiftFactors_of_hom_colimit
    {A : Type*} [Category A] {J : Type v} [SmallCategory J] [IsFiltered J]
    (N : J ⥤ A) [HasColimit N] (Q : A ⥤ D) (S : D)
    (h : ∀ n : ℤ, IsIso (colimit.desc _
      ((Q ⋙ shiftFunctor D n ⋙ preadditiveCoyoneda.obj (Opposite.op S)).mapCocone
        (colimit.cocone N)))) :
    shiftFactors (Q.mapCocone (colimit.cocone N)) S := by
  intro n f
  let F := Q ⋙ shiftFunctor D (-n) ⋙ preadditiveCoyoneda.obj (Opposite.op S)
  let t := F.mapCocone (colimit.cocone N)
  let p := colimit.desc (N ⋙ F) t
  have : IsIso p := h (-n)
  let adj := (shiftEquiv D n).toAdjunction
  let ff := adj.homEquiv S _ f
  let z := (inv p) ff
  obtain ⟨i, g, hg⟩ := Concrete.colimit_exists_rep (N ⋙ F) z
  have hfg : p ((colimit.ι (N ⋙ F) i) g) = ff := by
    rw [hg]
    exact ConcreteCategory.congr_hom (IsIso.inv_hom_id p) ff
  have he : g ≫ (Q.map (colimit.ι N i))⟦-n⟧' = ff := by
    change (colimit.ι (N ⋙ F) i ≫ p) g = ff at hfg
    rw [colimit.ι_desc] at hfg
    exact hfg
  refine ⟨i, (adj.homEquiv S _).symm g, ?_⟩
  apply (adj.homEquiv S _).injective
  rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
  exact he.symm
private lemma factors_of_colimit_cocone
    {A : Type*} [Category A] {J : Type*} [Category J] [IsFiltered J]
    (N : J ⥤ A) [HasColimit N] (Q : A ⥤ D) (c : Cocone N) (hc : IsColimit c) (K : D)
    (h : factors (Q.mapCocone (colimit.cocone N)) K) : factors (Q.mapCocone c) K := by
  let e := (colimit.isColimit N).coconePointUniqueUpToIso hc
  have he (i : J) : colimit.ι N i ≫ e.hom = c.ι.app i :=
    (colimit.isColimit N).comp_coconePointUniqueUpToIso_hom hc i
  intro f
  obtain ⟨i, g, hg⟩ := h (f ≫ Q.map e.inv)
  change f ≫ Q.map e.inv = g ≫ Q.map (colimit.ι N i) at hg
  refine ⟨i, g, ?_⟩
  calc
    f = (f ≫ Q.map e.inv) ≫ Q.map e.hom := by simp
    _ = (g ≫ Q.map (colimit.ι N i)) ≫ Q.map e.hom := by rw [hg]
    _ = g ≫ Q.map (c.ι.app i) := by rw [Category.assoc, ← Q.map_comp, he]
end CategoryTheory
end HomFactorization
namespace CategoryTheory.Functor
section DerivedCompositionAPI
variable {C : Type uC} {D : Type uD} {E : Type uE}
  [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D] [HasDerivedCategory.{wE} E]
  {F : C ⥤ D} {G : D ⥤ E} {FG : C ⥤ E}
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [FG.Additive] [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
private noncomputable abbrev derivedComp (e : F ⋙ G ≅ FG) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ FG.mapDerivedCategory :=
  (mapDerivedCategoryCompIso F G) ≪≫ mapDerivedCategoryNatIso e

end DerivedCompositionAPI
section TransportAPI
variable {C D E : Type*} [Category C] [Category D] [Category E]
  {F F' : C ⥤ D} {G G' : D ⥤ E} {FG FG' : C ⥤ E}
private noncomputable abbrev transportComp (a : F ≅ F') (b : G ≅ G') (c : FG ≅ FG')
    (e : F' ⋙ G' ≅ FG') : F ⋙ G ≅ FG :=
  isoWhiskerLeft F b ≪≫ isoWhiskerRight a G' ≪≫ e ≪≫ c.symm

end TransportAPI
end CategoryTheory.Functor

namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
section LeftTransport
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

variable [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]

variable [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCountableCoproducts D]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D]

private lemma leftComp_transport (G : D ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {FG : C ⥤ E} [FG.Additive] [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
    (e : F ⋙ G ≅ FG) :
    (F.leftDerivedFunctorCompIso G).symm ≪≫ (F ⋙ G).leftDerivedFunctorNatIso e =
      transportComp F.leftDerivedFunctorIsoMapDerivedCategory
        G.leftDerivedFunctorIsoMapDerivedCategory FG.leftDerivedFunctorIsoMapDerivedCategory
        (derivedComp e) := by
  simp [leftDerivedFunctorCompIso, leftDerivedFunctorNatIso, transportComp, derivedComp,
    Iso.trans_assoc, ← isoWhiskerLeft_symm, ← isoWhiskerRight_symm]

/-- For exact functors `F`, `G` and `FG` with `F ⋙ G ≅ FG`, the comparison
`L F ⋙ L G ≅ L FG` of their derived functors commutes with the shifts, for the shifts
transported from the derived functors `F.mapDerivedCategory`. -/
lemma leftComp_shift (G : D ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {FG : C ⥤ E} [FG.Additive] [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
    (e : F ⋙ G ≅ FG) :
    let := CommShift.ofIso F.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
    let := CommShift.ofIso G.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
    let := CommShift.ofIso FG.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
    NatTrans.CommShift ((F.leftDerivedFunctorCompIso G).symm ≪≫
      (F ⋙ G).leftDerivedFunctorNatIso e).hom ℤ := by
  let := CommShift.ofIso F.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  let := CommShift.ofIso G.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  let := CommShift.ofIso FG.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  have : NatTrans.CommShift F.leftDerivedFunctorIsoMapDerivedCategory.symm.hom ℤ :=
    CommShift.ofIso_compatibility F.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  have : NatTrans.CommShift F.leftDerivedFunctorIsoMapDerivedCategory.hom ℤ :=
    NatTrans.CommShift.of_iso_inv F.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  have : NatTrans.CommShift G.leftDerivedFunctorIsoMapDerivedCategory.symm.hom ℤ :=
    CommShift.ofIso_compatibility G.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  have : NatTrans.CommShift G.leftDerivedFunctorIsoMapDerivedCategory.hom ℤ :=
    NatTrans.CommShift.of_iso_inv G.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  have : NatTrans.CommShift FG.leftDerivedFunctorIsoMapDerivedCategory.inv ℤ :=
    CommShift.ofIso_compatibility FG.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  rw [leftComp_transport]
  dsimp only [transportComp, derivedComp, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom]
  infer_instance
end LeftTransport
end CategoryTheory.Functor
