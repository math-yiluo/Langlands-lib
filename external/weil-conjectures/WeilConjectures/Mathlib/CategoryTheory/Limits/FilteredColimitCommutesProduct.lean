/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Cones

/-!
# FilteredColimitCommutesProduct

Ported from the `proetale` package
(`Proetale.Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct`).
-/

@[expose] public section

universe w

namespace CategoryTheory

variable {I J : Type*} (C D : I → Type*) [∀ i, Category* (C i)]
    [∀ i, Category* (D i)]

def Pi.eqToEquivalenceCompIso {I : Type*} (C D : I → Type*) [∀ i, Category* (C i)]
    [∀ i, Category* (D i)]
    (F : ∀ i, C i ⥤ D i) {i j : I} (h : i = j) :
    (eqToEquivalence C h).functor ⋙ F j ≅ F i ⋙ (eqToEquivalence D h).functor := by
  subst h
  exact Iso.refl _

@[reassoc (attr := simp)]
lemma Pi.eqToEquivalenceCompIso_naturality {I : Type*} (C D : I → Type*) [∀ i, Category* (C i)]
    [∀ i, Category* (D i)] (F : ∀ i, C i ⥤ D i) {i j : I} (h : j = i) (a b : C j)
    (f : a ⟶ b) :
    (F i).map ((eqToEquivalence C h).functor.map f) ≫
      (eqToEquivalenceCompIso C D F h).hom.app b =
    (eqToEquivalenceCompIso C D F h).hom.app a ≫
      (eqToEquivalence D h).functor.map ((F j).map f) :=
  (eqToEquivalenceCompIso _ _ _ h).hom.naturality _

def Functor.piCompEval {I : Type*} {C D : I → Type*} [∀ i, Category* (C i)]
    [∀ i, Category* (D i)] (F : ∀ i, C i ⥤ D i) (i : I) :
    Functor.pi F ⋙ Pi.eval _ i ≅ Pi.eval _ i ⋙ F i :=
  Iso.refl _

noncomputable def Pi.equivalenceOfEquivCompEvalIso {I J : Type*} (C : I → Type*)
    [∀ i, Category* (C i)] (e : J ≃ I) (j : J) :
    (Pi.equivalenceOfEquiv C e).functor ⋙ Pi.eval C (e j) ≅ Pi.eval _ j :=
  (Functor.pi'CompEval _ _) ≪≫
    Functor.isoWhiskerLeft _ (Pi.eqToEquivalenceFunctorIso _ _ _) ≪≫
    Pi.evalCompEqToEquivalenceFunctor (fun j ↦ C (e j)) (show e.symm (e j) = j by simp)

noncomputable def Pi.equivalenceOfEquivCompEvalIso' {I J : Type*} (C : I → Type*)
    [∀ i, Category* (C i)] (e : J ≃ I) (i : I) :
    (Pi.equivalenceOfEquiv C e).functor ⋙ Pi.eval C i ≅
      Pi.eval _ (e.symm i) ⋙ (Pi.eqToEquivalence _ <| by simp).functor :=
  Iso.refl _

@[simp]
lemma Pi.eqToEquivalence_rfl {I : Type*} (C : I → Type*) [∀ i, Category* (C i)] (i : I) :
    Pi.eqToEquivalence C (refl i) = .refl :=
  rfl

attribute [-simp] Pi.equivalenceOfEquiv_functor Pi.equivalenceOfEquiv_inverse

noncomputable
def Pi.equivalenceOfEquivCompPiIso {I J : Type*} (C D : I → Type*) [∀ i, Category* (C i)]
    [∀ i, Category* (D i)]
    (e : J ≃ I) (F : ∀ i, C i ⥤ D i) :
    (Pi.equivalenceOfEquiv C e).functor ⋙ Functor.pi F ≅
      Functor.pi (fun j ↦ F (e j)) ⋙ (Pi.equivalenceOfEquiv D e).functor :=
  NatIso.ofComponents
    (fun a ↦ isoMk fun i ↦ (Pi.eqToEquivalenceCompIso _ _ F _).app (a (e.symm i))) <| by
    intro a b f
    ext i
    simp only [Functor.comp_map, comp_apply, Functor.pi_map, isoMk_hom, Iso.app_hom]
    apply eqToEquivalenceCompIso_naturality

@[simps!]
def Functor.piCompIso {I : Type*} {C D E : I → Type*} [∀ i, Category* (C i)]
    [∀ i, Category* (D i)] [∀ i, Category* (E i)] (F : ∀ i, C i ⥤ D i) (G : ∀ i, D i ⥤ E i) :
    Functor.pi (fun i ↦ F i ⋙ G i) ≅ Functor.pi F ⋙ Functor.pi G :=
  NatIso.ofComponents (fun a ↦ Pi.isoMk fun i ↦ Iso.refl _)

namespace Limits

variable (ι : Type*) {C : Type*} [Category* C]

@[simps!]
noncomputable
def Pi.functorCompIso {D : Type*} [Category* D] (F : C ⥤ D) [PreservesLimitsOfShape (Discrete ι) F]
    [HasProductsOfShape ι C] [HasProductsOfShape ι D] :
    Pi.functor ι ⋙ F ≅ Functor.pi (fun _ ↦ F) ⋙ Pi.functor ι :=
  NatIso.ofComponents (fun a ↦ PreservesProduct.iso F a) fun {a b} f ↦ by
    apply Pi.hom_ext
    intro i
    suffices h : F.map (map f) ≫ F.map (π b i) = F.map (π a i) ≫ F.map (f i) by simpa [Functor.pi]
    rw [← F.map_comp, Pi.map_π]
    simp

variable {ι}
variable [HasProductsOfShape ι C] {J : ι → Type*} [∀ i, Category* (J i)]

lemma IsIPC.of_isIPCOfShape [HasProducts.{w} C] [HasFilteredColimitsOfSize.{w, w} C]
    (h : ∀ (ι : Type w), IsIPCOfShape.{w} ι C) :
    IsIPC.{w} C where
  isIPCOfShape ι := h ι

/- On Lean ≥ 4.32, goals mixing cocone legs with explicit product projections are only
type-correct after unfolding these definitions, which blocks `simp`/`rw` unification.
Making them locally reducible restores the pre-4.32 behavior for the proofs below. -/
set_option allowUnsafeReducibility true in
attribute [local reducible] Functor.const Functor.pi Functor.comp Pi.functor
  Functor.mapCocone Cocone.functoriality coconePointwiseProduct

lemma IsIPCOfShape.of_preservesFilteredColimitsOfSize {D : Type*} [Category* D] (F : C ⥤ D)
    {ι : Type*} [HasProductsOfShape ι D] [IsIPCOfShape.{w} ι D] [HasProductsOfShape ι C]
    [PreservesFilteredColimitsOfSize.{w, w} F] [PreservesLimitsOfShape (Discrete ι) F]
    -- TODO: this assumption is seemingly hard for typeclass search
    [∀ (J : ι → Type w) [∀ i, SmallCategory (J i)] [∀ i, IsFiltered (J i)],
      ReflectsColimitsOfShape (∀ i, J i) F] :
    IsIPCOfShape.{w} ι C where
  nonempty_isColimit J _ _ D c hc := by
    obtain ⟨h⟩ := IsIPCOfShape.nonempty_isColimit (fun i ↦ isColimitOfPreserves F (hc i))
    constructor
    apply isColimitOfReflects F
    refine IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_ h
    · exact Functor.isoWhiskerRight (Functor.piCompIso _ _) _ ≪≫
        (Functor.associator _ _ _) ≪≫
        (Functor.isoWhiskerLeft _ <| (Pi.functorCompIso _ _).symm) ≪≫
        (Functor.associator _ _ _).symm
    · refine (Cocone.ext (PreservesProduct.iso F _) fun j ↦ ?_).symm
      refine Pi.hom_ext _ _ fun i ↦ ?_
      simp only [NatTrans.comp_app, Functor.whiskerRight_app,
        Pi.constCompPiIsoConst_hom_app, Category.comp_id, PreservesProduct.iso_hom, Category.assoc,
        Cocone.precompose_obj_ι, Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
        Functor.isoWhiskerRight_inv, Functor.associator_hom_app, Functor.whiskerLeft_app,
        Pi.functorCompIso_hom_app, Functor.associator_inv_app, Category.id_comp, Pi.map_π,
        NatTrans.pi_app, Pi.map_π_assoc, Functor.piCompIso_inv_app, piComparison_comp_π_assoc]
      calc F.map (Limits.Pi.map fun i ↦ (c i).ι.app (j i)) ≫
            (piComparison F fun i ↦ (c i).pt) ≫ Pi.π (fun i ↦ F.obj ((c i).pt)) i
          = F.map (Limits.Pi.map fun i ↦ (c i).ι.app (j i)) ≫
              F.map (Pi.π (fun i ↦ (c i).pt) i) := by rw [piComparison_comp_π]
        _ = F.map ((Limits.Pi.map fun i ↦ (c i).ι.app (j i)) ≫ Pi.π (fun i ↦ (c i).pt) i) := by
              rw [Functor.map_comp]
        _ = F.map (Pi.π (fun i ↦ (D i).obj (j i)) i ≫ (c i).ι.app (j i)) := by
              rw [Limits.Pi.map_π]
        _ = F.map (Pi.π (fun i ↦ (D i).obj (j i)) i) ≫ F.map ((c i).ι.app (j i)) := by
              rw [Functor.map_comp]

lemma IsIPC.of_preservesFilteredColimitsOfSize {D : Type*} [Category* D] (F : C ⥤ D)
    [HasProducts D] [HasFilteredColimitsOfSize.{w, w} D] [IsIPC.{w} D]
    [HasProducts C] [HasFilteredColimitsOfSize.{w, w} C]
    [PreservesFilteredColimitsOfSize.{w, w} F] [PreservesLimitsOfSize.{w, w} F]
    [ReflectsFilteredColimitsOfSize.{w, w} F] :
    IsIPC.{w} C :=
  .of_isIPCOfShape fun ι ↦ by
    convert IsIPCOfShape.of_preservesFilteredColimitsOfSize.{w} F
    · infer_instance
    · infer_instance
    · intro J
      infer_instance

end Limits

end CategoryTheory
