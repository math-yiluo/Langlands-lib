/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.CategoryTheory.Localization.Opposite

/-! # Descent of a chain comparison through K-injective representatives

Source: Stacks Project, Tags 0A95 and 08J7. Localization of the category of K-injective
complexes gives the comparison and its equation on every representative, simultaneously.
(blueprint: lem-sf-kinjective-hom-comparison-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe b vb wb a va wa

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {B : Type b} [Category.{vb} B] [Abelian B] [HasDerivedCategory.{wb} B]
  [Abelian.HasKInjectiveResolutions B]
  {A : Type a} [Category.{va} A] [Abelian A] [HasDerivedCategory.{wa} A]
  (U : B ⥤ A) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [U.PreservesKInjectiveComplexes]
  (HB : (CochainComplex B ℤ)ᵒᵖ × CochainComplex B ℤ ⥤ CochainComplex B ℤ)
  (HA : (CochainComplex A ℤ)ᵒᵖ × CochainComplex A ℤ ⥤ CochainComplex A ℤ)
  (DB : (DerivedCategory B)ᵒᵖ × DerivedCategory B ⥤ DerivedCategory B)
  (DA : (DerivedCategory A)ᵒᵖ × DerivedCategory A ⥤ DerivedCategory A)
  (ρB : ∀ (K I : CochainComplex B ℤ) [I.IsKInjective],
    DB.obj (op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (HB.obj (op K, I)))
  (ρA : ∀ (K I : CochainComplex A ℤ) [I.IsKInjective],
    DA.obj (op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (HA.obj (op K, I)))
  (nB : ∀ (K K' I I' : CochainComplex B ℤ) [I.IsKInjective] [I'.IsKInjective]
    (f : K' ⟶ K) (g : I ⟶ I'),
    DB.map ((DerivedCategory.Q.map f).op, DerivedCategory.Q.map g) ≫ (ρB K' I').hom =
      (ρB K I).hom ≫ DerivedCategory.Q.map (HB.map (f.op, g)))
  (nA : ∀ (K K' I I' : CochainComplex A ℤ) [I.IsKInjective] [I'.IsKInjective]
    (f : K' ⟶ K) (g : I ⟶ I'),
    DA.map ((DerivedCategory.Q.map f).op, DerivedCategory.Q.map g) ≫ (ρA K' I').hom =
      (ρA K I).hom ≫ DerivedCategory.Q.map (HA.map (f.op, g)))
  (chain : HB ⋙ U.mapHomologicalComplex (.up ℤ) ≅
    ((U.mapHomologicalComplex (.up ℤ)).op.prod (U.mapHomologicalComplex (.up ℤ))) ⋙ HA)

include nB nA

/-- A natural chain comparison descends, with its exact representative equation.
Source: Stacks Project, Tags 0A95 and 08J7; step 5 of the ringed-forgetting argument
(blueprint: lem-sf-kinjective-hom-comparison-descent).
Proof: restrict both variables to K-injective complexes. The representative isomorphisms,
the localization factor for U, and the chain comparison give a natural isomorphism after
precomposition with Qᵒᵖ × Q on that subcategory. The restricted Q is a localization at
quasi-isomorphisms, so its opposite product is also a localization. Precomposition with it
is fully faithful on functor categories. Lift the natural isomorphism through that fully
faithful functor. Its preimage equation, followed by cancellation of the two representative
isomorphisms, is exactly the displayed equality, for every pair of K-injectives. -/
theorem kInjectiveHomComparisonDescent :
    ∃ derived : DB ⋙ U.mapDerivedCategory ≅
        (U.mapDerivedCategory.op.prod U.mapDerivedCategory) ⋙ DA,
      ∀ (K I : CochainComplex B ℤ) [K.IsKInjective] [I.IsKInjective],
        derived.hom.app (op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj I) ≫
            DA.map
              (X := (op (U.mapDerivedCategory.obj (DerivedCategory.Q.obj K)),
                U.mapDerivedCategory.obj (DerivedCategory.Q.obj I)))
              (Y := (op (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj K)),
                DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj I)))
              ((U.mapDerivedCategoryFactors.inv.app K).op,
                U.mapDerivedCategoryFactors.hom.app I) ≫
            (ρA ((U.mapHomologicalComplex (.up ℤ)).obj K)
              ((U.mapHomologicalComplex (.up ℤ)).obj I)).hom =
          U.mapDerivedCategory.map (ρB K I).hom ≫
            U.mapDerivedCategoryFactors.hom.app (HB.obj (op K, I)) ≫
            DerivedCategory.Q.map (chain.hom.app (op K, I)) := by
  let V := CochainComplex.KInjectives.ι (C := B)
  let L := V ⋙ DerivedCategory.Q
  let P := L.op.prod L
  let W := (CochainComplex.KInjectives.quasiIso B).op.prod
    (CochainComplex.KInjectives.quasiIso B)
  have : L.IsLocalization (CochainComplex.KInjectives.quasiIso B) := by
    dsimp [L, V]
    infer_instance
  have : (CochainComplex.KInjectives.quasiIso B).ContainsIdentities := by
    dsimp [CochainComplex.KInjectives.quasiIso]
    infer_instance
  have : P.IsLocalization W := by
    dsimp [P, W]
    infer_instance
  let VC := V.op.prod V
  let UC := U.mapHomologicalComplex (.up ℤ)
  let QA := (DerivedCategory.Q (C := A)).op.prod (DerivedCategory.Q (C := A))
  let UB := U.mapDerivedCategory
  let F := DB ⋙ UB
  let G := (UB.op.prod UB) ⋙ DA
  let eB : P ⋙ DB ≅ VC ⋙ HB ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun X ↦ by
      have := X.2.property
      exact ρB X.1.unop.obj X.2.obj) (by
        intro X Y f
        have := X.2.property
        have := Y.2.property
        exact nB _ _ _ _ f.1.unop.hom f.2.hom)
  let eA : (VC ⋙ (UC.op.prod UC)) ⋙ QA ⋙ DA ≅
      (VC ⋙ (UC.op.prod UC)) ⋙ HA ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun X ↦ by
      have := X.2.property
      exact ρA (UC.obj X.1.unop.obj) (UC.obj X.2.obj)) (by
        intro X Y f
        have := X.2.property
        have := Y.2.property
        exact nA _ _ _ _ (UC.map f.1.unop.hom) (UC.map f.2.hom))
  let factors : P ⋙ (UB.op.prod UB) ≅ (VC ⋙ (UC.op.prod UC)) ⋙ QA :=
    Functor.isoWhiskerLeft VC
      (NatIso.prod (NatIso.op U.mapDerivedCategoryFactors.symm) U.mapDerivedCategoryFactors)
  let e : P ⋙ F ≅ P ⋙ G :=
    Functor.isoWhiskerRight eB UB ≪≫
      Functor.isoWhiskerLeft (VC ⋙ HB) U.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerLeft VC (Functor.isoWhiskerRight chain DerivedCategory.Q) ≪≫
      eA.symm ≪≫ (Functor.isoWhiskerRight factors DA).symm
  let ff := Localization.fullyFaithfulWhiskeringLeft P W (DerivedCategory A)
  let derived : F ≅ G := ff.preimageIso e
  refine ⟨derived, ?_⟩
  intro K I _ _
  have hd := congr_app (ff.map_preimage e.hom)
    (op (CochainComplex.KInjectives.mk K), CochainComplex.KInjectives.mk I)
  change derived.hom.app (op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj I) = _ at hd
  rw [hd]
  change e.hom.app (op (CochainComplex.KInjectives.mk K),
      CochainComplex.KInjectives.mk I) ≫
    (Functor.isoWhiskerRight factors DA).hom.app
      (op (CochainComplex.KInjectives.mk K), CochainComplex.KInjectives.mk I) ≫
    eA.hom.app (op (CochainComplex.KInjectives.mk K),
      CochainComplex.KInjectives.mk I) = _
  simp only [e, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]
  rfl

end CategoryTheory
