/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.StrictRoosComparison

/-!
# Triangle and augmentation compatibility of a prescribed Roos square

Source: Stacks Project, Tags 0940 and 0941, and the final paragraph of
literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-sf-cbc/lem-cbc-completed-extension-zero-comparison.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe uC vC r uD vD s wA wB
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

section SignedCone
open HomologicalComplex
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {P : CochainComplex A ℤ} (a : P ⟶ P)

private def compatCoords (i : ℤ) :
    ((CochainComplex.mappingCone a)⟦(-1 : ℤ)⟧).X (i + 1) ≅ P.X (i + 1) ⊞ P.X i :=
  (CochainComplex.mappingCone a).shiftFunctorObjXIso (-1) (i + 1) i
      (add_neg_cancel_right i 1).symm ≪≫
    homotopyCofiber.XIsoBiprod a i (i + 1) rfl ≪≫
    (⟨biprod.map (𝟙 _) (-𝟙 _), biprod.map (𝟙 _) (-𝟙 _),
      by ext <;> simp, by ext <;> simp⟩)

private def compatProjection : (CochainComplex.mappingCone a)⟦(-1 : ℤ)⟧ ⟶ P :=
  -CochainComplex.HomComplex.Cocycle.homOf
    ((CochainComplex.mappingCone.fst a).leftShift (-1) 0 (by omega))

private theorem compatProjection_f (i : ℤ) :
    (compatProjection a).f (i + 1) = (compatCoords a i).hom ≫ biprod.fst := by
  change -(((CochainComplex.mappingCone.fst a).1.leftShift (-1) 0 (by omega)).v
    (i + 1) (i + 1) (by omega)) = _
  rw [CochainComplex.HomComplex.Cochain.leftShift_v
    (CochainComplex.mappingCone.fst a).1 (-1) 0 (by omega)
      (i + 1) (i + 1) (by omega) i (by omega)]
  simp [compatCoords, CochainComplex.mappingCone.fst, Category.assoc,
    CochainComplex.HomComplex.Cochain.mk_v, homotopyCofiber.fstX]

private def compatBoundary : P ⟶ ((CochainComplex.mappingCone a)⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧ :=
  CochainComplex.mappingCone.inr a ≫
    (shiftFunctorZero _ ℤ).inv.app _ ≫ (shiftFunctorAdd' _ (-1 : ℤ) 1 0 (by omega)).hom.app _

private theorem compatBoundary_f (i : ℤ) :
    (compatBoundary a).f i ≫
      (((CochainComplex.mappingCone a)⟦(-1 : ℤ)⟧).shiftFunctorObjXIso 1 i (i + 1) rfl).hom ≫
      (compatCoords a i).hom = -biprod.inr := by
  simp only [compatBoundary, compatCoords, CochainComplex.shiftFunctorObjXIso,
    CochainComplex.shiftFunctorAdd'_hom_app_f',
    CochainComplex.shiftFunctorZero_inv_app_f, Iso.trans_hom, HomologicalComplex.comp_f,
    Category.assoc]
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
  change (CochainComplex.mappingCone.inr a).f i ≫
    ((CochainComplex.mappingCone a).XIsoOfEq (by omega : i = i + 0)).hom ≫
    ((CochainComplex.mappingCone a).XIsoOfEq (by omega : i + 0 = i + 1 + -1)).hom ≫
    𝟙 _ ≫
    ((CochainComplex.mappingCone a).XIsoOfEq (by omega : i + 1 + -1 = i)).hom ≫
    (homotopyCofiber.XIsoBiprod a i (i + 1) rfl).hom ≫
    biprod.map (𝟙 _) (-𝟙 _) = -biprod.inr
  simp only [Category.id_comp, ← Category.assoc,
    HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
  simp [CochainComplex.mappingCone.inr]

private theorem cofiber_snd {T : CochainComplex A ℤ} (a : T ⟶ T)
    (p j : ℤ) (hpj : (ComplexShape.up ℤ).Rel p j) :
    (homotopyCofiber.XIsoBiprod a p j hpj).hom ≫ biprod.snd =
      homotopyCofiber.sndX a p := by
  obtain rfl := (ComplexShape.up ℤ).next_eq' hpj
  simp only [homotopyCofiber.sndX, dite_eq_left hpj]

private theorem compatCoords_snd (i : ℤ) :
    (compatCoords a i).hom ≫ biprod.snd =
      -(CochainComplex.mappingCocone.snd a).v (i + 1) i (by omega) := by
  rw [CochainComplex.mappingCocone.snd,
    CochainComplex.HomComplex.Cochain.leftShift_v
      (CochainComplex.mappingCone.snd a) (-1) (-1) (by omega)
      (i + 1) i (by omega) i (by omega)]
  simp [compatCoords, CochainComplex.mappingCone.snd,
    Category.assoc, cofiber_snd, Int.negOnePow_even 2 ⟨1, rfl⟩]

private def compatAugment {V : CochainComplex A ℤ} (f : V ⟶ P) (hf : f ≫ a = 0) :
    V ⟶ (CochainComplex.mappingCone a)⟦(-1 : ℤ)⟧ :=
  CochainComplex.mappingCocone.lift a f 0 (by simp [hf])

private theorem compatAugment_f {V : CochainComplex A ℤ} (f : V ⟶ P)
    (hf : f ≫ a = 0) (i : ℤ) :
    (compatAugment a f hf).f (i + 1) ≫ (compatCoords a i).hom =
      biprod.lift (f.f (i + 1)) 0 := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.lift_fst, ← compatProjection_f]
    exact CochainComplex.mappingCocone.lift_f_fst_f a f 0 (by simp [hf]) (i + 1)
  · simp only [Category.assoc, biprod.lift_snd, compatCoords_snd,
      Preadditive.comp_neg]
    rw [show (compatAugment a f hf).f (i + 1) ≫
      (CochainComplex.mappingCocone.snd a).v (i + 1) i (by omega) = 0 from
        CochainComplex.mappingCocone.lift_f_snd_v a f 0 (by simp [hf]) _ _ (by omega)]
    simp

private theorem compatMaps (U : CochainComplex A ℤ)
    (hU : U = (CochainComplex.mappingCone a)⟦(-1 : ℤ)⟧)
    (χ : ∀ i : ℤ, U.X (i + 1) ≅ P.X (i + 1) ⊞ P.X i)
    (hc : ∀ i, (χ i).hom =
      (eqToIso (congrArg (fun V : CochainComplex A ℤ ↦ V.X (i + 1)) hU)).hom ≫
        (compatCoords a i).hom) :
    ∃ (p : U ⟶ P) (δ : P ⟶ U⟦(1 : ℤ)⟧),
      (∀ i, p.f (i + 1) = (χ i).hom ≫ biprod.fst) ∧
      (∀ i, δ.f i ≫ (U.shiftFunctorObjXIso 1 i (i + 1) rfl).hom ≫
        (χ i).hom = -biprod.inr) := by
  subst U
  have hχ : χ = compatCoords a := by
    funext i
    apply Iso.ext
    simpa using hc i
  subst χ
  exact ⟨compatProjection a, compatBoundary a, compatProjection_f a, compatBoundary_f a⟩

private theorem compatAugmentMaps (U : CochainComplex A ℤ)
    (hU : U = (CochainComplex.mappingCone a)⟦(-1 : ℤ)⟧)
    (χ : ∀ i : ℤ, U.X (i + 1) ≅ P.X (i + 1) ⊞ P.X i)
    (hc : ∀ i, (χ i).hom =
      (eqToIso (congrArg (fun V : CochainComplex A ℤ ↦ V.X (i + 1)) hU)).hom ≫
        (compatCoords a i).hom)
    {V : CochainComplex A ℤ} (f : V ⟶ P) (hf : f ≫ a = 0) :
    ∃ b : V ⟶ U, ∀ i, b.f (i + 1) ≫ (χ i).hom = biprod.lift (f.f (i + 1)) 0 := by
  subst U
  have hχ : χ = compatCoords a := by
    funext i
    apply Iso.ext
    simpa using hc i
  subst χ
  exact ⟨compatAugment a f hf, compatAugment_f a f hf⟩

private theorem product_component_ext [HasCountableProducts A]
    (T : ℕ → CochainComplex A ℤ) {V : A} (i : ℤ)
    (f g : V ⟶ (∏ᶜ T).X i)
    (h : ∀ n, f ≫ (Pi.π T n).f i = g ≫ (Pi.π T n).f i) : f = g := by
  apply (cancel_mono (piComparison (HomologicalComplex.eval A (ComplexShape.up ℤ) i) T)).mp
  apply Pi.hom_ext
  intro n
  simpa only [Category.assoc, piComparison_comp_π, HomologicalComplex.eval_map] using h n

end SignedCone

-- Check the coordinate calculations over abstract abelian categories, before
-- specializing to module sheaves and their products.
section SignedConeMap

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive]
    {P U : CochainComplex A ℤ} {P' U' : CochainComplex B ℤ}
    (χ : ∀ i : ℤ, U.X (i + 1) ≅ P.X (i + 1) ⊞ P.X i)
    (χ' : ∀ i : ℤ, U'.X (i + 1) ≅ P'.X (i + 1) ⊞ P'.X i)
    (k : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj U ⟶ U')
    (ψ : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶ P')

private theorem compatBoundary_map
    (hd : ∀ i,
      (k.f (i + 1) ≫ (χ' i).hom ≫ biprod.fst =
        F.map ((χ i).hom ≫ biprod.fst) ≫ ψ.f (i + 1)) ∧
      (k.f (i + 1) ≫ (χ' i).hom ≫ biprod.snd =
        F.map ((χ i).hom ≫ biprod.snd) ≫ ψ.f i))
    (δ : P ⟶ U⟦(1 : ℤ)⟧) (δ' : P' ⟶ U'⟦(1 : ℤ)⟧)
    (hδ : ∀ i, δ.f i ≫ (U.shiftFunctorObjXIso 1 i (i + 1) rfl).hom ≫
      (χ i).hom = -biprod.inr)
    (hδ' : ∀ i, δ'.f i ≫ (U'.shiftFunctorObjXIso 1 i (i + 1) rfl).hom ≫
      (χ' i).hom = -biprod.inr) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map δ ≫
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app U ≫
        k⟦(1 : ℤ)⟧' = ψ ≫ δ' := by
  apply HomologicalComplex.Hom.ext
  funext i
  have hda : δ.f i ≫ (χ i).hom = -biprod.inr := by
    simpa [CochainComplex.shiftFunctorObjXIso] using hδ i
  have hdb : δ'.f i ≫ (χ' i).hom = -biprod.inr := by
    simpa [CochainComplex.shiftFunctorObjXIso] using hδ' i
  change F.map (δ.f i) ≫ 𝟙 _ ≫ k.f (i + 1) = ψ.f i ≫ δ'.f i
  rw [Category.id_comp]
  apply (cancel_mono (χ' i).hom).mp
  apply biprod.hom_ext
  · simp only [Category.assoc, (hd i).1]
    rw [← Category.assoc, ← F.map_comp]
    simp only [← Category.assoc, hda, hdb]
    simp only [Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc,
      Functor.map_neg]
    rw [biprod.inr_fst, biprod.inr_fst]
    simp only [Functor.map_zero, zero_comp, comp_zero, neg_zero]
  · simp only [Category.assoc, (hd i).2]
    rw [← Category.assoc, ← F.map_comp]
    simp only [← Category.assoc, hda, hdb]
    simp only [Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc,
      Functor.map_neg]
    rw [biprod.inr_snd, biprod.inr_snd]
    simp only [Functor.map_id, Category.id_comp, Category.comp_id]

private theorem compatAugment_map
    (hd : ∀ i,
      (k.f (i + 1) ≫ (χ' i).hom ≫ biprod.fst =
        F.map ((χ i).hom ≫ biprod.fst) ≫ ψ.f (i + 1)) ∧
      (k.f (i + 1) ≫ (χ' i).hom ≫ biprod.snd =
        F.map ((χ i).hom ≫ biprod.snd) ≫ ψ.f i))
    {V : CochainComplex A ℤ} (f : V ⟶ P)
    (f' : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj V ⟶ P')
    (b : V ⟶ U) (b' : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj V ⟶ U')
    (hb : ∀ i, b.f (i + 1) ≫ (χ i).hom = biprod.lift (f.f (i + 1)) 0)
    (hb' : ∀ i, b'.f (i + 1) ≫ (χ' i).hom = biprod.lift (f'.f (i + 1)) 0)
    (hf : (F.mapHomologicalComplex (ComplexShape.up ℤ)).map f ≫ ψ = f') :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map b ≫ k = b' := by
  apply HomologicalComplex.Hom.ext
  funext i
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, i = j + 1 := ⟨i - 1, by omega⟩
  change F.map (b.f (j + 1)) ≫ k.f (j + 1) = b'.f (j + 1)
  apply (cancel_mono (χ' j).hom).mp
  apply biprod.hom_ext
  · simp only [Category.assoc, (hd j).1]
    rw [← Category.assoc, ← F.map_comp]
    rw [← Category.assoc, hb]
    rw [← Category.assoc, hb']
    rw [biprod.lift_fst, biprod.lift_fst]
    exact congrArg (fun g ↦ g.f (j + 1)) hf
  · simp only [Category.assoc, (hd j).2]
    rw [← Category.assoc, ← F.map_comp]
    rw [← Category.assoc, hb]
    rw [← Category.assoc, hb']
    rw [biprod.lift_snd, biprod.lift_snd]
    simp only [Functor.map_zero, zero_comp]

end SignedConeMap

private theorem localizedBoundary
    {E E' A B : Type*} [Category* E] [Category* E'] [Category* A] [Category* B]
    [HasShift E ℤ] [HasShift E' ℤ] [HasShift A ℤ] [HasShift B ℤ]
    (Q : E ⥤ A) (Q' : E' ⥤ B) (Fc : E ⥤ E') (FD : A ⥤ B)
    [Q.CommShift ℤ] [Q'.CommShift ℤ] [Fc.CommShift ℤ] [FD.CommShift ℤ]
    (c : Q ⋙ FD ≅ Fc ⋙ Q') [NatTrans.CommShift c.hom ℤ]
    {P U : E} {P' V : E'} {L : A}
    (eA : L ≅ Q.obj U) {N : B} (eB : N ≅ Q'.obj V)
    (l : FD.obj L ⟶ N) (k : Fc.obj U ⟶ V) (ψ : Fc.obj P ⟶ P')
    (δ : P ⟶ U⟦(1 : ℤ)⟧) (δ' : P' ⟶ V⟦(1 : ℤ)⟧)
    (hsq : FD.map eA.hom ≫ c.hom.app U ≫ Q'.map k = l ≫ eB.hom)
    (hb : Fc.map δ ≫ (Fc.commShiftIso (1 : ℤ)).hom.app U ≫ k⟦(1 : ℤ)⟧' = ψ ≫ δ') :
    FD.map (Q.map δ ≫ (Q.commShiftIso (1 : ℤ)).hom.app U ≫ eA.inv⟦(1 : ℤ)⟧') ≫
        (FD.commShiftIso (1 : ℤ)).hom.app L ≫ l⟦(1 : ℤ)⟧' =
      c.hom.app P ≫ Q'.map ψ ≫ Q'.map δ' ≫
        (Q'.commShiftIso (1 : ℤ)).hom.app V ≫ eB.inv⟦(1 : ℤ)⟧' := by
  have hl : FD.map eA.inv ≫ l ≫ eB.hom = c.hom.app U ≫ Q'.map k := by
    simpa only [Category.assoc, ← FD.map_comp_assoc, Iso.inv_hom_id, FD.map_id,
      Category.id_comp] using congrArg (fun f ↦ FD.map eA.inv ≫ f) hsq.symm
  have hcore :
      FD.map (Q.map δ ≫ (Q.commShiftIso (1 : ℤ)).hom.app U) ≫
          (FD.commShiftIso (1 : ℤ)).hom.app (Q.obj U) ≫
          (c.hom.app U ≫ Q'.map k)⟦(1 : ℤ)⟧' =
        c.hom.app P ≫ Q'.map ψ ≫ Q'.map δ' ≫
          (Q'.commShiftIso (1 : ℤ)).hom.app V := by
    calc
      _ = FD.map (Q.map δ) ≫ ((Q ⋙ FD).commShiftIso (1 : ℤ)).hom.app U ≫
          (c.hom.app U)⟦(1 : ℤ)⟧' ≫ (Q'.map k)⟦(1 : ℤ)⟧' := by
        simp only [Functor.commShiftIso_comp_hom_app, Functor.map_comp, Category.assoc]
      _ = FD.map (Q.map δ) ≫ c.hom.app (U⟦(1 : ℤ)⟧) ≫
          ((Fc ⋙ Q').commShiftIso (1 : ℤ)).hom.app U ≫
          (Q'.map k)⟦(1 : ℤ)⟧' := by rw [NatTrans.shift_app_comm_assoc]
      _ = c.hom.app P ≫ Q'.map (Fc.map δ) ≫
          Q'.map ((Fc.commShiftIso (1 : ℤ)).hom.app U) ≫
          (Q'.commShiftIso (1 : ℤ)).hom.app (Fc.obj U) ≫
          (Q'.map k)⟦(1 : ℤ)⟧' := by
        have hn := c.hom.naturality δ
        change FD.map (Q.map δ) ≫ c.hom.app _ = c.hom.app _ ≫ Q'.map (Fc.map δ) at hn
        rw [← Category.assoc, hn]
        simp only [Functor.commShiftIso_comp_hom_app, Category.assoc]
      _ = c.hom.app P ≫
          Q'.map (Fc.map δ ≫ (Fc.commShiftIso (1 : ℤ)).hom.app U ≫ k⟦(1 : ℤ)⟧') ≫
          (Q'.commShiftIso (1 : ℤ)).hom.app V := by
        rw [← Q'.commShiftIso_hom_naturality k]
        simp only [Functor.map_comp, Category.assoc]
      _ = _ := by rw [hb]; simp only [Functor.map_comp, Category.assoc]
  apply (cancel_mono (eB.hom⟦(1 : ℤ)⟧')).mp
  simp only [Category.assoc, ← (shiftFunctor B (1 : ℤ)).map_comp,
    Iso.inv_hom_id, Functor.map_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [FD.commShiftIso_hom_naturality_assoc]
  simp only [← (shiftFunctor B (1 : ℤ)).map_comp, ← Category.assoc] at *
  rw [hl]
  convert! hcore using 1 <;>
    simp only [Functor.map_comp, Category.assoc]
  exact congrArg (fun z ↦ c.hom.app P ≫ Q'.map ψ ≫ Q'.map δ' ≫ z)
    (Category.comp_id ((Q'.commShiftIso (1 : ℤ)).hom.app V))

private theorem localizedAugmentation
    {E E' A B : Type*} [Category E] [Category E'] [Category A] [Category B]
    (Q : E ⥤ A) (Q' : E' ⥤ B) (Fc : E ⥤ E') (FD : A ⥤ B)
    (c : Q ⋙ FD ≅ Fc ⋙ Q') {U : E} {V : E'} {L : A} {N : B}
    (eA : L ≅ Q.obj U) (eB : N ≅ Q'.obj V)
    (l : FD.obj L ⟶ N) (k : Fc.obj U ⟶ V)
    (hsq : FD.map eA.hom ≫ c.hom.app U ≫ Q'.map k = l ≫ eB.hom)
    {T : E} (b : T ⟶ U) (b' : Fc.obj T ⟶ V) (hb : Fc.map b ≫ k = b') :
    FD.map (Q.map b ≫ eA.inv) ≫ l = c.hom.app T ≫ Q'.map b' ≫ eB.inv := by
  apply (cancel_mono eB.hom).mp
  calc
    _ = FD.map (Q.map b) ≫ c.hom.app U ≫ Q'.map k := by
      rw [FD.map_comp, Category.assoc, Category.assoc, ← hsq]
      simp only [← FD.map_comp_assoc, Iso.inv_hom_id, FD.map_id, Category.id_comp]
    _ = _ := by
      have hn := c.hom.naturality b
      change FD.map (Q.map b) ≫ c.hom.app U =
        c.hom.app T ≫ Q'.map (Fc.map b) at hn
      rw [← Category.assoc, hn, Category.assoc, ← Q'.map_comp, hb]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Triangle and augmentation compatibility of a prescribed Roos square.

Source: Stacks Project, Tags 0940 and 0941, and the final paragraph of
literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-sf-cbc/lem-cbc-completed-extension-zero-comparison.proof.md.
(auxiliary; not a blueprint node).

Proof in words:
In the signed shifted-cone coordinates construct p as first projection and
delta as minus the second inclusion followed by the canonical shift. These are
chain maps: the differential matrix is (dx,(1-s)x-dy). The two diagonal entries
of kappa give kappa p' = F(p) psi and the corresponding shifted identity for
delta, with F's canonical shift comparison. Apply Q and the commutative-shift
identity for the exact-functor localization comparison; substitute the given
Roos square and cancel the theta isomorphisms. This gives both derived triangle
identities. For a compatible family gamma, the equality (1-s)gamma=0 constructs
the chain map b=(gamma,0); construct b' in the same way from F gamma.
The coordinate identities give F(b) kappa=b'. Applying Q, the same square,
and naturality of the localization comparison proves the augmentation equation.
This calculation needs no choice of resolutions or normalization of theta. -/
theorem exactProductFunctorRoosCompatibility
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (R : Sheaf J RingCat.{max uC vC r})
    {D : Type uD} [Category.{vD} D] (K : GrothendieckTopology D)
    [HasSheafify K AddCommGrpCat.{max uD vD s}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max uD vD s}]
    (S : Sheaf K RingCat.{max uD vD s})
    (_hR : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (_hS : ∀ (U : Dᵒᵖ) (a b : S.obj.obj U), a * b = b * a)
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max uC vC r} R)]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max uD vD s} S)]
    [HasDerivedCategory.{wA} (ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{wB} (ringedSiteModules.{max uD vD s} S)]
    [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S)]
    (F : ringedSiteModules.{max uC vC r} R ⥤ ringedSiteModules.{max uD vD s} S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (_hphi : ∀ (M : ℕ → ringedSiteModules.{max uC vC r} R), IsIso (piComparison F M))
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ⥤ DerivedCategory.{wA}
      (ringedSiteModules.{max uC vC r} R))
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) ⥤ DerivedCategory.{wB}
      (ringedSiteModules.{max uD vD s} S))
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max uC vC r} R) ℤ) ⥤ CochainComplex
        (ringedSiteModules.{max uC vC r} R) ℤ) ⋙ DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙
        LA)
    (_hLA : LA.IsRightDerivedFunctor etaA
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) (ComplexShape.up ℤ)))
    (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max uD vD s} S) ℤ) ⥤ CochainComplex
        (ringedSiteModules.{max uD vD s} S) ℤ) ⋙ DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙
        LB)
    (_hLB : LB.IsRightDerivedFunctor etaB
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) (ComplexShape.up ℤ)))
    (HA : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ ⥤ CochainComplex
      (ringedSiteModules.{max uC vC r} R) ℤ) (HB : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uD
      vD s} S) ℤ ⥤ CochainComplex (ringedSiteModules.{max uD vD s} S) ℤ)
      (hAobj : ∀ X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ, HA.obj X =
        (CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦ (X).asFunctor.obj
        (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ n)).op)))⟦(-1 : ℤ)⟧)
      (hBobj : ∀ X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) ℤ, HB.obj X =
        (CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦ (X).asFunctor.obj
        (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ n)).op)))⟦(-1 : ℤ)⟧)
      (chiA : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (p : ℤ), (HA.obj
        X).X (p + 1) ≅ (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n))).X (p + 1) ⊞ (∏ᶜ (fun n : ℕ ↦
        (X).asFunctor.obj (op n))).X p)
      (chiB : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) ℤ) (p : ℤ), (HB.obj
        X).X (p + 1) ≅ (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n))).X (p + 1) ⊞ (∏ᶜ (fun n : ℕ ↦
        (X).asFunctor.obj (op n))).X p)
      (thetaA : DerivedCategory.Q.{wA} ⋙ LA ≅ HA ⋙ DerivedCategory.Q.{wA})
      (thetaB : DerivedCategory.Q.{wB} ⋙ LB ≅ HB ⋙ DerivedCategory.Q.{wB})
      (psi : ∀ X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op
        n))) ≅ (∏ᶜ (fun n : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj X).asFunctor.obj (op n))))
      (kappa : ∀ X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (HA.obj X) ≅ HB.obj
        ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        X))
      (lambda : LA ⋙ F.mapDerivedCategory ≅ (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun
        _ _ _ ↦ inferInstance⟩)) ⋙ LB)
    (hcoord :
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (p : ℤ), (chiA X p).hom =
        (eqToIso (congrArg (fun V : CochainComplex (ringedSiteModules.{max uC vC r} R) ℤ ↦ V.X (p +
          1)) (hAobj X))).hom ≫
        ((CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦
          (X).asFunctor.obj (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ
          n)).op))).shiftFunctorObjXIso (-1) (p + 1) p (add_neg_cancel_right p 1).symm).hom ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (towerTransitionEndomorphism (K := fun n : ℕ
          ↦ (X).asFunctor.obj (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ n)).op))
          p (p + 1) rfl).hom ≫
        biprod.map (𝟙 _) (-𝟙 _)) ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) ℤ) (p : ℤ), (chiB X p).hom =
        (eqToIso (congrArg (fun V : CochainComplex (ringedSiteModules.{max uD vD s} S) ℤ ↦ V.X (p +
          1)) (hBobj X))).hom ≫
        ((CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦
          (X).asFunctor.obj (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ
          n)).op))).shiftFunctorObjXIso (-1) (p + 1) p (add_neg_cancel_right p 1).symm).hom ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (towerTransitionEndomorphism (K := fun n : ℕ
          ↦ (X).asFunctor.obj (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ n)).op))
          p (p + 1) rfl).hom ≫
        biprod.map (𝟙 _) (-𝟙 _)))
    (hpsi :
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (n : ℕ), (psi X).hom ≫
        Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj X).asFunctor.obj (op k)) n =
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k))
          n)))
    (hkappa :
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (p : ℤ) (n : ℕ),
        (kappa X).hom.f (p + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) p).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X).asFunctor.obj (op k)) n).f (p + 1) =
          F.map ((chiA X p).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f (p + 1)) ∧
        (kappa X).hom.f (p + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) p).hom ≫ biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X).asFunctor.obj (op k)) n).f p =
          F.map ((chiA X p).hom ≫ biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f p)))
    (hsquare :
      (∀ X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ,
        (F.mapDerivedCategory).map (thetaA.hom.app X) ≫ F.mapDerivedCategoryFactors.hom.app (HA.obj
          X) ≫
            DerivedCategory.Q.{wB}.map (kappa X).hom =
          lambda.hom.app (DerivedCategory.Q.{wA}.obj X) ≫
            LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
              ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦
              inferInstance⟩)).hom.app X) ≫
            thetaB.hom.app ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X))) :
      (∀ X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ,
        ∃ (p : HA.obj X ⟶ (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n)))) (p' : HB.obj
          ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          X) ⟶ (∏ᶜ (fun n : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj X).asFunctor.obj (op n))))
          (delta : (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n))) ⟶ (HA.obj X)⟦(1 : ℤ)⟧)
          (delta' : (∏ᶜ (fun n : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
            F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X).asFunctor.obj (op n))) ⟶ (HB.obj
            ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up
            ℤ)).obj X))⟦(1 : ℤ)⟧),
          (∀ i : ℤ, p.f (i + 1) = (chiA X i).hom ≫ biprod.fst) ∧
          (∀ i : ℤ, p'.f (i + 1) = (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
            F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) i).hom ≫ biprod.fst) ∧
          (∀ i : ℤ, delta.f i ≫ ((HA.obj X).shiftFunctorObjXIso 1 i (i + 1) rfl).hom ≫
            (chiA X i).hom = -biprod.inr) ∧
          (∀ i : ℤ, delta'.f i ≫ ((HB.obj ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
            F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X)).shiftFunctorObjXIso 1 i (i + 1)
            rfl).hom ≫
            (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up
              ℤ)).obj X) i).hom = -biprod.inr) ∧
          lambda.hom.app (DerivedCategory.Q.{wA}.obj X) ≫
              LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
                ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦
                inferInstance⟩)).hom.app X) ≫
              thetaB.hom.app ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj X) ≫ DerivedCategory.Q.{wB}.map p' =
            (F.mapDerivedCategory).map (thetaA.hom.app X ≫ DerivedCategory.Q.{wA}.map p) ≫
              F.mapDerivedCategoryFactors.hom.app (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n))) ≫
                DerivedCategory.Q.{wB}.map (psi X).hom ∧
          (F.mapDerivedCategory).map (DerivedCategory.Q.{wA}.map delta ≫
            (DerivedCategory.Q.{wA}.commShiftIso (1 : ℤ)).hom.app (HA.obj X) ≫
              (thetaA.inv.app X)⟦(1 : ℤ)⟧') ≫
              (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app (LA.obj
                (DerivedCategory.Q.{wA}.obj X)) ≫
              (lambda.hom.app (DerivedCategory.Q.{wA}.obj X))⟦(1 : ℤ)⟧' ≫
              (LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
                ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦
                inferInstance⟩)).hom.app X))⟦(1 : ℤ)⟧' =
            F.mapDerivedCategoryFactors.hom.app (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n))) ≫
              DerivedCategory.Q.{wB}.map (psi X).hom ≫
              DerivedCategory.Q.{wB}.map delta' ≫ (DerivedCategory.Q.{wB}.commShiftIso (1 :
                ℤ)).hom.app (HB.obj ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
                F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X)) ≫
              (thetaB.inv.app ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj X))⟦(1 : ℤ)⟧') ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (Q : CochainComplex
        (ringedSiteModules.{max uC vC r} R) ℤ) (gamma : ∀ n : ℕ, Q ⟶ X.asFunctor.obj (op n))
        (_hgamma : ∀ n : ℕ, gamma (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = gamma n),
        ∃ (b : Q ⟶ HA.obj X) (b' : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q ⟶ HB.obj
          ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          X)),
          (∀ i : ℤ, b.f (i + 1) ≫ (chiA X i).hom = biprod.lift ((Pi.lift gamma).f (i + 1)) 0) ∧
          (∀ i : ℤ, b'.f (i + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
            F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) i).hom =
            biprod.lift ((Pi.lift (fun n : ℕ ↦ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
              (gamma n))).f (i + 1)) 0) ∧
          (F.mapDerivedCategory).map (DerivedCategory.Q.{wA}.map b ≫ thetaA.inv.app X) ≫
              lambda.hom.app (DerivedCategory.Q.{wA}.obj X) ≫
              LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
                ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦
                inferInstance⟩)).hom.app X) =
            F.mapDerivedCategoryFactors.hom.app Q ≫ DerivedCategory.Q.{wB}.map b' ≫ thetaB.inv.app
              ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up
              ℤ)).obj X))  := by
  have : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let Fc := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let Ft := ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let P := fun X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ ↦
    fun n : ℕ ↦ X.asFunctor.obj (op n)
  let PB := fun X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) ℤ ↦
    fun n : ℕ ↦ X.asFunctor.obj (op n)
  let a := fun X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ ↦
    towerTransitionEndomorphism (K := P X)
      (fun n ↦ X.asFunctor.map (homOfLE (Nat.le_succ n)).op)
  let ab := fun X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) ℤ ↦
    towerTransitionEndomorphism (K := PB X)
      (fun n ↦ X.asFunctor.map (homOfLE (Nat.le_succ n)).op)
  have hcA X i : (chiA X i).hom =
      (eqToIso (congrArg (fun V ↦ V.X (i + 1)) (hAobj X))).hom ≫
        (compatCoords (a X) i).hom := hcoord.1 X i
  have hcB X i : (chiB X i).hom =
      (eqToIso (congrArg (fun V ↦ V.X (i + 1)) (hBobj X))).hom ≫
        (compatCoords (ab X) i).hom := hcoord.2 X i
  have hd X i :
      ((kappa X).hom.f (i + 1) ≫ (chiB (Ft.obj X) i).hom ≫ biprod.fst =
        F.map ((chiA X i).hom ≫ biprod.fst) ≫ (psi X).hom.f (i + 1)) ∧
      ((kappa X).hom.f (i + 1) ≫ (chiB (Ft.obj X) i).hom ≫ biprod.snd =
        F.map ((chiA X i).hom ≫ biprod.snd) ≫ (psi X).hom.f i) := by
    constructor
    · apply product_component_ext (PB (Ft.obj X)) (i + 1)
      intro n
      have hh := congrArg (fun f ↦ f.f (i + 1)) (hpsi X n)
      simp only [HomologicalComplex.comp_f] at hh
      calc
        _ = F.map ((chiA X i).hom ≫ biprod.fst ≫
            (Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n).f (i + 1)) :=
          (hkappa X i n).1
        _ = _ := (F.map_comp ((chiA X i).hom ≫ biprod.fst) _).trans
          (congrArg (fun z ↦ F.map ((chiA X i).hom ≫ biprod.fst) ≫ z) hh.symm)
    · apply product_component_ext (PB (Ft.obj X)) i
      intro n
      have hh := congrArg (fun f ↦ f.f i) (hpsi X n)
      simp only [HomologicalComplex.comp_f] at hh
      calc
        _ = F.map ((chiA X i).hom ≫ biprod.snd ≫
            (Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n).f i) :=
          (hkappa X i n).2
        _ = _ := (F.map_comp ((chiA X i).hom ≫ biprod.snd) _).trans
          (congrArg (fun z ↦ F.map ((chiA X i).hom ≫ biprod.snd) ≫ z) hh.symm)
  constructor
  · intro X
    obtain ⟨p, δ, hp, hδ⟩ := compatMaps (a X) (HA.obj X) (hAobj X) (chiA X) (hcA X)
    obtain ⟨p', δ', hp', hδ'⟩ :=
      compatMaps (ab (Ft.obj X)) (HB.obj (Ft.obj X)) (hBobj (Ft.obj X))
        (chiB (Ft.obj X)) (hcB (Ft.obj X))
    have hproj : (kappa X).hom ≫ p' = Fc.map p ≫ (psi X).hom := by
      apply HomologicalComplex.Hom.ext
      funext i
      obtain ⟨j, rfl⟩ : ∃ j : ℤ, i = j + 1 := ⟨i - 1, by omega⟩
      change (kappa X).hom.f (j + 1) ≫ p'.f (j + 1) =
        F.map (p.f (j + 1)) ≫ (psi X).hom.f (j + 1)
      rw [hp', hp]
      exact (hd X j).1
    refine ⟨p, p', δ, δ', hp, hp', hδ, hδ', ?_, ?_⟩
    · have ht := congrArg (fun f ↦ f ≫ DerivedCategory.Q.map p') (hsquare X).symm
      calc
        _ = F.mapDerivedCategory.map (thetaA.hom.app X) ≫
            F.mapDerivedCategoryFactors.hom.app (HA.obj X) ≫
            DerivedCategory.Q.map ((kappa X).hom ≫ p') := by
          simpa only [Functor.map_comp, Category.assoc] using ht
        _ = _ := by
          rw [hproj, Functor.map_comp]
          simp only [Functor.map_comp, Category.assoc]
          dsimp only [Fc]
          rw [← F.mapDerivedCategoryFactors_hom_naturality_assoc p]
    · have hboundary := compatBoundary_map F (chiA X) (chiB (Ft.obj X))
        (kappa X).hom (psi X).hom (hd X) δ δ' hδ hδ'
      simpa only [Ft, Functor.comp_obj, Functor.map_comp, Iso.app_inv, Category.assoc] using
        localizedBoundary DerivedCategory.Q DerivedCategory.Q Fc F.mapDerivedCategory
          F.mapDerivedCategoryFactors (thetaA.app X) (thetaB.app (Ft.obj X))
          (lambda.hom.app (DerivedCategory.Q.obj X) ≫
            LB.map (((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapDerivedCategoryFactors.hom.app X))
          (kappa X).hom (psi X).hom δ δ'
          (by simpa only [Iso.app_hom, Category.assoc] using hsquare X)
          hboundary
  · intro X Q gamma hgamma
    have hf : Pi.lift gamma ≫ a X = 0 := by
      apply Pi.hom_ext
      intro n
      change (Pi.lift gamma ≫ (𝟙 _ - towerProductShift _)) ≫ Pi.π _ n = 0 ≫ Pi.π _ n
      rw [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
        Pi.lift_comp_π, Category.assoc, towerProductShift, Pi.lift_comp_π, ← Category.assoc,
        Pi.lift_comp_π, hgamma, sub_self, zero_comp]
    let gamma' : ∀ n : ℕ, Fc.obj Q ⟶ (Ft.obj X).asFunctor.obj (op n) :=
      fun n ↦ Fc.map (gamma n)
    have hf' : Pi.lift gamma' ≫ ab (Ft.obj X) = 0 := by
      apply Pi.hom_ext
      intro n
      have hg : gamma' (n + 1) ≫ (Ft.obj X).asFunctor.map
          (homOfLE (Nat.le_succ n)).op = gamma' n := by
        change Fc.map (gamma (n + 1)) ≫
          Fc.map (X.asFunctor.map (homOfLE (Nat.le_succ n)).op) = Fc.map (gamma n)
        rw [← Fc.map_comp, hgamma]
      change (Pi.lift gamma' ≫ (𝟙 _ - towerProductShift _)) ≫ Pi.π _ n = 0 ≫ Pi.π _ n
      rw [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
        Pi.lift_comp_π, Category.assoc, towerProductShift, Pi.lift_comp_π, ← Category.assoc,
        Pi.lift_comp_π, hg, sub_self, zero_comp]
    obtain ⟨b, hb⟩ := compatAugmentMaps (a X) (HA.obj X) (hAobj X) (chiA X)
      (hcA X) (Pi.lift gamma) hf
    obtain ⟨b', hb'⟩ := compatAugmentMaps (ab (Ft.obj X)) (HB.obj (Ft.obj X))
      (hBobj (Ft.obj X)) (chiB (Ft.obj X)) (hcB (Ft.obj X)) (Pi.lift gamma') hf'
    have hg : Fc.map (Pi.lift gamma) ≫ (psi X).hom = Pi.lift gamma' := by
      apply Pi.hom_ext
      intro n
      rw [Category.assoc, hpsi]
      change Fc.map (Pi.lift gamma) ≫ Fc.map _ = _
      rw [← Fc.map_comp, Pi.lift_comp_π, Pi.lift_comp_π]
    have hmap := compatAugment_map F (chiA X) (chiB (Ft.obj X))
      (kappa X).hom (psi X).hom (hd X) (Pi.lift gamma) (Pi.lift gamma') b b' hb hb' hg
    refine ⟨b, b', hb, hb', ?_⟩
    change F.mapDerivedCategory.map (DerivedCategory.Q.map b ≫ thetaA.inv.app X) ≫
      lambda.hom.app (DerivedCategory.Q.obj X) ≫
      LB.map (((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapDerivedCategoryFactors.hom.app X) =
      F.mapDerivedCategoryFactors.hom.app Q ≫ DerivedCategory.Q.map b' ≫
        thetaB.inv.app (Ft.obj X)
    exact localizedAugmentation DerivedCategory.Q DerivedCategory.Q Fc F.mapDerivedCategory
      F.mapDerivedCategoryFactors (thetaA.app X) (thetaB.app (Ft.obj X))
      (lambda.hom.app (DerivedCategory.Q.obj X) ≫
        LB.map (((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapDerivedCategoryFactors.hom.app X))
      (kappa X).hom (by simpa only [Iso.app_hom, Category.assoc] using hsquare X) b b' hmap

end CategoryTheory
