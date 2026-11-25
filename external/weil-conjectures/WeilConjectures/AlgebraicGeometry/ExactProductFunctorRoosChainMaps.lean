/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.StrictRoosComparison

/-!
# Strict chain-level Roos comparison for an exact product-preserving functor

Source: Stacks Project, Tags 0940 and 0941, and the final paragraph of
literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-sf-cbc/lem-cbc-completed-extension-zero-comparison.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe uC vC r uD vD s wA wB
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

section ConeComparison
open HomologicalComplex
universe u v u' v'
variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B]
  [Abelian A] [Abelian B]
variable (F : A ⥤ B) [F.Additive]
variable {P : CochainComplex A ℤ} {Q : CochainComplex B ℤ}
  (φ : P ⟶ P) (ψ : Q ⟶ Q)
  (e : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ≅ Q)
  (h : (F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ ≫ e.hom = e.hom ≫ ψ)

private def cc : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (CochainComplex.mappingCone φ) ≅ CochainComplex.mappingCone ψ :=
  CochainComplex.mappingCone.mapHomologicalComplexIso φ F ≪≫
    homotopyCofiber.mapArrowIso _ _ (fun j ↦ ⟨j - 1, by dsimp; omega⟩)
      (Arrow.isoMk e e (by simpa using h.symm))

private theorem arrow_fst (p : ℤ) :
    (homotopyCofiber.mapArrowHom
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) ψ
      (fun j ↦ ⟨j - 1, by dsimp; omega⟩) (Arrow.isoMk e e (by simpa using h.symm)).hom).f p ≫
        homotopyCofiber.fstX ψ p (p + 1) rfl =
      homotopyCofiber.fstX ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)
        p (p + 1) rfl ≫ e.hom.f (p + 1) := by
  rw [homotopyCofiber.mapArrowHom, homotopyCofiber.desc_f _ _ _ p (p + 1) rfl]
  simp [Category.assoc, homotopyCofiber.inrCompHomotopy_hom]

private theorem cone_fst (p : ℤ) :
    (CochainComplex.mappingCone.mapHomologicalComplexIso φ F).hom.f p ≫
        homotopyCofiber.fstX ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)
          p (p + 1) rfl =
      F.map (homotopyCofiber.fstX φ p (p + 1) rfl) := by
  change (CochainComplex.mappingCone.mapHomologicalComplexXIso' φ F p (p + 1) rfl).hom ≫
    homotopyCofiber.fstX _ p (p + 1) rfl = _
  simp [CochainComplex.mappingCone.mapHomologicalComplexXIso',
    CochainComplex.mappingCone.fst, CochainComplex.mappingCone.inl,
    CochainComplex.mappingCone.inr, Category.assoc]

private theorem cc_fst (p : ℤ) :
    (cc F φ ψ e (by simpa using h)).hom.f p ≫ homotopyCofiber.fstX ψ p (p + 1) rfl =
      F.map (homotopyCofiber.fstX φ p (p + 1) rfl) ≫ e.hom.f (p + 1) := by
  dsimp only [cc, Iso.trans_hom, HomologicalComplex.comp_f,
    homotopyCofiber.mapArrowIso_hom]
  rw [Category.assoc, arrow_fst F φ ψ e h p, ← Category.assoc, cone_fst]

private theorem arrow_snd (p : ℤ) :
    (homotopyCofiber.mapArrowHom
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) ψ
      (fun j ↦ ⟨j - 1, by dsimp; omega⟩) (Arrow.isoMk e e (by simpa using h.symm)).hom).f p ≫
        homotopyCofiber.sndX ψ p =
      homotopyCofiber.sndX ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)
        p ≫ e.hom.f p := by
  rw [homotopyCofiber.mapArrowHom, homotopyCofiber.desc_f _ _ _ p (p + 1) rfl]
  simp [Category.assoc, homotopyCofiber.inrCompHomotopy_hom]

private theorem cone_snd (p : ℤ) :
    (CochainComplex.mappingCone.mapHomologicalComplexIso φ F).hom.f p ≫
        homotopyCofiber.sndX ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) p =
      F.map (homotopyCofiber.sndX φ p) := by
  change (CochainComplex.mappingCone.mapHomologicalComplexXIso' φ F p (p + 1) rfl).hom ≫
    homotopyCofiber.sndX _ p = _
  simp [CochainComplex.mappingCone.mapHomologicalComplexXIso',
    CochainComplex.mappingCone.snd, CochainComplex.mappingCone.inl,
    CochainComplex.mappingCone.inr, Category.assoc]

private theorem cc_snd (p : ℤ) :
    (cc F φ ψ e (by simpa using h)).hom.f p ≫ homotopyCofiber.sndX ψ p =
      F.map (homotopyCofiber.sndX φ p) ≫ e.hom.f p := by
  dsimp only [cc, Iso.trans_hom, HomologicalComplex.comp_f,
    homotopyCofiber.mapArrowIso_hom]
  rw [Category.assoc, arrow_snd F φ ψ e h p, ← Category.assoc, cone_snd]

private def cs : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((CochainComplex.mappingCone φ)⟦(-1 : ℤ)⟧) ≅
      (CochainComplex.mappingCone ψ)⟦(-1 : ℤ)⟧ :=
  ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (-1)).app _ ≪≫
    (shiftFunctor _ (-1 : ℤ)).mapIso (cc F φ ψ e h)

private theorem mapXIso (V : CochainComplex A ℤ) {i j : ℤ} (hij : i = j) :
    (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj V).XIsoOfEq hij).hom =
      F.map (V.XIsoOfEq hij).hom := by
  subst j
  simp

private theorem cs_fst (p : ℤ) :
    (cs F φ ψ e (by simpa using h)).hom.f (p + 1) ≫
      ((CochainComplex.mappingCone ψ).shiftFunctorObjXIso (-1) (p + 1) p
        (add_neg_cancel_right p 1).symm).hom ≫
        homotopyCofiber.fstX ψ p (p + 1) rfl =
      F.map (((CochainComplex.mappingCone φ).shiftFunctorObjXIso (-1) (p + 1) p
        (add_neg_cancel_right p 1).symm).hom ≫
        homotopyCofiber.fstX φ p (p + 1) rfl) ≫ e.hom.f (p + 1) := by
  dsimp only [cs, Iso.trans_hom, HomologicalComplex.comp_f,
    Functor.mapIso_hom]
  change (𝟙 _ ≫ (cc F φ ψ e h).hom.f (p + 1 + -1)) ≫ _ ≫ _ = _
  rw [Category.id_comp]
  rw [CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_hom_naturality_assoc]
  rw [cc_fst F φ ψ e h p]
  rw [mapXIso, ← Category.assoc, ← F.map_comp]
  rfl

private theorem cs_snd (p : ℤ) :
    (cs F φ ψ e (by simpa using h)).hom.f (p + 1) ≫
      ((CochainComplex.mappingCone ψ).shiftFunctorObjXIso (-1) (p + 1) p
        (add_neg_cancel_right p 1).symm).hom ≫
        homotopyCofiber.sndX ψ p =
      F.map (((CochainComplex.mappingCone φ).shiftFunctorObjXIso (-1) (p + 1) p
        (add_neg_cancel_right p 1).symm).hom ≫
        homotopyCofiber.sndX φ p) ≫ e.hom.f p := by
  dsimp only [cs, Iso.trans_hom, HomologicalComplex.comp_f,
    Functor.mapIso_hom]
  change (𝟙 _ ≫ (cc F φ ψ e h).hom.f (p + 1 + -1)) ≫ _ ≫ _ = _
  rw [Category.id_comp]
  rw [CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_hom_naturality_assoc]
  rw [cc_snd F φ ψ e h p]
  rw [mapXIso, ← Category.assoc, ← F.map_comp]
  rfl

private def signedCoords (T : CochainComplex A ℤ) (a : T ⟶ T) (p : ℤ) :
    ((CochainComplex.mappingCone a)⟦(-1 : ℤ)⟧).X (p + 1) ≅ T.X (p + 1) ⊞ T.X p :=
  (CochainComplex.mappingCone a).shiftFunctorObjXIso (-1) (p + 1) p
      (add_neg_cancel_right p 1).symm ≪≫
    homotopyCofiber.XIsoBiprod a p (p + 1) rfl ≪≫
    (⟨biprod.map (𝟙 _) (-𝟙 _), biprod.map (𝟙 _) (-𝟙 _),
      by ext <;> simp, by ext <;> simp⟩)

private theorem signed_fst (p : ℤ) :
    (cs F φ ψ e h).hom.f (p + 1) ≫ (signedCoords Q ψ p).hom ≫ biprod.fst =
      F.map ((signedCoords P φ p).hom ≫ biprod.fst) ≫ e.hom.f (p + 1) := by
  simpa [signedCoords, Category.assoc, homotopyCofiber.fstX] using cs_fst F φ ψ e h p

private theorem cofiber_snd {T : CochainComplex A ℤ} (a : T ⟶ T)
    (p j : ℤ) (hpj : (ComplexShape.up ℤ).Rel p j) :
    (homotopyCofiber.XIsoBiprod a p j hpj).hom ≫ biprod.snd =
      homotopyCofiber.sndX a p := by
  obtain rfl := (ComplexShape.up ℤ).next_eq' hpj
  simp only [homotopyCofiber.sndX, dite_eq_left hpj]

private theorem signed_snd (p : ℤ) :
    (cs F φ ψ e h).hom.f (p + 1) ≫ (signedCoords Q ψ p).hom ≫ biprod.snd =
      F.map ((signedCoords P φ p).hom ≫ biprod.snd) ≫ e.hom.f p := by
  simpa only [signedCoords, Iso.trans_hom, Category.assoc, biprod.map_snd,
    Preadditive.comp_neg, Category.comp_id, cofiber_snd,
    Functor.map_comp, Functor.map_neg, Preadditive.neg_comp] using
    congrArg Neg.neg (cs_snd F φ ψ e h p)

private def transportedComparison (U : CochainComplex A ℤ) (V : CochainComplex B ℤ)
    (hU : U = (CochainComplex.mappingCone φ)⟦(-1 : ℤ)⟧)
    (hV : V = (CochainComplex.mappingCone ψ)⟦(-1 : ℤ)⟧) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj U ≅ V :=
  (F.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso (eqToIso hU) ≪≫
    cs F φ ψ e h ≪≫ (eqToIso hV).symm

private def transportedCoords (U : CochainComplex A ℤ)
    (hU : U = (CochainComplex.mappingCone φ)⟦(-1 : ℤ)⟧) (p : ℤ) :
    U.X (p + 1) ≅ P.X (p + 1) ⊞ P.X p :=
  eqToIso (congrArg (fun V : CochainComplex A ℤ ↦ V.X (p + 1)) hU) ≪≫
    signedCoords P φ p

private theorem transported_fst (U : CochainComplex A ℤ) (V : CochainComplex B ℤ)
    (hU : U = (CochainComplex.mappingCone φ)⟦(-1 : ℤ)⟧)
    (hV : V = (CochainComplex.mappingCone ψ)⟦(-1 : ℤ)⟧) (p : ℤ) :
    (transportedComparison F φ ψ e h U V hU hV).hom.f (p + 1) ≫
        (transportedCoords ψ V hV p).hom ≫ biprod.fst =
      F.map ((transportedCoords φ U hU p).hom ≫ biprod.fst) ≫ e.hom.f (p + 1) := by
  subst U; subst V
  simpa [transportedComparison, transportedCoords] using signed_fst F φ ψ e h p

private theorem transported_snd (U : CochainComplex A ℤ) (V : CochainComplex B ℤ)
    (hU : U = (CochainComplex.mappingCone φ)⟦(-1 : ℤ)⟧)
    (hV : V = (CochainComplex.mappingCone ψ)⟦(-1 : ℤ)⟧) (p : ℤ) :
    (transportedComparison F φ ψ e h U V hU hV).hom.f (p + 1) ≫
        (transportedCoords ψ V hV p).hom ≫ biprod.snd =
      F.map ((transportedCoords φ U hU p).hom ≫ biprod.snd) ≫ e.hom.f p := by
  subst U; subst V
  simpa [transportedComparison, transportedCoords] using signed_snd F φ ψ e h p

end ConeComparison

private theorem chainProducts {A B : Type*} [Category* A] [Category* B]
    [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) (h : ∀ M : ℕ → A, IsIso (piComparison F M)) :
    PreservesLimitsOfShape (Discrete ℕ) F where
  preservesLimit {K} := by
    have := h (fun n ↦ K.obj ⟨n⟩)
    have : PreservesLimit (Discrete.functor (K.obj ∘ Discrete.mk)) F :=
      PreservesProduct.of_iso_comparison F (K.obj ∘ Discrete.mk)
    exact preservesLimit_of_iso_diagram F Discrete.natIsoFunctor.symm

private theorem productComparison_transition {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
    (P : ℕ → CochainComplex A ℤ) (f : ∀ n, P (n + 1) ⟶ P n) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (towerTransitionEndomorphism f) ≫
        piComparison (F.mapHomologicalComplex (ComplexShape.up ℤ)) P =
      piComparison (F.mapHomologicalComplex (ComplexShape.up ℤ)) P ≫
        towerTransitionEndomorphism
          (fun n ↦ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (f n)) := by
  let Fc := F.mapHomologicalComplex (ComplexShape.up ℤ)
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, towerTransitionEndomorphism, towerProductShift,
    Preadditive.sub_comp, Pi.lift_comp_π, Preadditive.comp_sub, Category.comp_id]
  simp only [Preadditive.sub_comp, Functor.map_sub]
  simp [← Functor.map_comp]

private theorem productComparison_natural {A B : Type*} [Category* A] [Category* B]
    [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) {P Q : ℕ → A} (a : ∀ n, P n ⟶ Q n) :
    F.map (Limits.Pi.map a) ≫ piComparison F Q =
      piComparison F P ≫ Limits.Pi.map (fun n ↦ F.map (a n)) := by
  apply Pi.hom_ext
  intro n
  simp [← Functor.map_comp]

private theorem diagonal_natural {A B : Type*} [Category* A] [Category* B]
    [Preadditive A] [Preadditive B] [HasBinaryBiproducts A] [HasBinaryBiproducts B]
    (F : A ⥤ B) {U V P Q P' Q' : A} {W Z L M L' M' : B}
    (cU : U ≅ P ⊞ Q) (cV : V ≅ P' ⊞ Q')
    (cW : W ≅ L ⊞ M) (cZ : Z ≅ L' ⊞ M')
    (u : U ⟶ V) (v : W ⟶ Z) (kx : F.obj U ⟶ W) (ky : F.obj V ⟶ Z)
    (a : P ⟶ P') (b : Q ⟶ Q') (a' : L ⟶ L') (b' : M ⟶ M')
    (eP : F.obj P ⟶ L) (eQ : F.obj Q ⟶ M)
    (eP' : F.obj P' ⟶ L') (eQ' : F.obj Q' ⟶ M')
    (hu : u ≫ cV.hom = cU.hom ≫ biprod.map a b)
    (hv : v ≫ cZ.hom = cW.hom ≫ biprod.map a' b')
    (hx₁ : kx ≫ cW.hom ≫ biprod.fst = F.map (cU.hom ≫ biprod.fst) ≫ eP)
    (hx₂ : kx ≫ cW.hom ≫ biprod.snd = F.map (cU.hom ≫ biprod.snd) ≫ eQ)
    (hy₁ : ky ≫ cZ.hom ≫ biprod.fst = F.map (cV.hom ≫ biprod.fst) ≫ eP')
    (hy₂ : ky ≫ cZ.hom ≫ biprod.snd = F.map (cV.hom ≫ biprod.snd) ≫ eQ')
    (he₁ : F.map a ≫ eP' = eP ≫ a')
    (he₂ : F.map b ≫ eQ' = eQ ≫ b') : F.map u ≫ ky = kx ≫ v := by
  apply (cancel_mono cZ.hom).mp
  apply biprod.hom_ext
  · simp only [Category.assoc]
    rw [hy₁, ← Category.assoc, ← F.map_comp, ← Category.assoc, hu]
    simp only [Category.assoc, biprod.map_fst, F.map_comp]
    rw [he₁]
    rw [← Category.assoc v, hv]
    simp only [Category.assoc, biprod.map_fst]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun t ↦ t ≫ a') hx₁.symm
  · simp only [Category.assoc]
    rw [hy₂, ← Category.assoc, ← F.map_comp, ← Category.assoc, hu]
    simp only [Category.assoc, biprod.map_snd, F.map_comp]
    rw [he₂]
    rw [← Category.assoc v, hv]
    simp only [Category.assoc, biprod.map_snd]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun t ↦ t ≫ b') hx₂.symm

-- The statement contains simultaneous universe-polymorphic cone comparisons.
/-- Strict chain-level Roos comparison for an exact product-preserving functor.

Source: Stacks Project, Tags 0940 and 0941, and the final paragraph of
literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-sf-cbc/lem-cbc-completed-extension-zero-comparison.proof.md.
(auxiliary; not a blueprint node).

Proof in words:
Take the canonical product comparison degreewise. Its projection identities imply
that it commutes with differentials and with the tower shift, hence with 1-s.
The cone comparison for an additive functor, followed by this commuting square,
and the shift comparison give kappa. Transport by the two object equalities.
In the signed coordinates its two components are the product comparison, which
proves the displayed equations. Apply product projections to the two components
for a strict tower map to obtain naturality. The inverse uses the inverse product
comparison on both coordinates, so kappa is an isomorphism. -/
theorem exactProductFunctorRoosChainMaps
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
    (hmaps :
      (∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ} (f : X ⟶ Y) (p : ℤ),
        (HA.map f).f (p + 1) ≫ (chiA Y p).hom = (chiA X p).hom ≫
        biprod.map
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f (p + 1))
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f p)) ∧
      (∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) ℤ} (f : X ⟶ Y) (p : ℤ),
        (HB.map f).f (p + 1) ≫ (chiB Y p).hom = (chiB X p).hom ≫
        biprod.map
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f (p + 1))
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f p))) :
    ∃ (psi : ∀ X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op
        n))) ≅ (∏ᶜ (fun n : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj X).asFunctor.obj (op n))))
      (kappa : ∀ X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (HA.obj X) ≅ HB.obj
        ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        X)),
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (n : ℕ), (psi X).hom ≫
        Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj X).asFunctor.obj (op k)) n =
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k))
          n)) ∧
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
            (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f p)) ∧
      (∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ}
        (f : X ⟶ Y),
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (HA.map f) ≫ (kappa Y).hom =
          (kappa X).hom ≫ HB.map
            ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).map f)) := by
  have : PreservesLimitsOfShape (Discrete ℕ) F := chainProducts F _hphi
  let Fc := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let Ft := ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let P := fun X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ ↦
    fun n : ℕ ↦ X.asFunctor.obj (op n)
  let t := fun X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ ↦
    fun n : ℕ ↦ X.asFunctor.map (homOfLE (Nat.le_succ n)).op
  let psi := fun X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ ↦
    asIso (piComparison Fc (P X))
  have ht (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) :
      Fc.map (towerTransitionEndomorphism (K := P X) (t X)) ≫ (psi X).hom =
        (psi X).hom ≫ towerTransitionEndomorphism (K := fun n ↦ Fc.obj (P X n))
        (fun n ↦ Fc.map (t X n)) :=
    productComparison_transition F (P X) (t X)
  let kappa := fun X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ ↦
    transportedComparison F (P := ∏ᶜ (P X))
      (Q := ∏ᶜ (fun n ↦ Fc.obj (P X n))) (towerTransitionEndomorphism (K := P X) (t X))
      (towerTransitionEndomorphism (K := fun n ↦ Fc.obj (P X n))
        (fun n ↦ Fc.map (t X n))) (psi X) (ht X)
      (HA.obj X) (HB.obj (Ft.obj X)) (hAobj X) (hBobj (Ft.obj X))
  have hdiag (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (p : ℤ) :
      ((kappa X).hom.f (p + 1) ≫ (chiB (Ft.obj X) p).hom ≫ biprod.fst =
        F.map ((chiA X p).hom ≫ biprod.fst) ≫ (psi X).hom.f (p + 1)) ∧
      ((kappa X).hom.f (p + 1) ≫ (chiB (Ft.obj X) p).hom ≫ biprod.snd =
        F.map ((chiA X p).hom ≫ biprod.snd) ≫ (psi X).hom.f p) := by
    have hca : (chiA X p).hom =
        (transportedCoords (P := ∏ᶜ (P X))
          (towerTransitionEndomorphism (K := P X) (t X)) (HA.obj X) (hAobj X) p).hom :=
      hcoord.1 X p
    have hcb : (chiB (Ft.obj X) p).hom =
        (transportedCoords (P := ∏ᶜ (fun n ↦ Fc.obj (P X n)))
          (towerTransitionEndomorphism (K := fun n ↦ Fc.obj (P X n))
        (fun n ↦ Fc.map (t X n)))
          (HB.obj (Ft.obj X)) (hBobj (Ft.obj X)) p).hom := hcoord.2 (Ft.obj X) p
    rw [hca, hcb]
    constructor
    · exact transported_fst F (P := ∏ᶜ (P X))
        (Q := ∏ᶜ (fun n ↦ Fc.obj (P X n))) (towerTransitionEndomorphism (K := P X) (t X))
        (towerTransitionEndomorphism (K := fun n ↦ Fc.obj (P X n))
        (fun n ↦ Fc.map (t X n))) (psi X) (ht X)
        (HA.obj X) (HB.obj (Ft.obj X)) (hAobj X) (hBobj (Ft.obj X)) p
    · exact transported_snd F (P := ∏ᶜ (P X))
        (Q := ∏ᶜ (fun n ↦ Fc.obj (P X n))) (towerTransitionEndomorphism (K := P X) (t X))
        (towerTransitionEndomorphism (K := fun n ↦ Fc.obj (P X n))
        (fun n ↦ Fc.map (t X n))) (psi X) (ht X)
        (HA.obj X) (HB.obj (Ft.obj X)) (hAobj X) (hBobj (Ft.obj X)) p
  refine ⟨psi, kappa, ?_, ?_, ?_⟩
  · intro X n
    exact piComparison_comp_π Fc (P X) n
  · intro X p n
    constructor
    · have hh := congrArg (fun f ↦ f.f (p + 1)) (piComparison_comp_π Fc (P X) n)
      dsimp only [HomologicalComplex.comp_f] at hh
      change (psi X).hom.f _ ≫ _ = F.map _ at hh
      have hd := congrArg (fun z ↦ z ≫ (Pi.π (fun n ↦ Fc.obj (P X n)) n).f (p + 1))
        (hdiag X p).1
      convert! (by simpa only [Category.assoc, hh, ← F.map_comp] using hd) using 1
    · have hh := congrArg (fun f ↦ f.f p) (piComparison_comp_π Fc (P X) n)
      dsimp only [HomologicalComplex.comp_f] at hh
      change (psi X).hom.f _ ≫ _ = F.map _ at hh
      have hd := congrArg (fun z ↦ z ≫ (Pi.π (fun n ↦ Fc.obj (P X n)) n).f p)
        (hdiag X p).2
      convert! (by simpa only [Category.assoc, hh, ← F.map_comp] using hd) using 1
  · intro X Y f
    apply HomologicalComplex.Hom.ext
    funext i
    obtain ⟨p, rfl⟩ : ∃ p : ℤ, i = p + 1 := ⟨i - 1, by omega⟩
    have hn := productComparison_natural Fc (fun n : ℕ ↦
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n))
    have hn₁ := congrArg (fun f ↦ f.f (p + 1)) hn
    have hn₂ := congrArg (fun f ↦ f.f p) hn
    exact diagonal_natural F (chiA X p) (chiA Y p)
      (chiB (Ft.obj X) p) (chiB (Ft.obj Y) p)
      ((HA.map f).f (p + 1)) ((HB.map (Ft.map f)).f (p + 1))
      ((kappa X).hom.f (p + 1)) ((kappa Y).hom.f (p + 1))
      _ _ _ _ _ _ _ _ (hmaps.1 f p) (hmaps.2 (Ft.map f) p)
      (hdiag X p).1 (hdiag X p).2 (hdiag Y p).1 (hdiag Y p).2 hn₁ hn₂

end CategoryTheory
