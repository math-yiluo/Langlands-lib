/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PrincipalKoszulDualTerms
import all WeilConjectures.Algebra.Homology.RingedSiteBoundedDualComponents

/-! # The nonzero singleton dual differential

Source: Stacks Project, algebraization.tex, Tag 0A0E.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.PrincipalKoszulDualTerms
attribute [local irreducible] homComplexFunctor homComplexπ

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (R : Sheaf J CommRingCat.{u})
variable (a : (SheafOfModules.unit
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections)

attribute [local instance 20000] ringedCompletionHasSheafCompose
attribute [local irreducible] ringedHomUnitEvaluationIso

private theorem transposeUnitScalar
    (f : SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⟶
        SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    SheafOfModules.homObjMap (R := R) f (𝟙 _) ≫
        (SheafOfModules.homObjUnitIso (R := R) (SheafOfModules.unit _)).hom =
      (SheafOfModules.homObjUnitIso (R := R) (SheafOfModules.unit _)).hom ≫ f := by
  apply SheafOfModules.hom_ext
  ext U φ : 3
  let fU : R.obj.obj U →ₗ[R.obj.obj U] R.obj.obj U := (f.val.app U).hom
  let φU : R.obj.obj U →ₗ[R.obj.obj U] R.obj.obj U :=
    (φ.app (op (Over.mk (𝟙 U.unop)))).hom
  change φU (fU 1) = fU (φU 1)
  calc
    _ = fU 1 * φU 1 := by
      simpa only [smul_eq_mul, mul_one] using φU.map_smul (fU 1) 1
    _ = φU 1 * fU 1 := mul_comm _ _
    _ = _ := by
      simpa only [smul_eq_mul, mul_one] using (fU.map_smul (φU 1) 1).symm

attribute [local irreducible] SheafOfModules.homObjMap
  SheafOfModules.homFunctor SheafOfModules.homObjUnitIso

private theorem projectionTermIso_d (L : ringedSiteComplex R) :
    (homComplex L (ringedSiteRingComplex R)).d (-1) 0 ≫
        (projectionTermIso R L 0 0 (by decide)).hom =
      (projectionTermIso R L 1 (-1) (by decide)).hom ≫
        SheafOfModules.homObjMap (R := R) (L.d 0 1) (𝟙 _) := by
  have hp (p q : ℤ) (h : p + q = 0) :
      (projectionTermIso R L p q h).hom =
        RingedSiteBoundedDual.component.{u, u, u} R L p q h := rfl
  erw [hp, hp]
  have hd := RingedSiteBoundedDual.component_d.{u, u, u} R L (-1) 0 1 0
    (by decide) (by decide) (by decide)
  unfold RingedSiteBoundedDual.complexDual RingedSiteBoundedDual.zeroComplex at hd
  erw [Int.negOnePow_zero, one_smul] at hd
  exact hd

private theorem scalarPower (n : ℕ) :
    endoPow (globalSectionMultiplication R a) n =
      ((ringedKoszulScalar R ⟨a.val, a.property⟩) ^ n).asHom := by
  change endoPow (ringedKoszulScalar R ⟨a.val, a.property⟩).asHom n = _
  induction n with
  | zero => rfl
  | succ n ih => erw [endoPow, ih, pow_succ', End.mul_asHom]

private theorem coneZeroProjection (m : ℕ) :
    (coneZeroTerm R a m).hom =
      HomologicalComplex.homotopyCofiber.sndX (scalarComplex R a m) 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))).hom := by
  change (HomologicalComplex.homotopyCofiber.XIsoBiprod (scalarComplex R a m)
      0 1 zeroOneRel).hom ≫ (biprod.snd ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (SheafOfModules.unit
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))).hom) = _
  erw [← Category.assoc]
  apply congrArg (fun f ↦ f ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))).hom)
  unfold HomologicalComplex.homotopyCofiber.sndX
  have hn : (ComplexShape.up ℤ).Rel 0 ((ComplexShape.up ℤ).next 0) := by
    erw [ComplexShape.next_eq' (ComplexShape.up ℤ)
      (show (ComplexShape.up ℤ).Rel 0 1 from rfl)]
    rfl
  erw [dite_eq_left hn]
  have hs (j : ℤ) (hj : (ComplexShape.up ℤ).Rel 0 j) :
      (HomologicalComplex.homotopyCofiber.XIsoBiprod (scalarComplex R a m)
        0 1 zeroOneRel).hom ≫ biprod.snd =
      (HomologicalComplex.homotopyCofiber.XIsoBiprod (scalarComplex R a m)
        0 j hj).hom ≫ biprod.snd := by
    have he : j = 1 := by change 0 + 1 = j at hj; omega
    subst j
    rfl
  exact hs _ _

private theorem coneDifferential (m : ℕ) :
    (principalKoszul R a m).d (-1) 0 ≫ (coneZeroTerm R a m).hom =
      (coneNegOneTerm R a m).hom ≫
        ((ringedKoszulScalar R ⟨a.val, a.property⟩) ^ (m + 1)).asHom := by
  let e := HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
  have hc0 : (coneZeroTerm R a m).hom =
      HomologicalComplex.homotopyCofiber.sndX (scalarComplex R a m) 0 ≫ e.hom :=
    coneZeroProjection R a m
  have hc1 : (coneNegOneTerm R a m).hom =
      HomologicalComplex.homotopyCofiber.fstX (scalarComplex R a m) (-1) 0
        (by decide) ≫ e.hom := by rfl
  erw [hc0, hc1]
  change HomologicalComplex.homotopyCofiber.d (scalarComplex R a m) (-1) 0 ≫
    (HomologicalComplex.homotopyCofiber.sndX (scalarComplex R a m) 0 ≫ e.hom) = _
  erw [← Category.assoc]
  erw [HomologicalComplex.homotopyCofiber.d_sndX _ (-1) 0 (by decide)]
  erw [show (homComplexUnitSource J R).d (-1) 0 = 0 from rfl, comp_zero, add_zero]
  change (_ ≫ (((HomologicalComplex.single _ (.up ℤ) 0).map
    (endoPow (globalSectionMultiplication R a) (m + 1))).f 0)) ≫ e.hom = _
  erw [HomologicalComplex.single_map_f_self]
  dsimp only [e]
  simp only [scalarPower R a]
  exact Category.assoc _ _ _

private theorem dualDifferential (m : ℕ) :
    ((ringedKoszulDualTower R 1 (fun _ ↦ ⟨a.val, a.property⟩)).obj (op m)).d (-1) 0 ≫
        (dualZeroTerm R a m).hom =
      (dualNegOneTerm R a m).hom ≫
        ((ringedKoszulScalar R ⟨a.val, a.property⟩) ^ (m + 1)).asHom := by
  erw [dualZeroTerm_hom R a m, dualNegOneTerm_hom R a m]
  let U := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let f := ((ringedKoszulScalar R ⟨a.val, a.property⟩) ^ (m + 1)).asHom
  let L := ringedKoszulFactor R ⟨a.val, a.property⟩ m
  let H := homComplex (R := R) L (ringedSiteRingComplex R)
  let e := SheafOfModules.homObjUnitIso (R := R) U
  let s0 : L.X 0 ≅ U := HomologicalComplex.doubleXIso₀ f zeroOneRel
  let s1 : L.X 1 ≅ U := HomologicalComplex.doubleXIso₁ f zeroOneRel
    (by decide : (0 : ℤ) ≠ 1)
  let v0 := homObjMapIso R s0.symm (Iso.refl U)
  let v1 := homObjMapIso R s1.symm (Iso.refl U)
  let p0 := projectionTermIso R L 0 0 (by decide)
  let p1 := projectionTermIso R L 1 (-1) (by decide)
  have hd : H.d (-1) 0 ≫ (p0.hom ≫ v0.hom ≫ e.hom) =
      (p1.hom ≫ v1.hom ≫ e.hom) ≫ f := by
    erw [← Category.assoc, projectionTermIso_d R L]
    change (p1.hom ≫ SheafOfModules.homObjMap (R := R) (L.d 0 1) (𝟙 U)) ≫
        (SheafOfModules.homObjMap (R := R) s0.inv (𝟙 U) ≫ e.hom) =
      (p1.hom ≫ SheafOfModules.homObjMap (R := R) s1.inv (𝟙 U) ≫ e.hom) ≫ f
    erw [Category.assoc, ← Category.assoc _ _ e.hom,
      SheafOfModules.homObjMap_comp_homObjMap (R := R) (L.d 0 1) s0.inv (𝟙 U) (𝟙 U)]
    have hl : s0.inv ≫ L.d 0 1 = f ≫ s1.inv := by
      change s0.inv ≫ (HomologicalComplex.double f
        zeroOneRel).d 0 1 = _
      erw [HomologicalComplex.double_d _ _ (by decide)]
      dsimp only [s0, s1]
      erw [Category.assoc, Iso.inv_hom_id_assoc]
    erw [hl]
    erw [Category.id_comp]
    have hs : SheafOfModules.homObjMap (R := R) (f ≫ s1.inv) (𝟙 U) =
        SheafOfModules.homObjMap (R := R) s1.inv (𝟙 U) ≫
          SheafOfModules.homObjMap (R := R) f (𝟙 U) := by
      symm
      simpa only [Category.comp_id] using
        SheafOfModules.homObjMap_comp_homObjMap (R := R) s1.inv f (𝟙 U) (𝟙 U)
    erw [hs]
    erw [Category.assoc, Category.assoc, transposeUnitScalar R f]
    simp only [Category.assoc]
    rfl
  let ψ : ((ringedKoszulDualTower R 1
      (fun _ ↦ ⟨a.val, a.property⟩)).obj (op m)) ≅ H :=
    ((homComplexFunctor (R := R)).flip.obj
    (ringedSiteRingComplex R)).mapIso (singletonRemoveUnit R a m).symm.op
  change _ ≫ (ψ.hom.f 0 ≫ p0.hom ≫ v0.hom ≫ e.hom) =
    (ψ.hom.f (-1) ≫ p1.hom ≫ v1.hom ≫ e.hom) ≫ f
  erw [← Category.assoc, ← ψ.hom.comm (-1) 0, Category.assoc, hd]
  simp only [Category.assoc]

/-- The explicit rank-one dual identification respects the sole nonzero differential.

Source: Stacks Project, algebraization.tex, Tag 0A0E, dual positive Koszul complex.
(auxiliary; not a blueprint node).

Proof: remove the right tensor unit by its chain isomorphism. Project Hom into R[0]
to source degrees 1 and 0. The product differential formula leaves
-(-1)^(-1) times precomposition by a^(m+1), so the sign is +1. Transport the two
rank-one terms by doubleXIso and evaluate at one. For a local scalar r, precomposing
multiplication by a^(m+1) sends the functional with value r at one to the functional
with value a^(m+1)r at one. This equals r a^(m+1) by commutativity. The cone differential,
projected from its shifted source to its target, is the single chain map for the
same scalar. Its other matrix entries vanish. Induction identifies endoPow with
categorical powers. Conjugating these two scalar identities by the explicitly defined
term isomorphisms gives the displayed equality. There is no regularity assumption;
zero and invertible a and the zero ring satisfy exactly the same scalar computation. -/
theorem finiteDualTerm_nonzero_differential (m : ℕ) :
    (finiteDualTerm R a m (-1)).hom ≫
        ((ringedKoszulDualTower R 1
          (fun _ ↦ ⟨a.val, a.property⟩)).obj (op m)).d (-1) 0 =
      (principalKoszul R a m).d (-1) 0 ≫
        (finiteDualTerm R a m 0).hom := by
  have h0 : (finiteDualTerm R a m 0).hom =
      (coneZeroTerm R a m).hom ≫ (dualZeroTerm R a m).inv := by
    simp [finiteDualTerm]
  have h1 : (finiteDualTerm R a m (-1)).hom =
      (coneNegOneTerm R a m).hom ≫ (dualNegOneTerm R a m).inv := by
    simp [finiteDualTerm]
  erw [h0, h1]
  apply (cancel_mono (dualZeroTerm R a m).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  erw [dualDifferential R a m, Iso.inv_hom_id_assoc, coneDifferential R a m]

end CategoryTheory.PrincipalKoszulDualTerms
