/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.PrincipalKoszulQuotientTowers
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
import all WeilConjectures.Algebra.Homology.RingedSiteBoundedDualComponents

/-! # Explicit singleton Koszul dual component identifications

Source: Stacks Project, algebraization.tex, Tag 0A0E.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.PrincipalKoszulDualTerms

/-- The supported upward differential starts in degree zero.
Source: Stacks Project, algebraization.tex, Tag 0A0E, singleton dual Koszul calculation.
(auxiliary; not a blueprint node). -/
theorem zeroOneRel : (ComplexShape.up ℤ).Rel 0 1 := by rfl

/-- The supported upward cone differential starts in degree minus one.
Source: Stacks Project, algebraization.tex, Tag 0A0E, singleton dual Koszul calculation.
(auxiliary; not a blueprint node). -/
theorem negOneZeroRel : (ComplexShape.up ℤ).Rel (-1) 0 := by rfl

attribute [local instance 20000] ringedCompletionHasSheafCompose
attribute [local irreducible] ringedHomUnitEvaluationIso

/-- Remove a zero left summand using the biproduct projection.
Source: Stacks Project, algebraization.tex, Tag 0A0E, singleton dual Koszul calculation.
(auxiliary; not a blueprint node). -/
def biprodZeroLeftIso {A : Type*} [Category* A] [Preadditive A]
    (X Y : A) [HasBinaryBiproduct X Y] (hX : IsZero X) : X ⊞ Y ≅ Y where
  hom := biprod.snd
  inv := biprod.inr
  hom_inv_id := by
    apply biprod.hom_ext'
    · exact hX.eq_of_src _ _
    · simp
  inv_hom_id := biprod.inr_snd

/-- Remove a zero right summand using the biproduct projection.
Source: Stacks Project, algebraization.tex, Tag 0A0E, singleton dual Koszul calculation.
(auxiliary; not a blueprint node). -/
def biprodZeroRightIso {A : Type*} [Category* A] [Preadditive A]
    (X Y : A) [HasBinaryBiproduct X Y] (hY : IsZero Y) : X ⊞ Y ≅ X where
  hom := biprod.fst
  inv := biprod.inl
  hom_inv_id := by
    apply biprod.hom_ext'
    · simp
    · exact hY.eq_of_src _ _
  inv_hom_id := biprod.inl_fst

section FiniteTerms
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (R : Sheaf J CommRingCat.{u})
variable (a : (SheafOfModules.unit
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections)

/-- The actual multiplication chain map whose cone is the principal Koszul complex.
Source: Stacks Project, algebraization.tex, Tag 0A0E, singleton dual Koszul calculation.
(auxiliary; not a blueprint node). -/
abbrev scalarComplex (m : ℕ) := principalKoszulScalarComplex R a m

/-- The degree-zero cone term, projected to its nonzero summand.
Source: Stacks Project, algebraization.tex, Tag 0A0E, singleton dual Koszul calculation.
(auxiliary; not a blueprint node). -/
def coneZeroTerm (m : ℕ) :
    (principalKoszul R a m).X 0 ≅ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod (scalarComplex R a m) 0 1 zeroOneRel ≪≫
    biprodZeroLeftIso _ _ (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ 1
      (by decide)) ≪≫ HomologicalComplex.singleObjXSelf (.up ℤ) 0 _

/-- The degree-minus-one cone term, projected to its nonzero summand.
Source: Stacks Project, algebraization.tex, Tag 0A0E, singleton dual Koszul calculation.
(auxiliary; not a blueprint node). -/
def coneNegOneTerm (m : ℕ) :
    (principalKoszul R a m).X (-1) ≅ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod (scalarComplex R a m) (-1) 0 negOneZeroRel ≪≫
    biprodZeroRightIso _ _ (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ (-1)
      (by decide)) ≪≫ HomologicalComplex.singleObjXSelf (.up ℤ) 0 _

/-- All other cone terms vanish, since both single-complex terms vanish.
Source: Stacks Project, algebraization.tex, Tag 0A0E, singleton dual Koszul calculation.
(auxiliary; not a blueprint node). -/
theorem coneOtherTerm (m : ℕ) (q : ℤ) (h0 : q ≠ 0) (h1 : q ≠ -1) :
    IsZero ((principalKoszul R a m).X q) := by
  apply HomologicalComplex.homotopyCofiber.isZero_X (scalarComplex R a m) q
  · exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ q h0
  · intro j hj
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ j (by
      change q + 1 = j at hj
      omega)

/-- Remove the right unit from the singleton positive Koszul diagram.
Source: Stacks Project, algebraization.tex, Tag 0A0E, singleton dual Koszul calculation.
(auxiliary; not a blueprint node). -/
def singletonRemoveUnit (m : ℕ) :
    (ringedKoszulDiagram R 1 (fun _ ↦ ⟨a.val, a.property⟩)).obj m ≅
      ringedKoszulFactor R ⟨a.val, a.property⟩ m :=
  ringedKoszulRightUnitIso R _

/-- Projection to the unique surviving Hom factor is invertible. Its inverse inserts
a map into that factor and zero elsewhere; the product universal property proves both identities.
Source: Stacks Project, algebraization.tex, Tag 0A0E, singleton dual Koszul calculation.
(auxiliary; not a blueprint node). -/
theorem projectionIsIso (L : ringedSiteComplex R) (p q : ℤ) (h : p + q = 0) :
    IsIso (homComplexπ L (ringedSiteRingComplex R) q p 0 h) :=
  RingedSiteBoundedDual.projection_isIso.{u, u, u} R L p q h

attribute [local irreducible] homComplexFunctor homComplexπ

/-- Transport internal Hom by two specified isomorphisms, with explicit forward and inverse maps.
Source: Stacks Project, algebraization.tex, Tag 0A0E, singleton dual Koszul calculation.
(auxiliary; not a blueprint node). -/
def homObjMapIso
    {A A' B B' : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (s : A' ≅ A) (t : B ≅ B') :
    SheafOfModules.homObj (R := R) A B ≅ SheafOfModules.homObj (R := R) A' B' where
  hom := SheafOfModules.homObjMap (R := R) s.hom t.hom
  inv := SheafOfModules.homObjMap (R := R) s.inv t.inv
  hom_inv_id := by
    rw [SheafOfModules.homObjMap_comp_homObjMap (R := R), s.inv_hom_id,
      t.hom_inv_id]
    exact SheafOfModules.homObjMap_id (R := R) (M := A) (N := B)
  inv_hom_id := by
    rw [SheafOfModules.homObjMap_comp_homObjMap (R := R), s.hom_inv_id,
      t.inv_hom_id]
    exact SheafOfModules.homObjMap_id (R := R) (M := A') (N := B')

/-- The canonical Hom-to-single component isomorphism, with its specified projection.
Source: Stacks Project, algebraization.tex, Tag 0A0E, singleton dual Koszul calculation.
(auxiliary; not a blueprint node). -/
def projectionTermIso (L : ringedSiteComplex R) (p q : ℤ) (h : p + q = 0) :
    (homComplex L (ringedSiteRingComplex R)).X q ≅
      SheafOfModules.homObj (R := R) (L.X p) (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  letI := projectionIsIso R L p q h
  asIso (homComplexπ L (ringedSiteRingComplex R) q p 0 h) ≪≫
    homObjMapIso R (Iso.refl (L.X p))
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _)

/-- Remove the positive tensor unit, project the Hom product and identify its target unit.
Source: Stacks Project, algebraization.tex, Tag 0A0E, singleton dual Koszul calculation.
(auxiliary; not a blueprint node). -/
def dualFactorTerm (m : ℕ) (q : ℤ) :
    ((ringedKoszulDualTower R 1 (fun _ ↦ ⟨a.val, a.property⟩)).obj (op m)).X q ≅
      SheafOfModules.homObj (R := R)
        ((ringedKoszulFactor R ⟨a.val, a.property⟩ m).X (-q))
        (SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  (HomologicalComplex.eval _ (.up ℤ) q).mapIso
    (((homComplexFunctor (R := R)).flip.obj (ringedSiteRingComplex R)).mapIso
      (singletonRemoveUnit R a m).symm.op) ≪≫
    projectionTermIso R (ringedKoszulFactor R ⟨a.val, a.property⟩ m)
      (-q) q (neg_add_cancel q)

/-- Evaluate the degree-zero rank-one dual at one.
Source: Stacks Project, algebraization.tex, Tag 0A0E, singleton dual Koszul calculation.
(auxiliary; not a blueprint node). -/
def dualZeroTerm (m : ℕ) :
    ((ringedKoszulDualTower R 1 (fun _ ↦ ⟨a.val, a.property⟩)).obj (op m)).X 0 ≅
      SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  dualFactorTerm R a m 0 ≪≫
    homObjMapIso R
      (HomologicalComplex.doubleXIso₀
        ((ringedKoszulScalar R ⟨a.val, a.property⟩) ^ (m + 1)).asHom
        zeroOneRel).symm (Iso.refl _) ≪≫
    SheafOfModules.homObjUnitIso (R := R) _

/-- Evaluate the degree-minus-one rank-one dual at one.
Source: Stacks Project, algebraization.tex, Tag 0A0E, singleton dual Koszul calculation.
(auxiliary; not a blueprint node). -/
def dualNegOneTerm (m : ℕ) :
    ((ringedKoszulDualTower R 1 (fun _ ↦ ⟨a.val, a.property⟩)).obj (op m)).X (-1) ≅
      SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  dualFactorTerm R a m (-1) ≪≫
    homObjMapIso R
      (HomologicalComplex.doubleXIso₁
        ((ringedKoszulScalar R ⟨a.val, a.property⟩) ^ (m + 1)).asHom
        zeroOneRel (by decide)).symm (Iso.refl _) ≪≫
    SheafOfModules.homObjUnitIso (R := R) _

/-- Outside degrees minus one and zero the surviving source term is zero, hence so is Hom.
Source: Stacks Project, algebraization.tex, Tag 0A0E, singleton dual Koszul calculation.
(auxiliary; not a blueprint node). -/
theorem dualOtherTerm (m : ℕ) (q : ℤ) (h0 : q ≠ 0) (h1 : q ≠ -1) :
    IsZero (((ringedKoszulDualTower R 1
      (fun _ ↦ ⟨a.val, a.property⟩)).obj (op m)).X q) := by
  apply IsZero.of_iso _ (dualFactorTerm R a m q)
  exact ((SheafOfModules.homFunctor R).flip.obj (SheafOfModules.unit _)).map_isZero
    (HomologicalComplex.isZero_double_X
      ((ringedKoszulScalar R ⟨a.val, a.property⟩) ^ (m + 1)).asHom
      zeroOneRel (-q) (by omega) (by omega)).op

/-- The explicit degreewise cone-to-dual identification. At the two supported degrees use
the projection and evaluation maps above; at other degrees use the unique zero-object isomorphism.
Source: Stacks Project, algebraization.tex, Tag 0A0E, singleton dual Koszul calculation.
(auxiliary; not a blueprint node). -/
def finiteDualTerm (m : ℕ) (q : ℤ) :
    (principalKoszul R a m).X q ≅
      ((ringedKoszulDualTower R 1
        (fun _ ↦ ⟨a.val, a.property⟩)).obj (op m)).X q :=
  if h0 : q = 0 then
    (principalKoszul R a m).XIsoOfEq h0 ≪≫ coneZeroTerm R a m ≪≫
      (dualZeroTerm R a m).symm ≪≫
      (((ringedKoszulDualTower R 1
        (fun _ ↦ ⟨a.val, a.property⟩)).obj (op m)).XIsoOfEq h0).symm
  else if h1 : q = -1 then
    (principalKoszul R a m).XIsoOfEq h1 ≪≫ coneNegOneTerm R a m ≪≫
      (dualNegOneTerm R a m).symm ≪≫
      (((ringedKoszulDualTower R 1
        (fun _ ↦ ⟨a.val, a.property⟩)).obj (op m)).XIsoOfEq h1).symm
  else (coneOtherTerm R a m q h0 h1).iso (dualOtherTerm R a m q h0 h1)

/-- The component projection followed by the target single-complex identification.
Source: Stacks Project, algebraization.tex, Tag 0A0E, singleton dual Koszul calculation.
(auxiliary; not a blueprint node). -/
theorem projectionTermIso_hom (L : ringedSiteComplex R) (p q : ℤ) (h : p + q = 0) :
    (projectionTermIso R L p q h).hom =
      homComplexπ L (ringedSiteRingComplex R) q p 0 h ≫
        SheafOfModules.homObjMap (R := R) (𝟙 _)
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0
            (SheafOfModules.unit
              ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))).hom := rfl

/-- The finite dual projection is the component of precomposition, then projection.
Source: Stacks Project, algebraization.tex, Tag 0A0E, singleton dual Koszul calculation.
(auxiliary; not a blueprint node). -/
theorem dualFactorTerm_hom (m : ℕ) (q : ℤ) :
    (dualFactorTerm R a m q).hom =
      ((((homComplexFunctor (R := R)).flip.obj (ringedSiteRingComplex R)).map
        (singletonRemoveUnit R a m).inv.op).f q) ≫
      (projectionTermIso R (ringedKoszulFactor R ⟨a.val, a.property⟩ m)
        (-q) q (neg_add_cancel q)).hom := rfl

/-- Degree-zero dual evaluation uses precomposition by the specified double-term inverse.
Source: Stacks Project, algebraization.tex, Tag 0A0E, singleton dual Koszul calculation.
(auxiliary; not a blueprint node). -/
theorem dualZeroTerm_hom (m : ℕ) :
    (dualZeroTerm R a m).hom =
      (dualFactorTerm R a m 0).hom ≫
        SheafOfModules.homObjMap (R := R)
          (HomologicalComplex.doubleXIso₀
            ((ringedKoszulScalar R ⟨a.val, a.property⟩) ^ (m + 1)).asHom
            zeroOneRel).inv (𝟙 _) ≫
          (SheafOfModules.homObjUnitIso (R := R) (SheafOfModules.unit _)).hom := rfl

/-- Degree-minus-one dual evaluation uses the other specified double-term inverse.
Source: Stacks Project, algebraization.tex, Tag 0A0E, singleton dual Koszul calculation.
(auxiliary; not a blueprint node). -/
theorem dualNegOneTerm_hom (m : ℕ) :
    (dualNegOneTerm R a m).hom =
      (dualFactorTerm R a m (-1)).hom ≫
        SheafOfModules.homObjMap (R := R)
          (HomologicalComplex.doubleXIso₁
            ((ringedKoszulScalar R ⟨a.val, a.property⟩) ^ (m + 1)).asHom
            zeroOneRel (by decide)).inv (𝟙 _) ≫
          (SheafOfModules.homObjUnitIso (R := R) (SheafOfModules.unit _)).hom := rfl

end FiniteTerms

end CategoryTheory.PrincipalKoszulDualTerms
