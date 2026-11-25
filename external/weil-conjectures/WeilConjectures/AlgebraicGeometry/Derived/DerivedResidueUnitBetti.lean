/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
import WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-! # Degree-zero dimension of the derived residue of the structure sheaf

Source: Stacks Project, Tags 06YD and 06YJ; Tag 0E62, local argument.
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The flat single complex on the structure sheaf computes its derived residue pullback.
Source: Stacks Project, Tags 06YD and 06YJ. This is the flat-single component of
(blueprint: lem-sc-derived-residue-unit-betti). -/
private theorem residue_unit_single_iso (S : Scheme.{u}) (s : S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (S.residueField s)).toRingedSpace))] :
    Nonempty ((derivedPullback (S.fromSpecResidueField s)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
          (SheafOfModules.unit S.ringCatSheaf)) ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) 0).obj
          (SheafOfModules.unit (Spec (S.residueField s)).ringCatSheaf)) := by
  let T := Spec (S.residueField s)
  let g := S.fromSpecResidueField s
  let A := SheafOfModules.{u} (moduleRings S.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings T.toRingedSpace)
  let M := SheafOfModules.unit S.ringCatSheaf
  let P := (CochainComplex.singleFunctor A (0 : ℤ)).obj M
  let := SheafOfModules.monoidalCategory S.sheaf
  obtain ⟨⟨hpreadd⟩, _⟩ := SheafOfModules.tensorClosed S.sheaf
  let := hpreadd
  have hM : SheafOfModules.IsFlat M := by
    change exactFunctor A A (MonoidalCategory.tensorRight (𝟙_ A))
    exact (exactFunctor A A).prop_of_iso (MonoidalCategory.rightUnitorNatIso A).symm
      (by rw [exactFunctor_iff]; exact ⟨inferInstance, inferInstance⟩)
  have hb : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i) := by
    refine ⟨0, fun i hi ↦ ?_⟩
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have hf : ∀ i : ℤ, SheafOfModules.IsFlat (P.X i) := by
    intro i
    by_cases hi : i = 0
    · subst i
      let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M
      exact (exactFunctor _ _).prop_of_iso
        ((MonoidalCategory.curriedTensor A).flip.mapIso e.symm) hM
    · exact (ObjectProperty.flat_of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)).2
  obtain ⟨F, hF, _, hFadd, _, _, ⟨e, _⟩⟩ := flatComplexDerivedPullback g P hb hf
  let := hFadd
  let eFM : F.obj M ≅ SheafOfModules.unit T.ringCatSheaf :=
    eqToIso (hF M) ≪≫
      ((Modules.nonempty_tensorPullbackAdjunction g).some.leftAdjointUniq
        (Modules.pullbackPushforwardAdjunction g)).app M ≪≫ Modules.pullbackObjUnitIso g
  exact ⟨(derivedPullback g).mapIso
    ((DerivedCategory.singleFunctorIsoCompQ A 0).app M ≪≫
      ((DerivedCategory.quotientCompQhIso A).app P).symm) ≪≫ e.symm ≪≫
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app P) ≪≫
    (DerivedCategory.quotientCompQhIso B).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ B 0).app (F.obj M)).symm ≪≫
    (DerivedCategory.singleFunctor B 0).mapIso eFM⟩

/-- An invertible degree-zero residue map from the structure sheaf forces Betti number one.
Source: Stacks Project, Tag 0E62, local argument, using Tags 06YD and 06YJ.
(blueprint: lem-sc-derived-residue-unit-betti).

Proof: The structure sheaf is flat, so its single complex computes its derived pullback
termwise. Ordinary pullback of the structure sheaf is the structure sheaf. Taking H^0,
global sections on Spec κ(s), and restriction of scalars through ΓSpecIso identifies the
source fibre cohomology with κ(s). The given isomorphism identifies the target with the
same one-dimensional vector space. No perfectness or vanishing in other degrees is used. -/
theorem derivedFiberBetti_zero_eq_one_of_unit_iso (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ x : S, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (S.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory S)
    (a : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
        (SheafOfModules.unit S.ringCatSheaf) ⟶ E) (s : S)
    (ha : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) 0).map
        ((derivedPullback (S.fromSpecResidueField s)).map a))) :
    derivedFiberBetti S E 0 s = 1 := by
  let := ha
  let T := Spec (S.residueField s)
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings T.toRingedSpace)) (0 : ℤ)
  let V := SheafOfModules.evaluation (moduleRings T.toRingedSpace) (Opposite.op ⊤)
  let R := ModuleCat.restrictScalars (ΓSpecIso (S.residueField s)).inv.hom
  obtain ⟨e⟩ := residue_unit_single_iso S s
  let eH := (asIso (H.map ((derivedPullback (S.fromSpecResidueField s)).map a))).symm ≪≫
    H.mapIso e ≪≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso _ (0 : ℤ)).app _
  let eV : derivedFiberCohomology S E 0 s ≅ ModuleCat.of (S.residueField s)
      (S.residueField s) :=
    R.mapIso (V.mapIso eH) ≪≫
      ModuleCat.restrictScalarsIsoOfEquiv
        (ΓSpecIso (S.residueField s)).symm.commRingCatIsoToRingEquiv
  exact eV.toLinearEquiv.finrank_eq.trans (Module.finrank_self _)

end AlgebraicGeometry.Scheme
