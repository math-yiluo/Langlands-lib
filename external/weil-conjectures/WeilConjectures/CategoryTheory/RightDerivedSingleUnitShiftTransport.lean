/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.RightDerivedSingleUnitHomologyComparison
public import Mathlib.Algebra.Homology.Localization
import WeilConjectures.CategoryTheory.SingleQuotientInverseShift
import WeilConjectures.CategoryTheory.MappedSingleInverseShift
import all Mathlib.Algebra.Homology.Localization

/-!
# Canonical single-complex shift comparisons

These comparisons isolate the source and unit transport calculations used by
`rightDerivedFunctorPlusUnit_canonical_single_shift`.
-/

@[expose] public section

universe uB vB uC vC
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

variable {B : Type uB} [Category.{vB} B] [Abelian B] [EnoughInjectives B]
  {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory C]
  (G : B ⥤ C) [G.Additive]

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Shift transport of the derived unit on a single object.

Source: Stacks Project, derived.tex, Tag 015J, proof remark (1), and the
canonical single-functor, quotient and homology shift comparisons.
(blueprint: lem-pc-right-derived-single-unit-shift-transport)

Proof: Use the canonical shift isomorphism from single_n X to single_0 X[-n]
in the bounded-below homotopy category. Naturality of rightDerivedFunctorPlusUnith
along this isomorphism, followed by its NatTrans.CommShift equation at -n, moves
the unit to degree zero. The canonical single/quotient identification e converts
the target to the derived single object; its naturality identifies this with the
first factor of c. The right-derived commShift comparison gives the second
factor of c. Apply H^n and use naturality of H₀.shiftIso to move the unit through
the homology shift comparison, giving the third factor of c. On the source,
mapHomotopyCategoryPlusSingleFunctorQhObjIso identifies the mapped single object
with the single object on G(X); compatibility of singleMapHomologicalComplex
with shifts gives d. The degree-zero unit, with its single/quotient identifications,
is precisely rightDerivedPlusSingleUnit. Thus the two paths in this naturality
square are the displayed composites. This uses no cycles projection and no
classical derived-functor comparison. -/
theorem rightDerivedPlusSingleUnit_shift_transport (X : B) (n : ℕ) :
    let S : CochainComplex.Plus B :=
      ⟨(CochainComplex.singleFunctor B (n : ℤ)).obj X, n, inferInstance⟩
    let e : (DerivedCategory.Plus.singleFunctor B n).obj X ≅
        DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient B).obj S) :=
      DerivedCategory.Plus.ι.preimageIso
        ((DerivedCategory.singleFunctorIsoCompQ B n).app X ≪≫
          (DerivedCategory.quotientCompQhIso B).symm.app _)
    let GS := G.mapCochainComplexPlus.obj S
    let H₀ := DerivedCategory.Plus.homologyFunctor C 0
    let RG := G.rightDerivedFunctorPlus
    let c := Functor.isoWhiskerRight
      ((DerivedCategory.Plus.singleFunctors B).shiftIso (-(n : ℤ)) n 0 (by simp)).symm
      (RG ⋙ H₀.shift (n : ℤ)) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor B 0)
        (Functor.isoWhiskerRight (RG.commShiftIso (-(n : ℤ))) (H₀.shift (n : ℤ))) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor B 0 ⋙ RG)
        (H₀.shiftIso (-(n : ℤ)) (n : ℤ) 0 (by ring))
    let d := Functor.isoWhiskerRight
      ((DerivedCategory.Plus.singleFunctors C).shiftIso (-(n : ℤ)) n 0 (by simp)).symm
      (H₀.shift (n : ℤ)) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C 0)
        (H₀.shiftIso (-(n : ℤ)) (n : ℤ) 0 (by ring))
    (DerivedCategory.Plus.homologyFunctor C n).map
      (G.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient B).obj S)) ≫
      (DerivedCategory.Plus.homologyFunctor C n).map (G.rightDerivedFunctorPlus.map e.inv) ≫
      c.hom.app X =
    (DerivedCategory.Plus.homologyFunctor C n).map
      (G.mapHomotopyCategoryPlusSingleFunctorQhObjIso n X).hom ≫
      d.hom.app (G.obj X) ≫ H₀.map (G.rightDerivedPlusSingleUnit X) := by
  intro S e GS H₀ RG c d
  clear GS
  dsimp only [S, e, H₀, RG, c, d]
  let K₀ := (HomotopyCategory.Plus.singleFunctor B 0).obj X
  let h := ((HomotopyCategory.Plus.singleFunctors B).shiftIso
    (-(n : ℤ)) n 0 (by simp)).inv.app X
  let eₙ : (DerivedCategory.Plus.singleFunctor B n).obj X ≅
      DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor B n).obj X) :=
    DerivedCategory.Plus.ι.preimageIso
      ((DerivedCategory.singleFunctorIsoCompQ B n).app X ≪≫
        (DerivedCategory.quotientCompQhIso B).symm.app _)
  let sB := ((DerivedCategory.Plus.singleFunctors B).shiftIso
    (-(n : ℤ)) n 0 (by simp)).inv.app X
  let sC := ((DerivedCategory.Plus.singleFunctors C).shiftIso
    (-(n : ℤ)) n 0 (by simp)).inv.app (G.obj X)
  let F := G.rightDerivedFunctorPlus
  let U := G.rightDerivedFunctorPlusUnith
  have ht := single_quotient_inverse_shift X n
  have hs := mapped_single_inverse_shift G X n
  have hu := U.naturality h
  have hc := NatTrans.shift_app_comm U (-(n : ℤ)) K₀
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj, Category.assoc] at hc
  simp only [Functor.comp_map, Functor.comp_obj] at hu
  have hd : U.app ((HomotopyCategory.Plus.singleFunctor B n).obj X) ≫
      F.map eₙ.inv ≫ F.map sB ≫
        (F.commShiftIso (-(n : ℤ))).hom.app
          ((DerivedCategory.Plus.singleFunctor B 0).obj X) =
      (G.mapHomotopyCategoryPlusSingleFunctorQhObjIso n X).hom ≫ sC ≫
        (G.rightDerivedPlusSingleUnit X)⟦-(n : ℤ)⟧' := by
    rw [← F.map_comp_assoc, ht]
    simp only [F.map_comp, Category.assoc]
    rw [F.commShiftIso_hom_naturality]
    erw [← reassoc_of% hu]
    erw [← reassoc_of% hc]
    erw [reassoc_of% hs]
    simp only [rightDerivedPlusSingleUnit, Functor.map_comp]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_assoc]
    rfl
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, Iso.symm_hom,
    Functor.comp_map, Category.assoc]
  change (DerivedCategory.Plus.homologyFunctor C n).map (U.app _) ≫
    (DerivedCategory.Plus.homologyFunctor C n).map (F.map eₙ.inv) ≫
    (DerivedCategory.Plus.homologyFunctor C n).map (F.map sB) ≫
    (DerivedCategory.Plus.homologyFunctor C n).map
      ((F.commShiftIso (-(n : ℤ))).hom.app _) ≫ _ =
    (DerivedCategory.Plus.homologyFunctor C n).map
      (G.mapHomotopyCategoryPlusSingleFunctorQhObjIso n X).hom ≫
    (DerivedCategory.Plus.homologyFunctor C n).map sC ≫ _ ≫ _
  simp only [← Functor.map_comp_assoc] at hd ⊢
  rw [hd]
  simp only [Functor.map_comp, Category.assoc]
  exact congrArg (fun f ↦
    (DerivedCategory.Plus.homologyFunctor C n).map
      (G.mapHomotopyCategoryPlusSingleFunctorQhObjIso n X).hom ≫
    (DerivedCategory.Plus.homologyFunctor C n).map sC ≫ f)
    (((DerivedCategory.Plus.homologyFunctor C 0).shiftIso
      (-(n : ℤ)) (n : ℤ) 0 (by ring)).hom.naturality (G.rightDerivedPlusSingleUnit X))

end CategoryTheory.Functor
