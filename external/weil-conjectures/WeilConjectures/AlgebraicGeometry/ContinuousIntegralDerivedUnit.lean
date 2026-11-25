/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact

/-! # Compatibility of the exact scalar extension unit with its derived adjunction -/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem transported_unit
    {A B : Type*} [Category A] [Category B]
    {L L' : A ⥤ B} {U : B ⥤ A} (ad : L ⊣ U) (mixed : L' ⊣ U)
    {X Y P T : A} (q : X ≅ Y) (p : P ≅ T) (t : U.obj (L.obj X) ≅ T)
    (a : Y ⟶ P) (h : X ⟶ T)
    (ha : a ≫ p.hom = q.inv ≫ h) (hh : ad.unit.app X ≫ t.hom = h) :
    a ≫ (p ≪≫ t.symm ≪≫ (L ⋙ U).mapIso q ≪≫
      U.mapIso ((ad.leftAdjointUniq mixed).app Y)).hom = mixed.unit.app Y := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ha]
  rw [← hh]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← ad.unit.naturality_assoc q.hom]
  simp only [Functor.id_map, Iso.inv_hom_id_assoc]
  exact Adjunction.unit_leftAdjointUniq_hom_app ad mixed Y

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The levelwise extension unit agrees with the specified derived extension unit.
Source: Bhatt--Scholze, Lemma 6.8.2; exact-functor derived adjunction compatibility.
(auxiliary; not a blueprint node).

Proof. Exactness gives the adjunction on levelwise derived functors. On the image
of C in the homotopy category its unit factors through the two exact-functor
comparison isomorphisms as the quotient image of the complex adjunction unit.
The natural isomorphism quotient ⋙ Qh ≅ Q transports this equation to Q(C).
Finally, uniqueness of left adjoints to the same exact restriction identifies
the levelwise left adjoint with the specified left derived extension, compatibly
with their units. Compose these comparisons to obtain the asserted isomorphism.
No colimit, bound, constructibility or pushforward occurs in this compatibility. -/
theorem integralScalar_derivedUnit_complex (X : Scheme.{u})
    (C : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)) ℤ) :
    ∃ e : DerivedCategory.Q.obj
        (((Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
              (coefficientMap (integralScalarMap ℓ E) X)).mapHomologicalComplex (.up ℤ)).obj
          (((Mod.extendScalars
            (coefficientMap (integralScalarMap ℓ E) X)).mapHomologicalComplex (.up ℤ)).obj C)) ≅
        ((Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (coefficientMap (integralScalarMap ℓ E) X)).mapDerivedCategory).obj
          ((integralScalarExtension ℓ E X).obj (DerivedCategory.Q.obj C)),
      DerivedCategory.Q.map
          (((Mod.extendRestrictAdjunction
            (coefficientMap (integralScalarMap ℓ E) X)).mapHomologicalComplex
            (.up ℤ)).unit.app C) ≫ e.hom =
        (Mod.derivedExtendMapDerivedCategoryAdjunction
          (coefficientMap (integralScalarMap ℓ E) X)).unit.app (DerivedCategory.Q.obj C) := by
  let φ := coefficientMap (integralScalarMap ℓ E) X
  let L := Mod.extendScalars φ
  let U := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) φ
  let adj := Mod.extendRestrictAdjunction φ
  let ad := adj.mapDerivedCategoryAdjunction
  let mixed := Mod.derivedExtendMapDerivedCategoryAdjunction φ
  let hC := (HomotopyCategory.quotient _ (.up ℤ)).obj C
  let P := (U.mapHomologicalComplex (.up ℤ)).obj
    ((L.mapHomologicalComplex (.up ℤ)).obj C)
  let qC := (DerivedCategory.quotientCompQhIso _).app C
  let qP := (DerivedCategory.quotientCompQhIso _).app P
  let t := U.mapDerivedCategory.mapIso (L.mapDerivedCategoryFactorsh.app hC) ≪≫
    U.mapDerivedCategoryFactorsh.app ((L.mapHomotopyCategory (.up ℤ)).obj hC)
  let b := ad.leftAdjointUniq mixed
  let e := qP.symm ≪≫ t.symm ≪≫
    (L.mapDerivedCategory ⋙ U.mapDerivedCategory).mapIso qC ≪≫
    U.mapDerivedCategory.mapIso (b.app (DerivedCategory.Q.obj C))
  refine ⟨e, ?_⟩
  have hf := adj.mapDerivedCategoryAdjunction_unit_app_fac hC
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient] at hf
  have hq := DerivedCategory.quotientCompQhIso_inv_naturality
    ((adj.mapHomologicalComplex
            (.up ℤ)).unit.app C)
  change DerivedCategory.Q.map ((adj.mapHomologicalComplex
            (.up ℤ)).unit.app C) ≫
    e.hom = mixed.unit.app (DerivedCategory.Q.obj C)
  exact transported_unit ad mixed qC qP.symm t
    (DerivedCategory.Q.map ((adj.mapHomologicalComplex
            (.up ℤ)).unit.app C))
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
      ((adj.mapHomologicalComplex
            (.up ℤ)).unit.app C))) hq hf

end AlgebraicGeometry.ProEtale.CondensedRing
