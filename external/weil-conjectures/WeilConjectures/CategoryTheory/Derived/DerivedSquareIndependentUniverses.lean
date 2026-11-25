/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Localization of a square with independent derived-category universes

Source: Stacks Project, Tags 05R7 and 05RU; fully faithful precomposition for localization.
(blueprint: lem-pur-derived-square-independent-universes).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe a av b bv c cv e ev da db dc dd
open CategoryTheory.Functor
namespace CategoryTheory

/-- Lift an ordinary square to specified derived realizations, retaining the given
factorization isomorphisms. The four localizations may have different Hom universes.

Source: Stacks Project, Tags 05R7 and 05RU; the localization universal property.
(blueprint: lem-pur-derived-square-independent-universes).

Proof: paste the four factorization maps with the ordinary square on complexes.
Fully faithful precomposition with the source localization lifts this isomorphism
uniquely. Evaluate the lifting equation at a complex and cancel the two target
factorization maps. This is the required representative equation. -/
theorem exists_derivedSquare_independentUniverses
    {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{da} A]
    {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{db} B]
    {C : Type c} [Category.{cv} C] [Abelian C] [HasDerivedCategory.{dc} C]
    {D : Type e} [Category.{ev} D] [Abelian D] [HasDerivedCategory.{dd} D]
    (F : A ⥤ B) (eA : A ⥤ C) (eB : B ⥤ D) (Fl : C ⥤ D)
    [F.Additive] [eA.Additive] [eB.Additive] [Fl.Additive]
    (FD : DerivedCategory A ⥤ DerivedCategory B)
    (EA : DerivedCategory A ⥤ DerivedCategory C)
    (EB : DerivedCategory B ⥤ DerivedCategory D)
    (FlD : DerivedCategory C ⥤ DerivedCategory D)
    (φF : DerivedCategory.Q ⋙ FD ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (φA : DerivedCategory.Q ⋙ EA ≅ eA.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (φB : DerivedCategory.Q ⋙ EB ≅ eB.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (φl : DerivedCategory.Q ⋙ FlD ≅ Fl.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α : F ⋙ eB ≅ eA ⋙ Fl) :
    ∃ δ : FD ⋙ EB ≅ EA ⋙ FlD, ∀ P,
      δ.hom.app (DerivedCategory.Q.obj P) ≫
        FlD.map (φA.hom.app P) ≫
        φl.hom.app ((eA.mapHomologicalComplex (.up ℤ)).obj P) =
      EB.map (φF.hom.app P) ≫
        φB.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex α (.up ℤ)).hom.app P) := by
  let ψF : DerivedCategory.Q ⋙ (FD ⋙ EB) ≅
      F.mapHomologicalComplex (.up ℤ) ⋙
        eB.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight φF EB ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ φB
  let ψl : DerivedCategory.Q ⋙ (EA ⋙ FlD) ≅
      eA.mapHomologicalComplex (.up ℤ) ⋙
        Fl.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight φA FlD ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ φl
  let γ := Functor.mapHomologicalComplexCompIso α (.up ℤ)
  let τ := ψF ≪≫ isoWhiskerRight γ DerivedCategory.Q ≪≫ ψl.symm
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) (DerivedCategory D)
  let δ := ff.preimageIso τ
  refine ⟨δ, ?_⟩
  intro P
  have hd : δ.hom.app (DerivedCategory.Q.obj P) = τ.hom.app P := by
    exact congr_app (ff.map_preimage τ.hom) P
  rw [hd]
  dsimp only [τ, ψF, ψl, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    isoWhiskerRight_inv, isoWhiskerLeft_inv, whiskerRight_app, whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.id_comp, Category.comp_id, Category.assoc,
    ← FlD.map_comp_assoc, Iso.inv_hom_id_app]
  erw [FlD.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
  rfl

end CategoryTheory
