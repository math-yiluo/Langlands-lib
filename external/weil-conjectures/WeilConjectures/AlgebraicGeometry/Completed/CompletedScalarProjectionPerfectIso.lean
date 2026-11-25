/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedScalarProjectionTensorComparison

/-!
# Perfectness makes the normalized scalar projection invertible

Source: Stacks Project, Tag 0944, and blueprint order 1276.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem derivedRestriction_reflectsIsomorphisms (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    (pbcDerivedRestrict φ).ReflectsIsomorphisms := by
  let := (proEtaleRingRestrictScalars_properties φ).2.2
  refine ⟨fun g hg ↦ ?_⟩
  change IsIso ((pbcRestrict φ).mapDerivedCategory.map g) at hg
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso ((pbcRestrict φ).map ((DerivedCategory.homologyFunctor _ n).map g)) :=
    (NatIso.isIso_map_iff ((pbcRestrict φ).mapDerivedCategoryHomologyFunctorIso n) g).2
      (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ (pbcRestrict φ)

/-- A scalar projection whose coefficient unit is the positive quotient is invertible.
Source: Stacks Project, Tag 0944; blueprint order 1276, finite-level projection formula.
(blueprint: lem-pbc-completed-scalar-projection-perfect-iso).
Proof: the scalar-to-tensor comparison identifies the projection after two exact
restrictions of scalars with the tensor projection for the nth quotient. That quotient
is site-perfect by reductionMap_isIso, so perfect_projection_formula makes the tensor
projection invertible. Cancel the comparison isomorphisms. Exact scalar restriction
reflects derived isomorphisms because it commutes with homology and reflects ordinary
module-sheaf isomorphisms. Reflect twice to recover invertibility of the scalar mate. -/
theorem completedScalarProjectionPerfectIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) [IsIso (completedCoefficientMap f d)]
    (SY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (SX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (φY : pbcAdicCompletion Y d ⟶ SY) (φX : pbcAdicCompletion X d ⟶ SX)
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SY ≅ SX)
    (hc : completedCoefficientMap f d ≫ φX =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map φY ≫ c.hom)
    (F : pbcModules X (pbcAdicCompletion X d) ⥤ pbcModules Y (pbcAdicCompletion Y d))
    [F.Additive]
    (hF : F = proEtaleRingModuleDirectImage f (pbcAdicCompletion Y d)
      (pbcAdicCompletion X d) (asIso (completedCoefficientMap f d)))
    (G : pbcModules X SX ⥤ pbcModules Y SY) [G.Additive]
    (hG : G = proEtaleRingModuleDirectImage f SY SX c)
    (i : pbcRestrict φX ⋙ F ≅
      G ⋙ pbcRestrict φY)
    (hi : ∀ (M : pbcModules X SX) (U : Y.ProEtᵒᵖ),
      HEq (fun x ↦ (i.hom.app M).val.app U x)
        (fun x : ((proEtaleRingModuleDirectImage f SY SX c).obj M).val.obj U ↦ x))
    (e : pbcDerivedRestrict φX ⋙ F.rightDerivedFunctor ≅
      G.rightDerivedFunctor ⋙ pbcDerivedRestrict φY)
    (he : ∀ C : CochainComplex (pbcModules X SX) ℤ,
      F.rightDerivedFunctorUnitQ
          (((pbcRestrict φX).mapHomologicalComplex (.up ℤ)).obj C) ≫
        F.rightDerivedFunctor.map
          ((pbcRestrict φX).mapDerivedCategoryFactors.inv.app C) ≫
        e.hom.app (DerivedCategory.Q.obj C) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex i.hom (.up ℤ)).app C) ≫
        (pbcRestrict φY).mapDerivedCategoryFactors.inv.app
          ((G.mapHomologicalComplex (.up ℤ)).obj C) ≫
        (pbcDerivedRestrict φY).map (G.rightDerivedFunctorUnitQ C))
    (n : ℕ)
    (r : (DerivedCategory.singleFunctor (PerfectProjection.modules d Y) 0).obj
        ((pbcRestrict ((pbcCompletedComparison Y d).hom ≫ φY)).obj
          (SheafOfModules.unit (reductionModuleRing Y SY))) ≅ PerfectProjection.quotient d Y n)
    (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d))) :
    IsIso (((pbcDerivedScalarAdjunction φY).homEquiv _ _).symm
      (F.rightDerivedFunctor.map ((pbcDerivedScalarAdjunction φX).unit.app K) ≫
        e.hom.app ((pbcDerivedExtend φX).obj K))) := by
  let R := pbcDerivedRestrict φY
  let C := pbcDerivedRestrict (pbcCompletedComparison Y d).hom
  let := derivedRestriction_reflectsIsomorphisms Y φY
  let := derivedRestriction_reflectsIsomorphisms Y (pbcCompletedComparison Y d).hom
  let π := ((pbcDerivedScalarAdjunction φY).homEquiv _ _).symm
    (F.rightDerivedFunctor.map ((pbcDerivedScalarAdjunction φX).unit.app K) ≫
      e.hom.app ((pbcDerivedExtend φX).obj K))
  obtain ⟨aY, aX, s, t, ht⟩ := completedScalarProjectionTensorComparison f d
    SY SX φY φX c hc F hF G hG i hi e he (PerfectProjection.quotient d Y n) r K
  let K₀ := (pbcDerivedRestrict (pbcCompletedComparison X d).hom).obj K
  have hp : IsIso (PerfectProjection.projection d f aY aX K₀
      (PerfectProjection.quotient d Y n)) :=
    (PerfectProjection.perfect_projection_formula d f aY aX K₀).2.2.2
      (PerfectProjection.quotient d Y n)
      (PerfectProjection.reductionMap_isIso d f aY aX K₀ n).1
  have : IsIso (C.map (R.map π) ≫ t.hom) := by
    have ht' : C.map (R.map π) ≫ t.hom =
        s.hom ≫ PerfectProjection.projection d f aY aX K₀
          (PerfectProjection.quotient d Y n) := ht
    exact ht'.symm ▸ (inferInstance : IsIso
      (s.hom ≫ PerfectProjection.projection d f aY aX K₀
        (PerfectProjection.quotient d Y n)))
  have : IsIso (C.map (R.map π)) := IsIso.of_isIso_comp_right _ t.hom
  have : IsIso (R.map π) := isIso_of_reflects_iso _ C
  exact isIso_of_reflects_iso _ R

end AlgebraicGeometry.Scheme
