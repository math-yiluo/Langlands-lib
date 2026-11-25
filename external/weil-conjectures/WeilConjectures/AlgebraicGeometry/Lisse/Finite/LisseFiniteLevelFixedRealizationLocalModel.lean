/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerEtaleDescentData
import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerLocalizedConstantsModel
import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerFixedPullback
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalPullbackComposition

/-! # Local fixed-realization comparison for a finite-level model

## References

* Stacks Project, Tags 099Y, 099Z, 09B1 and 09BV
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard
  pbcDerivedRestrict constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow etaleIsomorphismNormalizationArrow
  lisseTowerAlgebraArrow lisseTowerFixedRealization

/-- The fixed-realization images of the normalized constant model and the supplied etale
complex are locally isomorphic on the model sieve.
-/
theorem lisse_finite_level_fixed_realization_local_model
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (U : Y.ProEt) (n : ℕ)
    (N : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n))))
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (D : DerivedCategory
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))
    (hcomparison : Nonempty ((lisseTowerFixedRealization (U.hom ≫ g) d n).obj
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) U.left).mapDerivedCategory.obj D) ≅
        (adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj N))
    (hmodels : ∃ T : Sieve U, T ∈ ProEt.topology Y U ∧
      ∀ (W : Y.ProEt) (w : W ⟶ U), T w →
        Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj E ≅
          (adicTowerPullback (W.hom ≫ g)
            ((pbcAdicRings X d).obj (op n))).obj N)) :
    ∃ T : Sieve U, T ∈ ProEt.topology Y U ∧
      ∀ (W : Y.ProEt) (w : W ⟶ U), T w →
        Nonempty (
          (lisseTowerFixedRealization (W.hom ≫ g) d n).obj
            ((localProEtaleComparison w.left (lisseTowerEtaleRing d n)).obj
              ((normalizationConstant U.left.smallEtaleTopology).obj E)) ≅
          (lisseTowerFixedRealization (W.hom ≫ g) d n).obj
            ((localProEtaleComparison w.left (lisseTowerEtaleRing d n)).obj D)) := by
  classical
  obtain ⟨e⟩ := hcomparison
  obtain ⟨T, hT, hm⟩ := hmodels
  refine ⟨T, hT, fun W w hw ↦ ?_⟩
  obtain ⟨em⟩ := hm W w hw
  let a := w.left
  let b := U.hom ≫ g
  have hab : a ≫ b = W.hom ≫ g := by
    have h := w.w
    change w.left ≫ U.hom = W.hom ≫ 𝟙 Y at h
    erw [Category.comp_id] at h
    simpa only [a, b, Category.assoc] using congrArg (fun t ↦ t ≫ g) h
  let B := lisseTowerEtaleRing d n
  let F := lisseTowerFixedRealization (W.hom ≫ g) d n
  let C₀ := (normalizationConstant U.left.smallEtaleTopology).obj E
  let K₀ := (localProEtaleComparison a B).obj C₀
  obtain ⟨models⟩ :=
    lisseTower_localized_constants_model (W.hom ≫ g) a (𝟙 W.left) d
  let idD := Functor.mapDerivedCategoryNatIso
      (ProEtale.upperStarId (ModuleCat.{u + 1} B) W.left) ≪≫
    Functor.mapDerivedCategoryIdIso _
  have model : F.obj K₀ ≅ (constantAdicQuotientRealization (W.hom ≫ g) d n).obj E :=
    F.mapIso (idD.app K₀).symm ≪≫ models n E
  let R := (pbcAdicRings X d).obj (op n)
  let RT := (adicTowerInverseImage b).obj R
  let RZ := (adicTowerInverseImage (a ≫ b)).obj R
  let c := (proEtaleRingInverseImageComp a b).symm.app R
  let P := proEtaleRingModulePullback a RT RZ c
  have hc : Iso.refl RZ = proEtaleRingCompositeCoefficients a b R RT RZ
      (Iso.refl RT) c := by
    apply Iso.ext
    change 𝟙 RZ = (proEtaleRingInverseImageComp a b).hom.app R ≫
      (adicTowerInverseImage a).map (𝟙 RT) ≫
        (proEtaleRingInverseImageComp a b).inv.app R
    erw [(adicTowerInverseImage a).map_id RT, Category.id_comp]
    exact (Iso.hom_inv_id_app (proEtaleRingInverseImageComp a b) R).symm
  let comp := (proEtaleCanonicalPullbackComposition_existsUnique a b R RT RZ
    (Iso.refl RT) c (Iso.refl RZ) hc).exists.choose
  let sq := (lisseTower_fixed_sheaf_pullback a b d n).some
  let dsq : (ProEtale.upperStar (ModuleCat.{u + 1} B) a).mapDerivedCategory ⋙
        lisseTowerFixedRealization (a ≫ b) d n ≅
      lisseTowerFixedRealization b d n ⋙ P.mapDerivedCategory :=
    Functor.isoWhiskerLeft _ (lisseTowerFixedRealizationIso (a ≫ b) d n).symm ≪≫
      Functor.mapDerivedCategorySquareIso sq ≪≫
      Functor.isoWhiskerRight (lisseTowerFixedRealizationIso b d n) P.mapDerivedCategory
  let K := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B)
    U.left).mapDerivedCategory.obj D
  have actual : (lisseTowerFixedRealization (a ≫ b) d n).obj
      ((ProEtale.upperStar (ModuleCat.{u + 1} B) a).mapDerivedCategory.obj K) ≅
      (adicTowerPullback (a ≫ b) R).obj N :=
    dsq.app K ≪≫ P.mapDerivedCategory.mapIso e ≪≫ (comp.app N).symm
  rw [hab] at actual
  exact ⟨model ≪≫ em ≪≫ actual.symm⟩

end AlgebraicGeometry.Scheme
