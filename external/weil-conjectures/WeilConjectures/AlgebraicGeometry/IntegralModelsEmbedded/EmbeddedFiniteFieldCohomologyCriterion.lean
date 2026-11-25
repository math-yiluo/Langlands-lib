/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.EmbeddedFiniteCoefficientRealization
import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.EmbeddedFiniteFieldPresentation
import WeilConjectures.AlgebraicGeometry.Constant.ConstantFieldTorBounds
import all WeilConjectures.CategoryTheory.ProEtaleCoefficients.CoefficientTorFlatModelSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory

/-! # Constructible finite Tor complexes over an embedded constant finite field

## References

* Stacks Tags 03ET, 00YV and 06YQ
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsEmbedded

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] integralModel_coefficientMonObj in
/-- For any complex over an embedded constant finite field, constructible homology
and finite Tor amplitude mean exactly intrinsically constructible bounded homology
under the specified scalar realization. No integral reduction or etale origin occurs. -/
theorem finiteFieldCohomologyCriterion
    (X : Scheme.{u}) [IsNoetherian X] (A : Type) [Field A]
    [TopologicalSpace A] [IsTopologicalRing A] [Finite A] [DiscreteTopology A]
    (B : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (discreteObj A) X))) :
    letI : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
      CategoryTheory.siteAbelianHasSheafify.{u + 1, u, u + 1} _
    letI : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
      CategoryTheory.siteAbelianWEqualsLocallyBijective.{u + 1, u, u + 1} _
    ((∀ i : ℤ, IsConstantModelConstructible (discreteObj A) X
        ((DerivedCategory.homologyFunctor.{u + 1} _ i).obj B)) ∧
      _root_.DerivedCategory.finiteTorAmplitude _ B) ↔
    ((∀ i : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf X (ULift.{u, 0} A)
        ((@DerivedCategory.homologyFunctor
          (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X (ULift.{u, 0} A)))
          _ _ (HasDerivedCategory.standard _) i).obj ((finiteRealization X A).obj B))) ∧
      ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, i < a ∨ b < i →
        IsZero ((@DerivedCategory.homologyFunctor
          (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X (ULift.{u, 0} A)))
          _ _ (HasDerivedCategory.standard _) i).obj ((finiteRealization X A).obj B))) := by
  classical
  let : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianHasSheafify.{u + 1, u, u + 1} _
  let : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianWEqualsLocallyBijective.{u + 1, u, u + 1} _
  let R := ConstantCompletion.constant
    (Scheme.coefficientProEtaleModelTopology.{u, u} X) (ULift.{u + 1, 0} A)
  let := SheafOfModules.monoidalCategory R
  let := CategoryTheory.moduleSymmetric R
  let := CategoryTheory.moduleClosed R
  let := CategoryTheory.modulePreadditive R
  let := CategoryTheory.moduleGrothendieck R
  let := CategoryTheory.flatResolution R
  let : HasDerivedCategory (ConstantCompletion.Mod R) := HasDerivedCategory.standard _
  let : HasDerivedCategory (Scheme.proEtaleRingModules X
      (Scheme.proEtaleConstantRing X (ULift.{u, 0} A))) := HasDerivedCategory.standard _
  obtain ⟨E, H, hE, hH, ⟨hmon⟩, ⟨comp⟩, hc⟩ := finiteFieldPresentation X A
  let := hE
  let := hH
  let := hmon
  let := Functor.preservesFlat_of_isEquivalence E.functor
  let K := E.functor.mapDerivedCategory.obj B
  let L := (finiteRealization X A).obj B
  have e (i : ℤ) :
      E.functor.obj ((DerivedCategory.homologyFunctor _ i).obj B) ≅
        H.functor.obj ((@DerivedCategory.homologyFunctor
          (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X (ULift.{u, 0} A)))
          _ _ (HasDerivedCategory.standard _) i).obj L) :=
    (E.functor.mapDerivedCategoryHomologyFunctorIso i).app B ≪≫
      (coefficientModelCohomology R i).mapIso (comp.app B).symm ≪≫
        ((H.functor.mapDerivedCategoryHomologyFunctorIso i).app L).symm
  have hzero (i : ℤ) :
      IsZero ((coefficientModelCohomology R i).obj K) ↔
        IsZero ((@DerivedCategory.homologyFunctor
          (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X (ULift.{u, 0} A)))
          _ _ (HasDerivedCategory.standard _) i).obj L) := by
    let c := (coefficientModelCohomology R i).mapIso (comp.app B).symm ≪≫
      ((H.functor.mapDerivedCategoryHomologyFunctorIso i).app L).symm
    constructor
    · intro h
      apply (IsZero.iff_id_eq_zero _).2
      apply H.functor.map_injective
      rw [H.functor.map_id, H.functor.map_zero]
      exact (IsZero.iff_id_eq_zero _).1 (h.of_iso c.symm)
    · intro h
      exact (H.functor.map_isZero h).of_iso c
  have ht : _root_.DerivedCategory.finiteTorAmplitude _ B ↔
      Scheme.HasFiniteCoefficientProEtaleTorAmplitude.{u, u} X (ULift.{u + 1, 0} A) K := by
    constructor
    · rintro ⟨a, b, h⟩
      refine ⟨min a b, b,
        (CategoryTheory.nativeTor_iff R K (min a b) b (min_le_right a b)).mp ?_⟩
      exact DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj E.functor
        (h.mono (min_le_left a b) le_rfl)
    · rintro ⟨a, b, h⟩
      refine ⟨a, b, ?_⟩
      exact (DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff
        E.functor a b B).mp ((CategoryTheory.nativeTor_iff R K a b h.1).mpr h)
  refine and_congr (forall_congr' fun i ↦ hc _ _ (e i)) ?_
  refine ht.trans ((Scheme.constant_field_finite_tor_amplitude_iff.{u, u}
    X (ULift.{u + 1, 0} A) K).trans ?_)
  exact exists_congr fun a ↦ exists_congr fun b ↦
    and_congr Iff.rfl (forall_congr' fun i ↦ imp_congr_right fun _ ↦ hzero i)

end AlgebraicGeometry.ProEtale.IntegralModelsEmbedded
