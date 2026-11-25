/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PolynomialChartFibreStalk
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.FinitePresentationStalkLocalizationModel
import WeilConjectures.AlgebraicGeometry.PolynomialChartClosedFiberModuleFlat
import WeilConjectures.RingTheory.FlatOfFlatClosedFiber

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Algebraic stalk-tower criterion after the finite-presentation and fibre identifications.
Apply the affine stalk localization-model theorem to the projection and to its
composite with the chart. Stalk-map composition gives the local scalar tower.
Base stalk flatness and the open-immersion stalk isomorphism give base flatness
of the source stalk; the factorization identifies this with the composite tower.
The closed-fibre module comparison supplies the fibre hypothesis. Apply the
local criterion with the source stalk as its own finitely presented nonzero module;
its second conclusion is chart flatness. Scheme stalk maps are automatically local.
Source: Stacks Project, Tags 00R7 and 00RH.
(blueprint: lem-sbc-polynomial-chart-stalk-flat-comparison-reverse-aux-ring-bridge) -/
theorem polynomial_chart_stalk_flat_comparison_reverse_ring_bridge
    {X T : Scheme.{u}} [IsAffine T] (f : X ⟶ T)
    [Flat f] [LocallyOfFinitePresentation f]
    (U : X.Opens) [IsAffine U.toScheme] (n : ℕ)
    (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T)
    [LocallyOfFinitePresentation e]
    (he : e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f)
    (x : U.toScheme)
    (hbase : (f.stalkMap (U.ι x)).hom.Flat)
    (hfibre : (PolynomialChart.stalkMap f U n e he x).Flat) :
    (e.stalkMap x).hom.Flat ∧ IsLocalHom (e.stalkMap x).hom := by
  let p := (AffineSpace (ULift.{u} (Fin n)) T ↘ T)
  let R := T.presheaf.stalk (p (e x))
  let S := (AffineSpace (ULift.{u} (Fin n)) T).presheaf.stalk (e x)
  let B := U.toScheme.presheaf.stalk x
  let α : R →+* S := (p.stalkMap (e x)).hom
  let β : S →+* B := (e.stalkMap x).hom
  let : Algebra R S := α.toAlgebra
  let : Algebra S B := β.toAlgebra
  let : Algebra R B := (β.comp α).toAlgebra
  have : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsLocalHom (algebraMap R S) := inferInstanceAs (IsLocalHom α)
  have : IsLocalHom (algebraMap S B) := inferInstanceAs (IsLocalHom β)
  obtain ⟨P, algRP, algPS, towerRPS, fpP, W, locS⟩ :=
    exists_finitePresentation_stalk_localization_model p (e x)
  have hmodel := exists_finitePresentation_stalk_localization_model (e ≫ p) x
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp] at hmodel
  obtain ⟨Q, algRQ, algQB, towerRQB, fpQ, V, locB⟩ := hmodel
  let : Algebra R Q := algRQ
  let : Algebra Q B := algQB
  have : IsScalarTower R Q B := towerRQB
  have : Algebra.FinitePresentation R Q := fpQ
  have : IsLocalization V B := locB
  have hflat : ((U.ι ≫ f).stalkMap x).hom.Flat := by
    rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
    exact hbase.comp (Flat.stalkMap U.ι x)
  rw [← he, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp] at hflat
  have : Module.Flat R B := hflat
  have hf := polynomial_chart_closedFiber_module_flat f U n e he x hfibre
  have hresult := Module.flat_of_flat_closedFiber R S B B P Q W V hf
  exact ⟨hresult.2, inferInstance⟩

/-- Local criterion step for the reverse polynomial-chart flatness comparison.
The proof is the Stacks Project local flatness criterion (Tags 00R7 and 00RH):
write the relevant stalks as essentially finitely presented local algebras over
the base stalk, use flatness over the base and flatness of the closed fibre,
and transport flatness through the canonical fibre-stalk identification.
(blueprint: lem-sbc-polynomial-chart-stalk-flat-comparison-reverse-aux) -/
theorem polynomial_chart_stalk_flat_comparison_reverse_aux
    {X T : Scheme.{u}} [IsAffine T] (f : X ⟶ T)
    [Flat f] [LocallyOfFinitePresentation f]
    (U : X.Opens) [IsAffine U.toScheme] (n : ℕ)
    (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T)
    [LocallyOfFinitePresentation e]
    (he : e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f)
    (x : U.toScheme)
    (hbase : (f.stalkMap (U.ι x)).hom.Flat)
    (hfibre : (PolynomialChart.stalkMap f U n e he x).Flat) :
    (e.stalkMap x).hom.Flat := by
  exact (polynomial_chart_stalk_flat_comparison_reverse_ring_bridge
    f U n e he x hbase hfibre).1

end AlgebraicGeometry

