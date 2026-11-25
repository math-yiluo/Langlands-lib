/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.IntegralCompletedComparison.IntegralPullbackCompletedComparisonData
public import WeilConjectures.DeligneLaumon.FinitePullbackStrictTower.FinitePullbackStrictTowerComparison
import WeilConjectures.CategoryTheory.DeligneLaumon.CompletedRlimRoosComparison
import WeilConjectures.DeligneLaumon.IntegralCompletedComparison.IntegralRoosFiniteTowerShift
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

set_option linter.privateModule false

/-! # Integral Roos realization through the finite-tower derived pair

Source: Stacks Project, sites-cohomology.tex, Tag 0941, and proetale.tex, Tag 099N(5).
(blueprint: lem-a1-integral-roos-finite-tower-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.IntegralOnSlice.hasDerived
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
  WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
  WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.constantSheaf
attribute [local implicit_reducible] SheafOfModules.instAbelian
  CategoryTheory.abelianOfAdjunction CategoryTheory.Abelian.ofCoimageImageComparisonIsIso
  WeilConjectures.scalarReductionSourceDerived WeilConjectures.scalarReductionTargetDerived
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.integralTowerHasDerivedCategory
  WeilConjectures.integralCompletedRingHasDerivedCategory
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
private instance (priority := 6000) fixedAbSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} W
private instance (priority := 6000) fixedAbBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W
namespace WeilConjectures.IntegralCompletedComparison
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y)

private abbrev rlim :=
  completedRlim.{u} X (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)

private theorem integralCofiberMap_eq_coneMap
    {V : Type*} [Category V] [Abelian V]
    {K L K' L' : CochainComplex V ℤ} (f : K ⟶ L) (g : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (h : a ≫ g = f ≫ b) :
    HomologicalComplex.homotopyCofiber.mapArrowHom f g
      (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (Arrow.homMk a b h) =
      CochainComplex.mappingCone.map f g a b h.symm := by
  ext i
  apply HomologicalComplex.homotopyCofiber.ext_from_X f (i + 1) i rfl
  all_goals simp [HomologicalComplex.homotopyCofiber.mapArrowHom,
    HomologicalComplex.homotopyCofiber.desc_f,
    HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom,
    CochainComplex.mappingCone.map, CochainComplex.mappingCone.desc,
    CochainComplex.mappingCone.descCochain, CochainComplex.HomComplex.Cochain.comp_v,
    CochainComplex.mappingCone.inl, CochainComplex.mappingCone.fst,
    CochainComplex.mappingCone.snd, CochainComplex.mappingCone.inr]

private def roosTransposeIso
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A] :
    integralOperationsRoosFunctor (A := A) ≅
      (HomologicalComplex.functorEquivalence A (.up ℤ) ℕᵒᵖ).inverse ⋙ roosF :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro P Q f
    dsimp only [Iso.refl_hom]
    rw [Category.comp_id, Category.id_comp]
    dsimp only [integralOperationsRoosFunctor, integralOperationsRoosMap,
      Functor.comp_map, roosF, roosConeFunctor]
    rw [integralCofiberMap_eq_coneMap]
    rfl)

end WeilConjectures.IntegralCompletedComparison
