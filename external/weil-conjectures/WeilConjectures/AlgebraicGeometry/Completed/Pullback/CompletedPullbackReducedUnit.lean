/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReductionData
import all WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantCoefficientEquivalence
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulConstantTransport
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedCoefficientFiniteUnit
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Finite reduction of the ordinary-to-completed pullback comparison

Source: Stacks Tag 099N (5).
(blueprint: lem-weil-pbc-completed-pullback-reduced-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A)

private instance proEtaleEssentiallySmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

private instance constantModuleDerived
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u + 1}) :
    HasDerivedCategory (ConstantCompletion.Mod R) := HasDerivedCategory.standard _

private instance smallEquivFunctor_additive (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (B : Sheaf (comparisonTopology T) CommRingCat.{u + 1})
    (β : (CechConstantAlgebra.pushRing T).obj R ≅ B) :
    (smallModulesEquiv T R B β).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

private instance smallEquivInverse_additive (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (B : Sheaf (comparisonTopology T) CommRingCat.{u + 1})
    (β : (CechConstantAlgebra.pushRing T).obj R ≅ B) :
    (smallModulesEquiv T R B β).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

private instance cechEquiv_additive (T : Scheme.{u}) :
    (completedCechModulesEquiv T d).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

private def finiteExtensionTransport (T : Scheme.{u}) (n : ℕ) :
    reductionDerivedChange T (completedReductionProjection T d n) ⋙
        (smallModulesEquiv T (reductionCoefficient T d n)
          (ConstantCompletion.finite (comparisonTopology T) A d.ideal n)
          (comparisonFiniteRing T d n)).mapDerivedCategory.functor ≅
      (comparisonModulesEquiv T d).mapDerivedCategory.functor ⋙
        ConstantCompletion.extend
          (ConstantCompletion.projection (comparisonTopology T) A d.ideal n) := by
  let E := comparisonModulesEquiv T d
  let G := smallModulesEquiv T (reductionCoefficient T d n)
    (ConstantCompletion.finite (comparisonTopology T) A d.ideal n)
    (comparisonFiniteRing T d n)
  let : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  let : E.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let : G.functor.Additive := Functor.additive_of_preserves_binary_products _
  let : G.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let h := smallRestrictionComparison T
    (CechConstantAlgebra.algebraIso T d.ideal (pbcCompletedComparison T d))
    (comparisonFiniteRing T d n) (completedReductionProjection T d n)
    (ConstantCompletion.projection (comparisonTopology T) A d.ideal n)
    (comparisonRing_projection T d n)
  let hd := Functor.mapDerivedCategorySquareIso h
  exact extensionTransport E.mapDerivedCategory G.mapDerivedCategory
    (reductionDerivedChange T (completedReductionProjection T d n))
    (pbcDerivedRestrict (completedReductionProjection T d n))
    (ConstantCompletion.extend
      (ConstantCompletion.projection (comparisonTopology T) A d.ideal n))
    (ConstantCompletion.dres
      (ConstantCompletion.projection (comparisonTopology T) A d.ideal n))
    (pbcDerivedScalarAdjunction (completedReductionProjection T d n))
    (ConstantCompletion.scalarAdjunction (comparisonTopology T)
      (ConstantCompletion.projection (comparisonTopology T) A d.ideal n)) hd

private theorem intrinsicUnit_finite (T : Scheme.{u})
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (P : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) (n : ℕ) :
    IsIso ((reductionDerivedChange T (completedReductionProjection T d n)).map
      (DerivedCategory.Q.map (intrinsicCompletionComplexUnit T d r a P))) := by
  let := d.noetherian
  let E := comparisonModulesEquiv T d
  let : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  let : E.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let F := E.mapDerivedCategory.functor
  let : (completedCechModulesEquiv T d).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  let δ := comparisonModulesEquiv_to_cech T d
  let δD : F ≅ (completedCechDerivedEquiv T d).functor ⋙
      ConstantCompletion.dres (comparisonCompletedRingIso T d).inv :=
    Functor.mapDerivedCategoryNatIso δ ≪≫ (Functor.mapDerivedCategoryCompIso _ _).symm
  obtain ⟨k, hk⟩ := completed_koszul_constant_transport T d
    (comparisonCompletedRingIso T d) (comparisonCompletedRingIso_scalar T d) F δD r a ha P
  let L := ConstantCompletion.extend
    (ConstantCompletion.projection (comparisonTopology T) A d.ideal n)
  have hunit := ConstantCompletion.finite_completionUnit_isIso
    (comparisonTopology T) A d.ideal true (F.obj (DerivedCategory.Q.obj P)) n
  have hm : IsIso (L.map (F.map
      (DerivedCategory.Q.map (intrinsicCompletionComplexUnit T d r a P))) ≫
        L.map k.hom) := by
    rw [← L.map_comp, hk]
    exact hunit
  have : IsIso (L.map (F.map
      (DerivedCategory.Q.map (intrinsicCompletionComplexUnit T d r a P)))) :=
    IsIso.of_isIso_comp_right _ (L.map k.hom)
  let G := smallModulesEquiv T (reductionCoefficient T d n)
    (ConstantCompletion.finite (comparisonTopology T) A d.ideal n)
    (comparisonFiniteRing T d n)
  let : G.functor.Additive := Functor.additive_of_preserves_binary_products _
  let : G.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let v := DerivedCategory.Q.map (intrinsicCompletionComplexUnit T d r a P)
  let e := finiteExtensionTransport d T n
  have hn : (G.mapDerivedCategory.functor).map
      ((reductionDerivedChange T (completedReductionProjection T d n)).map v) ≫
        e.hom.app _ = e.hom.app _ ≫ L.map (F.map v) := e.hom.naturality v
  have hiso : IsIso ((G.mapDerivedCategory.functor).map
      ((reductionDerivedChange T (completedReductionProjection T d n)).map v) ≫
        e.hom.app _) := by
    rw [hn]
    infer_instance
  have : IsIso ((G.mapDerivedCategory.functor).map
      ((reductionDerivedChange T (completedReductionProjection T d n)).map v)) :=
    IsIso.of_isIso_comp_right _ (e.hom.app _)
  exact isIso_of_reflects_iso _ G.mapDerivedCategory.functor

/-- Finite scalar extension inverts the ordinary-to-completed comparison.
Source: Stacks Tag 099N (5), finite reduction of the completion reflector unit.
(blueprint: lem-weil-pbc-completed-pullback-reduced-unit).

Proof: identify the augmented pulled tower with the quotient tower of ordinary
pullback. Its limit comparison carries the displayed comparison to the completion
unit. Restricted finite quotient objects are complete because the generators of the
adic ideal act nilpotently. The reflector's Hom bijection and scalar adjunction
therefore show that precomposition with the reduced unit is bijective into every
finite-coefficient target. Coyoneda detects that it is an isomorphism. -/
theorem completedPullbackComparison_reduction_isIso
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
    (C : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
    (e : DerivedCategory.Q.obj C ≅ K)
    (hK : IsDerivedCompleteIntrinsic Y d r a ha K C e) (n : ℕ) :
    IsIso ((reductionDerivedChange X (completedReductionProjection X d n)).map
      (completedPullbackComparison g d K)) := by
  let N := (completedOrdinaryPullback g d).obj K
  let P := DerivedCategory.Q.objPreimage N
  let eP := DerivedCategory.Q.objObjPreimageIso N
  obtain ⟨α, hα⟩ := completedPullback_isCompletion g d r a ha K C e hK P eP
  let L := reductionDerivedChange X (completedReductionProjection X d n)
  have := intrinsicUnit_finite d X r a ha P n
  have hi : IsIso (L.map (intrinsicCompletionUnit X d r a ha N P eP)) := by
    unfold intrinsicCompletionUnit
    rw [L.map_comp]
    infer_instance
  have hc : IsIso (L.map (completedPullbackComparison g d K) ≫ L.map α.hom) := by
    rw [← L.map_comp, hα]
    exact hi
  exact IsIso.of_isIso_comp_right _ (L.map α.hom)

end AlgebraicGeometry.Scheme
