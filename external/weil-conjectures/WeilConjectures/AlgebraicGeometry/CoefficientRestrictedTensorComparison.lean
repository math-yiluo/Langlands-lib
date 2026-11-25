/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
public import WeilConjectures.AlgebraicGeometry.CoefficientFixedPullbackExact
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.Algebra.Homology.ConstantRingDerivedTensorFlatFunctor
import WeilConjectures.AlgebraicGeometry.CoefficientFixedPullbackFlat
import all WeilConjectures.AlgebraicGeometry.CoefficientProEtaleFiniteLocalModelsPullback
import all WeilConjectures.AlgebraicGeometry.FiniteComparisonModelRealization
import all WeilConjectures.CategoryTheory.SiteModuleSheafConstantRingEquivalence
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal

/-! # Derived tensor comparison for the coefficient-sized inverse image

Source: Stacks Project, Cohomology on Sites, Tag 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v w
open CategoryTheory CategoryTheory.ConstantCompletion CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme

attribute [local instance] ConstantScalarRestriction.complexTensorMemo
  ConstantScalarRestriction.derivedTensorMemo

private def fixedConstantIso {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type w) [CommRing A] :
    commutativeSiteConstantModuleFunctor J A ⋙ coefficientModelFixedScalars J A ≅
      constantSheaf J (ModuleCat.{w} A) := by
  let α := realizationRingUnit J A
  let := (realizationRingUnit_locallyBijective J A).1
  let := (realizationRingUnit_locallyBijective J A).2
  let i : moduleRestriction J A _ α ≅ coefficientModelFixedScalars J A :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro _ _ _; rfl)
  let e := moduleRestrictionConstantIso J A _ α
  exact (Functor.isoWhiskerLeft (commutativeSiteConstantModuleFunctor J A) i.symm) ≪≫ e

@[instance_reducible]
private def fixedScalarsMonoidal {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type w) [CommRing A] :
    (coefficientModelFixedScalars J A).Monoidal := by
  letI := (ConstantScalarRestriction.ordinary J A).braided.toMonoidal
  let i : ConstantScalarRestriction.restriction J A ≅ coefficientModelFixedScalars J A :=
    CategoryTheory.restrictionIso J A
  exact Functor.Monoidal.transport i

/-- Exact fixed-scalar inverse image commutes with tensor by a constant module in the
ordinary derived categories, after the target constant-scalar equivalence.

Source: Stacks Project, sites-cohomology.tex, Tag 07A4,
lemma-pullback-tensor-product; Modules on Sites, Tag 03CY.
(auxiliary; not a blueprint node).

Proof: the constant-scalar realization equivalences are exact and monoidal, and
coefficient inverse image is an exact monoidal left adjoint preserving ordinary flat
objects. Choose flat-term K-flat representatives for both derived inputs. The published
cochain tensor comparison computes their tensor; the flat-term preservation theorem
makes the second image K-flat. Compose exact derived-functor factorization, the cochain
monoidal comparison and the inverse native localization tensorator. Thus either
realization functor takes the published tensor to the native tensor of its images.
The ordinary constant-realization comparison and the constant-sheaf adjunction identify
inverse image of constant_X(M) with constant_Y(M). Derive this isomorphism on the single
complexes. Finally compose the two tensor comparisons with this isomorphism and the
counit of the target derived equivalence. No boundedness, Noetherianity, finite
generation, local constancy or flatness of M is used. Zero coefficients, the zero
module and empty schemes are included. -/
theorem coefficient_restricted_tensor_comparison
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : Type (max v (u + 1))) [CommRing A]
    (K : adicFiniteAmbient.{u, v} X A) (M : ModuleCat.{max v (u + 1)} A) :
    let R := constant (coefficientProEtaleModelTopology.{u, v} Y) A
    let S := constant (coefficientProEtaleModelTopology.{u, v} X) A
    let E := coefficientModelFixedScalars (coefficientProEtaleModelTopology.{u, v} Y) A
    let F := coefficientModelFixedScalars (coefficientProEtaleModelTopology.{u, v} X) A ⋙
      coefficientProEtaleFixedModulePullback.{u, v} f A
    letI := HasDerivedCategory.standard (Mod R)
    letI := HasDerivedCategory.standard (Mod S)
    letI := HasDerivedCategory.standard
      (Sheaf (coefficientProEtaleModelTopology.{u, v} Y) (ModuleCat.{max v (u + 1)} A))
    Nonempty (F.mapDerivedCategory.obj
        (((SheafOfModules.KFlatFixedTensor.derivedTensor S).obj K).obj
          ((Q S).obj ((HomologicalComplex.single (Mod S) (.up ℤ) 0).obj
            ((commutativeSiteConstantModuleFunctor
              (coefficientProEtaleModelTopology.{u, v} X) A).obj M)))) ≅
      E.mapDerivedCategory.obj
        (((SheafOfModules.KFlatFixedTensor.derivedTensor R).obj
          (E.mapDerivedCategory.inv.obj (F.mapDerivedCategory.obj K))).obj
            ((Q R).obj ((HomologicalComplex.single (Mod R) (.up ℤ) 0).obj
              ((commutativeSiteConstantModuleFunctor
                (coefficientProEtaleModelTopology.{u, v} Y) A).obj M))))) := by
  dsimp only
  classical
  let J := coefficientProEtaleModelTopology.{u, v} X
  let T := coefficientProEtaleModelTopology.{u, v} Y
  let ES : ConstantScalarRestriction.Modules J A ⥤ Sheaf J (ModuleCat A) :=
    coefficientModelFixedScalars J A
  let E : ConstantScalarRestriction.Modules T A ⥤ Sheaf T (ModuleCat A) :=
    coefficientModelFixedScalars T A
  let P := coefficientProEtaleFixedModulePullback.{u, v} f A
  let F := ES ⋙ P
  let := HasDerivedCategory.standard (ConstantScalarRestriction.Modules J A)
  let := HasDerivedCategory.standard (ConstantScalarRestriction.Modules T A)
  let := HasDerivedCategory.standard (Sheaf T (ModuleCat.{max v (u + 1)} A))
  let : ES.IsEquivalence :=
    inferInstanceAs (coefficientModelFixedScalars J A).IsEquivalence
  let : E.IsEquivalence :=
    inferInstanceAs (coefficientModelFixedScalars T A).IsEquivalence
  let : ES.Additive := Functor.additive_of_preserves_binary_products ES
  let : E.Additive := Functor.additive_of_preserves_binary_products E
  let : ES.Monoidal := fixedScalarsMonoidal J A
  let : E.Monoidal := fixedScalarsMonoidal T A
  let : ES.PreservesFlat := ES.preservesFlat_of_isEquivalence
  let : E.PreservesFlat := E.preservesFlat_of_isEquivalence
  let : P.PreservesFlat := coefficientFixedPullback_preservesFlat f A
  let V := coefficientProEtaleModelBaseChange.{u, v} f
  have : PreservesFiniteLimits V := AlgebraicGeometry.ProEtale.model_preserves f
  have : RepresentablyFlat V := flat_of_preservesFiniteLimits V
  let : P.Monoidal :=
    Functor.sheafPullbackConstruction.sheafPullbackMonoidal V (ModuleCat A) J T
  let : P.Additive := Functor.additive_of_preserves_binary_products P
  let : P.IsLeftAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      V (ModuleCat A) J T).isLeftAdjoint
  let : F.PreservesFlat :=
    ⟨fun h ↦ Functor.PreservesFlat.flat_obj (F := P)
      (Functor.PreservesFlat.flat_obj (F := ES) h)⟩
  let NS : ConstantScalarRestriction.Modules J A :=
    (commutativeSiteConstantModuleFunctor J A).obj M
  let NR : ConstantScalarRestriction.Modules T A :=
    (commutativeSiteConstantModuleFunctor T A).obj M
  let singS := (HomologicalComplex.single (ConstantScalarRestriction.Modules J A) (.up ℤ) 0).obj NS
  let singR := (HomologicalComplex.single (ConstantScalarRestriction.Modules T A) (.up ℤ) 0).obj NR
  let KS := DerivedCategory.Q.obj singS
  let KR := DerivedCategory.Q.obj singR
  let G := E.mapDerivedCategory
  let H := F.mapDerivedCategory
  let L := G.inv.obj (H.obj K)
  let e : G.obj L ≅ H.obj K := G.asEquivalence.counitIso.app _
  let cF := (ConstantScalarRestriction.constantRingDerivedTensorComparison J T A F K KS).some
  let cE := (ConstantScalarRestriction.constantRingDerivedTensorComparison T T A E L KR).some
  let cc : F.obj NS ≅ E.obj NR := by
    let ci : (constantSheaf J (ModuleCat A)) ⋙ P ≅ constantSheaf T (ModuleCat A) :=
      Functor.isoWhiskerLeft (constantSheaf J (ModuleCat A))
        (Functor.sheafPullbackConstruction.sheafPullbackIso V (ModuleCat A) J T).symm ≪≫
      V.constantSheafsheafPullbackIso (ModuleCat A) J T terminalIsTerminal
        (terminalIsTerminal.isTerminalObj V)
    exact P.mapIso ((fixedConstantIso J A).app M) ≪≫ ci.app M ≪≫
      ((fixedConstantIso T A).app M).symm
  let cs : (F.mapHomologicalComplex (.up ℤ)).obj singS ≅
      (E.mapHomologicalComplex (.up ℤ)).obj singR :=
    (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app NS ≪≫
      (HomologicalComplex.single _ (.up ℤ) 0).mapIso cc ≪≫
      ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).app NR).symm
  let c : H.obj KS ≅ G.obj KR :=
    F.mapDerivedCategoryFactors.app singS ≪≫ DerivedCategory.Q.mapIso cs ≪≫
      (E.mapDerivedCategoryFactors.app singR).symm
  exact ⟨cF ≪≫ tensorIso e.symm c ≪≫ cE.symm⟩

end AlgebraicGeometry.Scheme
