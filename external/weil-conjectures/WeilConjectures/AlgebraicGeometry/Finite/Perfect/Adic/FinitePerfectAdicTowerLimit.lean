/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicTowerExtraction
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicMarkedRoos
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicComplexRoos
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.AlgebraicGeometry.Pbc.PbcDerivedProductRepresentation
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTowerTriangle
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # The Roos computation for a compatibly marked finite-projective quotient system

Source: Stacks Project, Tag 09C6, the finite-projective inverse-limit calculation;
Cohomology on Sites, Tags 0940 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The specified total right derived limit is the Roos limit of every representative diagram. -/
private theorem completedRlim_isDerivedLimit
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (Z : DerivedCategory (CompletedAdicTowers X d)) :
    IsDerivedLimit (K := fun n : ℕ ↦ DerivedCategory.Q.obj
      ((DerivedCategory.Q.objPreimage Z).asFunctor.obj (op n)))
      (fun n : ℕ ↦ DerivedCategory.Q.map
        ((DerivedCategory.Q.objPreimage Z).asFunctor.map (homOfLE (Nat.le_succ n)).op))
      ((reconstructionRlim X d).obj Z) := by
  classical
  have := finitePerfectAdicModules_exactProducts X d
  have : IsGrothendieckAbelian.{t + 1} (CompletedAdicModules X d) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1, t, 0}
      (ProEt.topology X) (completedAdicCommRing X d)).1
  let H := DerivedCategory.Q.objPreimage Z
  obtain ⟨J, hJ, q, _, hq⟩ :=
    CategoryTheory.Abelian.HasKInjectiveResolutions.exists_isKInjective H
  have := hJ
  have := hq
  let eZ : DerivedCategory.Q.obj J ≅ Z :=
    (asIso (DerivedCategory.Q.map q)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso Z
  let c : Cone J.asFunctor :=
    { pt := ((reconstructionLimit X d).mapHomologicalComplex (.up ℤ)).obj J
      π :=
        { app := fun n ↦ (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app J
          naturality := by
            intro n m f
            apply HomologicalComplex.Hom.ext
            funext i
            exact (limit.w (J.X i) f).symm } }
  have hc : IsLimit c := by
    apply HomologicalComplex.isLimitOfEval
    intro i
    exact limit.isLimit (J.X i)
  obtain ⟨δ, hδ⟩ := derivedCategory_towerLimit_triangle (CompletedAdicModules X d)
    inferInstance inferInstance J c hc
  let eL : DerivedCategory.Q.obj c.pt ≅ (reconstructionRlim X d).obj Z :=
    ((reconstructionLimit X d).rightDerivedFunctorObjQIso J).symm ≪≫
      (reconstructionRlim X d).mapIso eZ
  have hi : IsIso ((AlgebraicGeometry.ProEtale.pbcComplexEvaluation X d).map q) :=
    AlgebraicGeometry.ProEtale.pbcComplexEvaluation_inverts X d q hq
  let e : J.asFunctor ⋙ DerivedCategory.Q ≅ H.asFunctor ⋙ DerivedCategory.Q :=
    (asIso ((AlgebraicGeometry.ProEtale.pbcComplexEvaluation X d).map q)).symm
  exact finitePerfectAdicRoos_changeDiagram _ _ e _
    (finitePerfectAdicRoos_changeObject _ eL ⟨_, δ, hδ⟩)

/-- Slice restriction carries the specified strict limit to the restricted Roos limit. -/
private theorem restrictedRlim_isDerivedLimit
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (U : X.ProEt)
    [HasCountableProducts
      (DerivedCategory (SheafOfModules.{t + 1} ((completedAdicRing X d).over U)))]
    (Z : DerivedCategory (CompletedAdicTowers X d)) :
    IsDerivedLimit
      (K := fun n : ℕ ↦ (finitePerfectAdicRestrictedTower X d U Z).obj (op n))
      (fun n : ℕ ↦ (finitePerfectAdicRestrictedTower X d U Z).map
        (homOfLE (Nat.le_succ n)).op)
      ((ringedDerivedRestrictionGeneral.{t + 1, t, t + 1, t + 1}
        (completedAdicRing X d) U).obj ((reconstructionRlim X d).obj Z)) := by
  have := finitePerfectAdicModules_exactProducts X d
  obtain ⟨hprod, _, _⟩ := derivedCategory_countableProducts_core.{0}
    (CompletedAdicModules X d)
  let := hprod
  simpa only [finitePerfectAdicRestrictedTower, Functor.comp_obj, Functor.comp_map] using
    finitePerfectAdicRestriction_roos X d U
      ((DerivedCategory.Q.objPreimage Z).asFunctor ⋙ DerivedCategory.Q) _
      (completedRlim_isDerivedLimit X d Z)

/-- A compatible finite-projective marking computes the local derived inverse limit.

Source: Stacks Project, Tag 09C6, the inverse-limit calculation for finite-projective
complexes; Cohomology on Sites, Tags 0940 and 0941.
(blueprint: lem-weil-pbc-finite-perfect-adic-tower-limit).

Proof: identify each chosen left adjoint with derived tensor by uniqueness of a left
adjoint to exact restriction of scalars. The markings and their displayed unit equations
then identify the entire restricted quotient diagram with the canonical quotient
system of P, including all longer transitions. For each projective finite term of P,
choose an idempotent splitting it from a finite free module. The quotient tower has
sectionwise surjective transitions. Recursive lifting proves that one minus shift on
its product is sectionwise surjective. Its kernel is the same idempotent summand of
the completed coefficient sheaf. Thus the degreewise Roos short exact sequence
identifies its derived limit with completed scalar extension of the constant P.
The boundedness of P permits the termwise computation for the total complex.
Exact slice restriction preserves products and carries Roos triangles to Roos
triangles. The strict-tower homotopy-limit comparison identifies the specified total
right derived inverse limit, after restriction, with the derived limit of its
levelwise diagram. Apply the diagram isomorphism and uniqueness of Roos limits.
This argument concerns a specified compatible marking and requires no local
constancy, geometric stalk, or perfect-model existence assertion. -/
theorem finitePerfectAdicTower_limit
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [IsAdicComplete d.ideal A] (U : X.ProEt)
    (Z : DerivedCategory (CompletedAdicTowers X d))
    (T : FinitePerfectAdicLocalTower X d U Z)
    (P : CochainComplex (ModuleCat.{t} A) ℤ) (a b : ℤ)
    (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hP : ∀ i : ℤ, Module.Projective A (P.X i) ∧ Module.Finite A (P.X i))
    (e : ∀ n : ℕ, (T.extension n).obj (DerivedCategory.Q.obj P) ≅ T.level n)
    (he : ∀ n : ℕ,
      (T.adjunction (n + 1)).unit.app (DerivedCategory.Q.obj P) ≫
          (DerivedCategory.adicLevelRestriction d.ideal (n + 1)).map (e (n + 1)).hom ≫
          DerivedCategory.adicTowerTransition d.ideal T.level T.transition n =
        (T.adjunction n).unit.app (DerivedCategory.Q.obj P) ≫
          (DerivedCategory.adicLevelRestriction d.ideal n).map (e n).hom) :
    Nonempty
      ((ringedDerivedRestrictionGeneral.{t + 1, t, t + 1, t + 1}
          (completedAdicRing X d) U).obj ((reconstructionRlim X d).obj Z) ≅
        (finitePerfectAdicLocalRealization X d U).obj (DerivedCategory.Q.obj P)) := by
  classical
  have : IsGrothendieckAbelian.{t + 1}
      (SheafOfModules.{t + 1} ((completedAdicRing X d).over U)) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1, t, 0}
      ((ProEt.topology X).over U)
      ((completedAdicCommRing X d).over U)).1
  have : HasCountableProducts
      (DerivedCategory (SheafOfModules.{t + 1} ((completedAdicRing X d).over U))) :=
    ⟨fun J _ ↦ DerivedCategory.hasLimitsOfShape_discrete _ J⟩
  obtain ⟨c⟩ := T.comparison
  have h₁ := finitePerfectAdicRoos_changeDiagram _ _ c _
    (restrictedRlim_isDerivedLimit X d U Z)
  obtain ⟨m⟩ := finitePerfectAdicQuotientDiagram_marking d.ideal T.extension T.adjunction
    (DerivedCategory.Q.obj P) T.level T.transition e he
  let m' := Functor.isoWhiskerRight m (finitePerfectAdicLocalRealization X d U)
  have h₂ := finitePerfectAdicRoos_changeDiagram _ _ m' _
    (finitePerfectAdicMarked_roos X d U T.extension T.adjunction P a b ha hb hP)
  simp only [Functor.comp_obj, Functor.comp_map,
    Functor.ofOpSequence_map_homOfLE_succ] at h₁ h₂
  exact (exists_isDerivedLimit_and_iso _ _).2 _ _ h₁ h₂

end AlgebraicGeometry.Scheme
