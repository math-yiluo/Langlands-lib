/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatumCompleted
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.AlgebraicGeometry.ConstantRealizationDerivedScalarExtension
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.AlgebraicGeometry.KoszulDifferential
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
/-! # Intrinsic completion over the completed coefficient sheaf

Source: blueprint, proper base change, order 1247; Stacks Tags 099M and 091Z
(blueprint: def-weil-pbc-intrinsic-completion).

The ring and tensor product are those of Mod(A_T), with site object universe t+1
and morphism universe t. The mapping cocone of minus (1-shift) has differential
(dx, (1-shift)x-dy) after listing its degree-i terms as (x,y).

## Main definitions

* `completedKoszulPowerSheaf`: the completed-coefficient Koszul complex.
* `completedKoszulFiber`: the explicit completion complex.
* `completedIntrinsicCompletionMap`: its specified unit.
* `IsCompletedIntrinsicallyDerivedComplete`: invertibility of that unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
variable (d : ProEtaleAdicCoefficientDatum A)

section TensorUnits
set_option backward.isDefEq.respectTransparency false
variable {M : Type*} [Category* M] [Preadditive M] [MonoidalCategory M]
  [MonoidalPreadditive M]
  (C D K L : CochainComplex M ℤ)
  [HomologicalComplex.HasMapBifunctor C K (curriedTensor M) (.up ℤ)]
  [HomologicalComplex.HasMapBifunctor C L (curriedTensor M) (.up ℤ)]
  [HomologicalComplex.HasMapBifunctor D K (curriedTensor M) (.up ℤ)]

end TensorUnits

/-- Constant A-modules extended to the actual completed coefficient sheaf.
Source: order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def completedKoszulConstant : ModuleCat.{t + 1} A ⥤ adicDatumModules X d :=
  adicLisseConstantModules X A ⋙ completedConstantExtension X (adicDatumScalar X d)

/-- Constant module sheafification and scalar extension are additive.
Source: order 1247 (blueprint: def-weil-pbc-intrinsic-completion).
Proof: addition and zero hold on the constant presheaves, then on their sheafification;
scalar extension is additive by its specified tensor/restriction adjunction. -/
theorem completedKoszulConstant_additive : (completedKoszulConstant X d).Additive := by
  let := CompletedConstantReduction.constant_additive X A
  exact Functor.Additive.mk (by
    intro M N f g
    dsimp [completedKoszulConstant]
    rw [Functor.map_add, Functor.map_add])

attribute [instance] completedKoszulConstant_additive

/-- The completed unit is the image of 1 tensor 1 in the extended constant module.
The section formula uniquely determines it, including over the empty scheme.
Source: order 1247 (blueprint: def-weil-pbc-intrinsic-completion).
Proof: maps from the regular module correspond to global sections. The compatible
section 1 tensor 1 gives the map and determines it uniquely by linearity. -/
theorem completedKoszulOne_exists :
    ∃! u : SheafOfModules.unit ((adicLisseForget X).obj (adicDatumRing X d)) ⟶
        (completedKoszulConstant X d).obj (ModuleCat.of A A),
      ∀ U : X.ProEtᵒᵖ, u.val.app U (1 : (adicDatumRing X d).obj.obj U) =
        adicDatumTensorSection X (adicDatumScalar X d)
          ((adicLisseConstantModules X A).obj (ModuleCat.of A A)) U 1
          (completedConstantGenerator X A (ModuleCat.of A A) U 1) := by
  let M := (completedKoszulConstant X d).obj (ModuleCat.of A A)
  let s : M.sections := PresheafOfModules.sectionsMk
    (fun U ↦ adicDatumTensorSection X (adicDatumScalar X d)
      ((adicLisseConstantModules X A).obj (ModuleCat.of A A)) U 1
      (completedConstantGenerator X A (ModuleCat.of A A) U 1)) (by
        intro U V g
        let N := (adicLisseConstantModules X A).obj (ModuleCat.of A A)
        let u := adicDatumOrdinaryUnit X (adicDatumScalar X d) N
        have hu := (adicDatumOrdinaryUnit_exists X (adicDatumScalar X d) N).exists.choose_spec
        rw [← hu U, ← hu V]
        have hn := u.val.naturality g
        have hg : N.val.map g (completedConstantGenerator X A (ModuleCat.of A A) U 1) =
            completedConstantGenerator X A (ModuleCat.of A A) V 1 := by
          exact (ConcreteCategory.congr_hom
            ((toSheafify (ProEt.topology X)
              ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of A))).naturality g) (1 : A)).symm
        change M.val.map g (u.val.app U _) = u.val.app V _
        exact (ConcreteCategory.congr_hom hn _).symm.trans (congrArg (u.val.app V) hg))
  refine ⟨M.unitHomEquiv.symm s, ?_, ?_⟩
  · intro U
    exact congrArg (fun z : M.sections ↦ z.val U)
      (M.unitHomEquiv.apply_symm_apply s)
  · intro u hu
    apply M.unitHomEquiv.injective
    apply PresheafOfModules.sections_ext
    intro U
    exact (hu U).trans
      (congrArg (fun z : M.sections ↦ z.val U)
        (M.unitHomEquiv.apply_symm_apply s)).symm

/-- The canonical degree-zero unit of the extended Koszul complex.
Source: order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def completedKoszulOne := (completedKoszulOne_exists X d).exists.choose

section Descent
set_option backward.isDefEq.respectTransparency false

end Descent

end AlgebraicGeometry.Scheme
