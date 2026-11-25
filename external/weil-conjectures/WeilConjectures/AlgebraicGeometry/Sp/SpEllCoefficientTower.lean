/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwistLevelsSupplement

import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Mathlib.NumberTheory.Padics.PadicNumbers
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Mathlib.Condensed.TopComparison
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import WeilConjectures.SixFunctors.ProEtale.Adic.ContinuousMapReduction
import WeilConjectures.NumberTheory.Padics.IntegersModPow

/-! # The integral coefficient tower with its specified reduction maps -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale

/-- Section reconstruction followed by restriction to the specified slice. -/
def spRootBasisSliceSections (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    [MonObj R] [IsCommMonObj R] (W : X.ProEt) :
    Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R ⥤
      SheafOfModules.{u + 1}
        (((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
              (Scheme.ProEt.topology X) R)).over W) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) R).functor ⋙
      SheafOfModules.overFunctor _ W

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The quotient coefficient as an integral module, with its actual quotient action. -/
def spEllCoefficientLevel (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X) :=
  (Mod.comap (spEllReduction X ℓ E n)).obj
    (Mod.regular (condensedRingObj.{u} (spEllPointRingObj ℓ E n) X))

/-- Reduction of coefficients, bundled with linearity over the integral coefficient ring. -/
def spEllCoefficientTransition (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    spEllCoefficientLevel X ℓ E (n + 1) ⟶ spEllCoefficientLevel X ℓ E n :=
  Mod.homMk (coefficientMap.{u} (spEllPointTransition ℓ E n) X) (by
    let p := spEllReduction X ℓ E (n + 1)
    let q := spEllReduction X ℓ E n
    let r := coefficientMap.{u} (spEllPointTransition ℓ E n) X
    change (p ▷ _) ≫ MonObj.mul ≫ r = _ ◁ r ≫ (q ▷ _) ≫ MonObj.mul
    have h : p ≫ r = q := by
      dsimp only [p, q, r]
      rw [← coefficientMap_comp]
      apply congrArg (fun f ↦ coefficientMap.{u} f X)
      unfold spEllPointReduction spEllPointTransition
      rw [← Functor.map_comp]
      rfl
    rw [IsMonHom.mul_hom]
    simp only [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
      Category.comp_id, Category.id_comp, h])

/-- The positive ell-power quotient tower, in integral module objects. -/
def spEllCoefficientSystem (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ℕᵒᵖ ⥤ Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X) :=
  Functor.ofOpSequence (spEllCoefficientTransition X ℓ E)

/-- The reduction from the regular integral module to one quotient level. -/
def spEllCoefficientProjection (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    Mod.regular (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X) ⟶
      spEllCoefficientLevel X ℓ E n :=
  Mod.homMk (spEllReduction X ℓ E n) (by
    change MonObj.mul ≫ spEllReduction X ℓ E n =
      _ ◁ spEllReduction X ℓ E n ≫ (spEllReduction X ℓ E n ▷ _) ≫ MonObj.mul
    rw [IsMonHom.mul_hom, tensorHom_def', Category.assoc])

/-- The coefficient cone uses the given reductions, rather than arbitrary limit maps. -/
def spEllCoefficientCone (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    Cone (spEllCoefficientSystem X ℓ E) where
  pt := Mod.regular (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X)
  π := NatTrans.ofOpSequence (spEllCoefficientProjection X ℓ E) (by
    intro n
    simp only [Functor.const_obj_map, spEllCoefficientSystem,
      Functor.ofOpSequence_map_homOfLE_succ]
    apply Mod.hom_ext
    change spEllReduction X ℓ E n = spEllReduction X ℓ E (n + 1) ≫
      coefficientMap.{u} (spEllPointTransition ℓ E n) X
    symm
    rw [← coefficientMap_comp]
    apply congrArg (fun f ↦ coefficientMap.{u} f X)
    unfold spEllPointReduction spEllPointTransition
    rw [← Functor.map_comp]
    rfl)

/-- The specified ell-power reductions make the regular integral coefficient module
an inverse limit of its quotient coefficient modules.

Source: blueprint latest, sec-proetale-coefficients/sk-def-sp-tate-twist/_section.md,
integral coefficient comparison and cofinality paragraph;
sec-smooth-purity/sk-prop-an/sk-def-sp-tate-twist-locally-free.proof.md, clause (3).
(blueprint: lem-sp-ell-coefficient-cone-limit)

Proof: the native continuous-function coefficient sheaf is the limit of all
ell-power quotient sheaves, with its specified reduction projections. The successor
functor on the opposite natural-number category is initial: predecessor is left
adjoint to successor on the natural-number order. Whiskering this limit cone removes
its zero exponent and gives exactly the positive exponents used here. The canonical
condensed-to-continuous coefficient comparison is an isomorphism for the integral
ring and for each discrete quotient. Its naturality for continuous ring maps makes
these comparisons an isomorphism of the actual quotient diagrams and identifies
every reduction projection. Transport the continuous limit through these diagram
and cone isomorphisms. Finally the internal-module forgetful functor reflects limits,
so the constructed coefficient cone is a limit in modules with the specified action.
No preservation of infinite limits by an inverse-image functor is used. -/
theorem spEllCoefficientCone_isLimit (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    Nonempty (IsLimit (spEllCoefficientCone X ℓ E)) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let := PadicAlgCl.isUltrametricDist_ofAlgebra ℓ E.1
  let R := condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X
  let D := continuousMapAbSheafTower X (PadicAlgCl.integersModPowTransition ℓ E.1)
    (fun _ ↦ continuous_of_discreteTopology)
  let c : Cone D := continuousMapAbSheafCone X
    (PadicAlgCl.integersModPowTransition ℓ E.1) (fun _ ↦ continuous_of_discreteTopology)
    (PadicAlgCl.integersModPowMk ℓ E.1) (PadicAlgCl.continuous_integersModPowMk ℓ E.1)
    (PadicAlgCl.integersModPowTransition_comp ℓ E.1)
  have hc : IsLimit c := isLimitContinuousMapAbSheafCone X _ _ _ _ _
    (fun _ _ h ↦ PadicAlgCl.integersModPowMk_injective ℓ E.1 h)
    (PadicAlgCl.exists_integersModPowMk_eq ℓ E.1)
    (PadicAlgCl.isInducing_integersModPowMk ℓ E.1)
  let σ := (Order.gc_pred_succ (α := ℕ)).monotone_u.functor.op
  have : σ.Initial := Functor.initial_of_adjunction
    (Order.gc_pred_succ (α := ℕ)).adjunction.op
  have hσ (n : ℕ) :
      (σ ⋙ D).map (homOfLE (Nat.le_succ n)).op =
        continuousMapAbSheafMap X (PadicAlgCl.integersModPowTransition ℓ E.1 (n + 1))
          continuous_of_discreteTopology := by
    change D.map (homOfLE (Nat.le_succ (n + 1))).op = _
    exact continuousMapAbSheafTower_map_succ X _ _ (n + 1)
  let t : spEllCoefficientSystem X ℓ E ⋙ Mod.forget R ⟶ σ ⋙ D :=
    NatTrans.ofOpSequence
      (fun n ↦ chartComparison X (PadicAlgCl.integersModPow ℓ E.1 (n + 1))) (by
        intro n
        rw [hσ]
        simp only [Functor.comp_map, spEllCoefficientSystem,
          Functor.ofOpSequence_map_homOfLE_succ]
        change coefficientMap.{u} (spEllPointTransition ℓ E n) X ≫
            chartComparison X (PadicAlgCl.integersModPow ℓ E.1 (n + 1)) =
          chartComparison X (PadicAlgCl.integersModPow ℓ E.1 (n + 2)) ≫
            continuousMapAbSheafMap X
              (PadicAlgCl.integersModPowTransition ℓ E.1 (n + 1))
              continuous_of_discreteTopology
        exact chartComparison_naturality X _ _
          (PadicAlgCl.integersModPowTransition ℓ E.1 (n + 1))
          continuous_of_discreteTopology)
  have (n : ℕᵒᵖ) : IsIso (t.app n) := by
    change IsIso (chartComparison X (PadicAlgCl.integersModPow ℓ E.1 (n.unop + 1)))
    infer_instance
  have : IsIso t := NatIso.isIso_of_isIso_app t
  refine ⟨?_⟩
  apply isLimitOfReflects (Mod.forget R)
  apply (IsLimit.postcomposeHomEquiv (asIso t) _).toFun
  refine IsLimit.ofIsoLimit ((Functor.Initial.isLimitWhiskerEquiv σ c).symm hc) ?_
  refine (Cone.ext (asIso (chartComparison X (PadicAlgCl.integers ℓ E.1))) ?_).symm
  intro n
  simp only [Cone.postcompose_obj_π, NatTrans.comp_app]
  change spEllReduction X ℓ E n.unop ≫
      chartComparison X (PadicAlgCl.integersModPow ℓ E.1 (n.unop + 1)) =
    chartComparison X (PadicAlgCl.integers ℓ E.1) ≫
      continuousMapAbSheafMap X (PadicAlgCl.integersModPowMk ℓ E.1 (n.unop + 1))
        (PadicAlgCl.continuous_integersModPowMk ℓ E.1 (n.unop + 1))
  exact chartComparison_naturality X _ _
    (PadicAlgCl.integersModPowMk ℓ E.1 (n.unop + 1))
    (PadicAlgCl.continuous_integersModPowMk ℓ E.1 (n.unop + 1))

end AlgebraicGeometry.ProEtale
