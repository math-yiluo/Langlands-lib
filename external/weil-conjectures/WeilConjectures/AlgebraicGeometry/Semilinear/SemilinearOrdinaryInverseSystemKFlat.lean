/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearOrdinaryInverseSystem
import WeilConjectures.Algebra.Homology.System.SystemEvaluationKFlat
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.SixFunctors.Supporting.SemilinearTotalTensorEvaluation
import all WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearSystemsExistence

/-! # K-flatness for ordinary inverse systems

## References

* Zheng Construction 4.1
* Stacks sites-cohomology
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n, B (n + 1) ⟶ B n)
  {D : Type c} [Category.{v} D] [EssentiallySmall.{max c v r} D]
  (J' : GrothendieckTopology D)
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
  (F : ℕ → Sheaf J' CommRingCat.{max c v r}) (σ : ∀ n, F (n + 1) ⟶ F n)
  (I : ∀ n, SheafOfModules.AlgebraicInverseImage uInv (B n) (F n))

private theorem evaluation_sequence (n : ℕ) :
    evaluation.{c, v, max c v r} J B τ n =
      SheafOfModules.systemSequenceEvaluation (rings.{c, v, max c v r} J B τ) n := by
  unfold evaluation SheafOfModules.systemSequenceEvaluation
  congr 1
  ext U x
  rw [ObjectProperty.eqToHom_hom, eqToHom_app]
  rfl

include uPush adj in
private theorem finite_kflat (n : ℕ) [(I n).modules.Additive]
    (P : CochainComplex (Mod.{c, v, max c v r} J (B n)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := B n) P)
    (hf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := B n) (P.X i)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := F n)
      (((I n).modules.mapHomologicalComplex (.up ℤ)).obj P) := by
  let A : SheafOfModules.SystemScalarModel (J := J') (𝟙 (F n)) :=
    (SheafOfModules.nonempty_systemScalarModel (J := J') (𝟙 (F n))).some
  let T := (I n).modules ⋙ A.model.E
  have ht := SheafOfModules.isKFlat_ringedToposPullback uInv uPush adj (I n) (𝟙 (F n)) T
    (fun M ↦ A.model.obj_eq ((I n).modules.obj M))
    (fun f ↦ A.model.map_eq ((I n).modules.map f)) P hP hf
  let e : T ≅ (I n).modules := Functor.isoWhiskerLeft (I n).modules
    (SheafOfModules.systemScalarModelUnit rfl A) ≪≫ (I n).modules.rightUnitor
  exact SheafOfModules.kFlat_iso_independent (F n)
    ((NatIso.mapHomologicalComplex e (.up ℤ)).app P) ht.1

include uPush adj in
/-- An ordinary inverse system carries flat-term K-flat complexes to K-flat complexes. -/
theorem ordinaryInverseSystem_kflat [∀ n, (I n).modules.Additive]
    (P : OrdinaryInverseSystem.{c, v, r} J B τ J' uInv F σ I) [P.pull.Additive]
    (K : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
    (hK : CochainComplex.IsKFlatIndependentCoefficients (R := systemRing.{c, v, max c v r} J B τ) K)
    (hf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := coefficientSequenceTopology J)
      (R := systemRing.{c, v, max c v r} J B τ) (K.X i)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := systemRing.{c, v, max c v r} J' F σ)
      ((P.pull.mapHomologicalComplex (.up ℤ)).obj K) := by
  have hk (n : ℕ) := SheafOfModules.systemSequenceEvaluation_preservesKFlat
    (rings.{c, v, max c v r} J B τ) n K hK hf
  have he (n : ℕ) := finite_kflat.{c, v, r} J B J' uInv uPush adj F I n
    (((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up ℤ)).obj K)
    (by simpa only [← evaluation_sequence.{c, v, r}] using (hk n).1)
    (by simpa only [← evaluation_sequence.{c, v, r}] using (hk n).2)
  have hout (n : ℕ) : CochainComplex.IsKFlatIndependentCoefficients (R := F n)
      (((evaluation.{c, v, max c v r} J' F σ n).mapHomologicalComplex (.up ℤ)).obj
        ((P.pull.mapHomologicalComplex (.up ℤ)).obj K)) := by
    let e := (NatIso.mapHomologicalComplex (P.component n) (.up ℤ)).app K
    exact SheafOfModules.kFlat_iso_independent (F n) e.symm (he n)
  let T := (P.pull.mapHomologicalComplex (.up ℤ)).obj K
  let R := systemRing.{c, v, max c v r} J' F σ
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro Z hZ i
  apply (systemsComponentwise.{c, v, r} J' F σ _).2
  intro n
  have hn : (((evaluation.{c, v, max c v r} J' F σ n).mapHomologicalComplex
      (.up ℤ)).obj Z).Acyclic := by
    intro j
    exact (hZ j).map (evaluation.{c, v, max c v r} J' F σ n)
  exact (hout n _ hn i).of_iso (WeilConjectures.evaluationTotalIso.{c, v, r} J' F σ n Z T).symm

end WeilConjectures.SemilinearSections
