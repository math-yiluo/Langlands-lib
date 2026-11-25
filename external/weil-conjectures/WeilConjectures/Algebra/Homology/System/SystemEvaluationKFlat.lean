/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemEvaluationTopos
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
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence

/-! # Simultaneous K-flat representatives for strict systems

Source: Stacks 06YS and 0G7E; Zheng, Construction 4.1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- Sequence-site flat-term K-flat complexes remain flat-term K-flat at every level.
Source: Stacks 0G7E (blueprint: lem-pur-system-evaluation-kflat).
Proof: vertical evaluation is the algebraic inverse image of a geometric morphism.
Apply K-flat pullback along its identity structural ring map. The normalized scalar
unit identifies extension along that identity with the original evaluation. Transport
K-flatness and flatness along this natural isomorphism. -/
theorem systemSequenceEvaluation_preservesKFlat (n : ℕ)
    (P : CochainComplex (systemSequenceModules B) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := systemSequenceRing B) P)
    (hf : ∀ i : ℤ, IsFlatOnSite (R := systemSequenceRing B) (P.X i)) :
    systemLevelKFlat B n
      (((systemSequenceEvaluation B n).mapHomologicalComplex (.up ℤ)).obj P) := by
  classical
  let A : SystemScalarModel (𝟙 (B.obj (op n))) := (nonempty_systemScalarModel _).some
  let F := systemSequenceEvaluation B n
  let T := F ⋙ A.model.E
  have : F.Additive := inferInstance
  have : T.Additive := inferInstance
  have ht := isKFlat_ringedToposPullback
    ((Prod.sectR n C).sheafPushforwardContinuous (Type w) J (coefficientSequenceTopology J))
    ((Prod.sectR n C).sheafPushforwardCocontinuous (Type w) J (coefficientSequenceTopology J))
    (systemSequenceEvaluationToposAdjunction (J := J) n)
    (systemSequenceEvaluationInverseImage B n) (𝟙 (B.obj (op n))) T
    (fun M ↦ A.model.obj_eq (F.obj M)) (fun f ↦ A.model.map_eq (F.map f)) P hP hf
  let e : T ≅ F := Functor.isoWhiskerLeft F (systemScalarModelUnit rfl A) ≪≫ F.rightUnitor
  let ec := (NatIso.mapHomologicalComplex e (.up ℤ)).app P
  exact ⟨kFlat_iso_independent (B.obj (op n)) ec ht.1,
    fun i ↦ flatOnSite_of_iso (B.obj (op n))
      ((HomologicalComplex.eval _ (.up ℤ) i).mapIso ec) (ht.2 i)⟩

/-- Every complex of strict systems has one strict representative which is flat-term
K-flat at every level. Source: Stacks 06YS and 0G7E; Zheng 4.1
(blueprint: lem-pur-system-evaluation-kflat).
Proof: transport the complex to the ringed sequence site and resolve it there by a
flat-term K-flat complex. Pull the resolution back through the sequence-site equivalence.
The unit identifies its augmentation target with the original strict complex. Exactness
of the equivalence preserves its quasi-isomorphism. Every slice is flat-term K-flat by
the evaluation pullback theorem, so the construction resolves all levels simultaneously. -/
theorem strictRingSystem_kFlatResolution (K : CochainComplex (StrictRingSystem B) ℤ) :
    ∃ (L : CochainComplex (StrictRingSystem B) ℤ) (f : L ⟶ K),
      systemComponentwiseKFlat B L ∧ QuasiIso f := by
  classical
  let E := strictSystemSequenceEquivalence B
  let e := E.mapHomologicalComplex (.up ℤ)
  obtain ⟨P, q, hP, hflat, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := systemSequenceRing B) (e.functor.obj K)
  have hflat' (i : ℤ) : IsFlatOnSite (R := systemSequenceRing B) (P.X i) :=
    (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso (systemSequenceRing B) (P.X i)).symm (hflat i)
  let L := e.inverse.obj P
  let f : L ⟶ K := e.inverse.map q ≫ e.unitIso.inv.app K
  have : QuasiIso q := hq
  have : QuasiIso (e.inverse.map q) := by
    change QuasiIso ((E.inverse.mapHomologicalComplex (.up ℤ)).map q)
    infer_instance
  refine ⟨L, f, ?_, ?_⟩
  · intro n
    change systemLevelKFlat B n
      (((systemSequenceEvaluation B n).mapHomologicalComplex (.up ℤ)).obj P)
    exact systemSequenceEvaluation_preservesKFlat B n P hP hflat'
  · dsimp only [f]
    infer_instance

end SheafOfModules
