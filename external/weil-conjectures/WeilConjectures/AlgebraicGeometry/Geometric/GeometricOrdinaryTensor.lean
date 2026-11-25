/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geometric.GeometricOrdinaryRealization
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricTensorComponentHorizontal
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricOrdinaryKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearTensorEvaluation
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearSystemIsoAssembly
import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly

/-! # Ordinary tensor preservation for the termwise geometric realization

Source: Zheng Construction 4.1; Stacks 03EL and 0G7E.
(blueprint: lem-coef-semilinear-geometric-ordinary-tensor)
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush)
  (O : GeometryOrdinary.{c, v, r} J B τ J' uInv uPush adjSet)

/-- Ordinary tensor comparisons and preservation of the resolving class.
There are no derived tensor functors or localized comparisons in this record.
Source: Zheng Construction 4.1; Stacks 03EL and 0G7E.
(blueprint: lem-coef-semilinear-geometric-ordinary-tensor). -/
structure GeometryOrdinaryTensor where
  /-- The level comparison on ordinary module sheaves. -/
  level : ∀ (n : ℕ) (M N : Mod.{c, v, max c v r} J (B n)),
    (O.inverseImage n).modules.obj (ordinaryTensor.{c, v, r} J (B n) M N) ≅
      ordinaryTensor.{c, v, r} J' (O.coefficients n)
        ((O.inverseImage n).modules.obj M) ((O.inverseImage n).modules.obj N)
  /-- Naturality before taking complexes. -/
  level_natural : ∀ (n : ℕ) {M M' N N' : Mod.{c, v, max c v r} J (B n)}
    (f : M ⟶ M') (g : N ⟶ N'),
    (O.inverseImage n).modules.map (ordinaryTensorHom.{c, v, r} J (B n) f g) ≫
        (level n M' N').hom =
      (level n M N).hom ≫ ordinaryTensorHom.{c, v, r} J' (O.coefficients n)
        ((O.inverseImage n).modules.map f) ((O.inverseImage n).modules.map g)
  /-- The inverse image of a pure tensor is the tensor of the inverse images. -/
  level_pure : ∀ n : ℕ,
    InverseTensorPure.{c, v, r} J J' uInv (B n) (O.coefficients n) (O.inverseImage n) (level n)
  /-- The comparison on ordinary systems with their actual horizontal transitions. -/
  system : ∀ M N : Systems.{c, v, max c v r} J B τ,
    O.pull.obj (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ) M N) ≅
      ordinaryTensor.{c, v, r} (coefficientSequenceTopology J')
        (systemRing.{c, v, max c v r} J' O.coefficients O.coefficientTransition)
        (O.pull.obj M) (O.pull.obj N)
  /-- Naturality on ordinary systems. -/
  system_natural : ∀ {M M' N N' : Systems.{c, v, max c v r} J B τ}
    (f : M ⟶ M') (g : N ⟶ N'),
    O.pull.map (ordinaryTensorHom.{c, v, r} (coefficientSequenceTopology J)
        (systemRing.{c, v, max c v r} J B τ) f g) ≫ (system M' N').hom =
      (system M N).hom ≫ ordinaryTensorHom.{c, v, r} (coefficientSequenceTopology J')
        (systemRing.{c, v, max c v r} J' O.coefficients O.coefficientTransition)
        (O.pull.map f) (O.pull.map g)
  /-- The ordinary evaluation square. -/
  evaluation : ∀ (n : ℕ) (M N : Systems.{c, v, max c v r} J B τ),
    (SemilinearSections.evaluation.{c, v, max c v r}
        J' O.coefficients O.coefficientTransition n).map (system M N).hom ≫
      (ordinaryEvaluationTensor.{c, v, r} J' O.coefficients O.coefficientTransition n
        (O.pull.obj M) (O.pull.obj N)).hom ≫
      ordinaryTensorHom.{c, v, r} J' (O.coefficients n)
        ((O.ordinaryPullEvaluation n).hom.app M) ((O.ordinaryPullEvaluation n).hom.app N) =
      (O.ordinaryPullEvaluation n).hom.app
        (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ) M N) ≫
        (O.inverseImage n).modules.map (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom ≫
        (level n ((SemilinearSections.evaluation.{c, v, max c v r} J B τ n).obj M)
          ((SemilinearSections.evaluation.{c, v, max c v r} J B τ n).obj N)).hom
  /-- Inverse image at a level preserves flat-term K-flat representatives. -/
  level_kflat : ∀ (n : ℕ) (P : CochainComplex (Mod.{c, v, max c v r} J (B n)) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := B n) P →
    flatTerms.{c, v, r} J (B n) P →
    CochainComplex.IsKFlatIndependentCoefficients (J := J') (R := O.coefficients n)
      (((O.inverseImage n).modules.mapHomologicalComplex (.up ℤ)).obj P)
  /-- Inverse image on the sequence site preserves the same resolving class. -/
  system_kflat : ∀ (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := coefficientSequenceTopology J)
      (R := systemRing.{c, v, max c v r} J B τ) P →
    flatTerms.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ) P →
    CochainComplex.IsKFlatIndependentCoefficients (J := coefficientSequenceTopology J')
      (R := systemRing.{c, v, max c v r} J' O.coefficients O.coefficientTransition)
      ((O.pull.mapHomologicalComplex (.up ℤ)).obj P)

section Level
variable (R : Sheaf J CommRingCat.{max c v r}) (S : Sheaf J' CommRingCat.{max c v r})
  (I : SheafOfModules.AlgebraicInverseImage uInv R S)

include adjSet in
private theorem inverse_tensor [PreservesFiniteLimits uInv] :
    ∃ μ : ∀ M N : Mod.{c, v, max c v r} J R,
      I.modules.obj (ordinaryTensor.{c, v, r} J R M N) ≅
        ordinaryTensor.{c, v, r} J' S (I.modules.obj M) (I.modules.obj N),
      (∀ {M M' N N' : Mod.{c, v, max c v r} J R} (f : M ⟶ M') (g : N ⟶ N'),
        I.modules.map (ordinaryTensorHom.{c, v, r} J R f g) ≫ (μ M' N').hom =
          (μ M N).hom ≫ ordinaryTensorHom.{c, v, r} J' S
            (I.modules.map f) (I.modules.map g)) ∧
      InverseTensorPure.{c, v, r} J J' uInv R S I μ := by
  obtain ⟨μ, hn, hp⟩ :=
    SheafOfModules.CochainInversePairing.exists_inverseImageTensorComparison
      R S uInv I uPush adjSet
  exact ⟨μ, hn, hp⟩

end Level

section ComponentNaturality
open CategoryTheory.MonoidalCategory
variable (μ : ∀ (n : ℕ) (M N : Mod.{c, v, max c v r} J (B n)),
  (O.inverseImage n).modules.obj (ordinaryTensor.{c, v, r} J (B n) M N) ≅
    ordinaryTensor.{c, v, r} J' (O.coefficients n)
      ((O.inverseImage n).modules.obj M) ((O.inverseImage n).modules.obj N))
  (hn : ∀ (n : ℕ) {M M' N N' : Mod.{c, v, max c v r} J (B n)}
    (f : M ⟶ M') (g : N ⟶ N'),
    (O.inverseImage n).modules.map (ordinaryTensorHom.{c, v, r} J (B n) f g) ≫
      (μ n M' N').hom = (μ n M N).hom ≫ ordinaryTensorHom.{c, v, r} J' (O.coefficients n)
        ((O.inverseImage n).modules.map f) ((O.inverseImage n).modules.map g))

include hn in
private theorem component_natural (n : ℕ)
    {M M' N N' : Systems.{c, v, max c v r} J B τ} (f : M ⟶ M') (g : N ⟶ N') :
    (evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).map
        (O.pull.map (ordinaryTensorHom.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ) f g)) ≫
      (geometricTensorComponent.{c, v, r} J B τ J' uInv uPush adjSet O μ n M' N').hom =
    (geometricTensorComponent.{c, v, r} J B τ J' uInv uPush adjSet O μ n M N).hom ≫
      (evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).map
        (ordinaryTensorHom.{c, v, r} (coefficientSequenceTopology J')
          (systemRing.{c, v, max c v r} J' O.coefficients O.coefficientTransition)
          (O.pull.map f) (O.pull.map g)) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients (B n)
  let := SheafOfModules.isMonoidal_W_independentCoefficients (O.coefficients n)
  let := SheafOfModules.isMonoidal_W_independentCoefficients (systemRing J B τ)
  let := SheafOfModules.isMonoidal_W_independentCoefficients
    (systemRing J' O.coefficients O.coefficientTransition)
  let := SheafOfModules.monoidalCategory (B n)
  let := SheafOfModules.monoidalCategory (O.coefficients n)
  let := SheafOfModules.monoidalCategory (systemRing J B τ)
  let := SheafOfModules.monoidalCategory
    (systemRing J' O.coefficients O.coefficientTransition)
  let E := evaluation.{c, v, max c v r} J B τ n
  let E' := evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n
  let L := (O.inverseImage n).modules
  let a : tensor _ ⋙ E ≅ E.prod E ⋙ tensor _ :=
    NatIso.ofComponents (fun MN ↦ ordinaryEvaluationTensor.{c, v, r} J B τ n MN.1 MN.2)
      (fun f ↦ evaluation_tensor_natural.{c, v, r} J B τ n f.1 f.2)
  let b : tensor _ ⋙ L ≅ L.prod L ⋙ tensor _ :=
    NatIso.ofComponents (fun MN ↦ μ n MN.1 MN.2) (fun f ↦ hn n f.1 f.2)
  let a' : tensor _ ⋙ E' ≅ E'.prod E' ⋙ tensor _ :=
    NatIso.ofComponents
      (fun MN ↦ ordinaryEvaluationTensor.{c, v, r} J' O.coefficients
        O.coefficientTransition n MN.1 MN.2)
      (fun f ↦ evaluation_tensor_natural.{c, v, r} J' O.coefficients
        O.coefficientTransition n f.1 f.2)
  let e : tensor _ ⋙ O.pull ⋙ E' ≅ O.pull.prod O.pull ⋙ tensor _ ⋙ E' :=
    Functor.isoWhiskerLeft (tensor _) (O.ordinaryPullEvaluation n) ≪≫
      Functor.isoWhiskerRight a L ≪≫
      Functor.isoWhiskerLeft (E.prod E) b ≪≫
      (Functor.isoWhiskerRight
        (NatIso.prod (O.ordinaryPullEvaluation n) (O.ordinaryPullEvaluation n))
        (tensor _)).symm ≪≫
      (Functor.isoWhiskerLeft (O.pull.prod O.pull) a').symm
  unfold geometricTensorComponent
  exact e.hom.naturality (show (M, N) ⟶ (M', N') from (f, g))
private theorem component_square (n : ℕ) (M N : Systems.{c, v, max c v r} J B τ) :
    (geometricTensorComponent.{c, v, r} J B τ J' uInv uPush adjSet O μ n M N).hom ≫
      (ordinaryEvaluationTensor.{c, v, r} J' O.coefficients O.coefficientTransition n
        (O.pull.obj M) (O.pull.obj N)).hom ≫
      ordinaryTensorHom.{c, v, r} J' (O.coefficients n)
        ((O.ordinaryPullEvaluation n).hom.app M) ((O.ordinaryPullEvaluation n).hom.app N) =
    (O.ordinaryPullEvaluation n).hom.app
        (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ) M N) ≫
      (O.inverseImage n).modules.map (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom ≫
      (μ n ((evaluation.{c, v, max c v r} J B τ n).obj M)
        ((evaluation.{c, v, max c v r} J B τ n).obj N)).hom := by
  let : HasSheafify J' AddCommGrpCat.{max c v r} := abelianSheafify J'
  let : J'.WEqualsLocallyBijective AddCommGrpCat.{max c v r} := locallyBijective J'
  let := SheafOfModules.isMonoidal_W_independentCoefficients (O.coefficients n)
  let := SheafOfModules.monoidalCategory (O.coefficients n)
  unfold geometricTensorComponent
  dsimp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, CategoryTheory.MonoidalCategory.tensorIso_hom]
  unfold ordinaryTensorHom
  simp only [Category.assoc, Iso.inv_hom_id_assoc,
    CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom,
    Iso.inv_hom_id_app]
  erw [CategoryTheory.MonoidalCategory.id_tensorHom_id, Category.comp_id]

end ComponentNaturality

/-- The ordinary pure-tensor construction and its K-flat preservation property.
Source: Zheng Construction 4.1; Stacks 03EL and 0G7E.
(blueprint: lem-coef-semilinear-geometric-ordinary-tensor).

Proof: the balanced pairing on inverse-image sheaves gives the level tensor comparison.
The algebraic inverse-image graph equations transport its additivity and balancing;
the sheaf tensor universal property gives the inverse and naturality. The generalized
pure-tensor formula determines the comparison uniquely. Apply these level maps to
the components of a strict system. Naturality for the coefficient-restriction maps,
and O.ordinaryPullTransition, show compatibility with the actual horizontal maps.
Thus the maps and their inverses reassemble to system isomorphisms. Their evaluation
square is the defining component equation; joint faithfulness is used only for
ordinary system maps. For level K-flatness use ringed-topos pullback (Stacks 0G7E),
then remove its identity scalar extension by the scalar unit isomorphism. Exact,
jointly faithful evaluations detect acyclicity of system complexes. The ordinary
evaluation tensor isomorphism commutes with tensor totals, since evaluation has the
sectionwise coextension right adjoint and therefore preserves coproducts. It follows
that a system complex whose evaluations are K-flat is K-flat. Evaluate a flat-term
K-flat source complex, apply level inverse-image preservation, and transport along
O.ordinaryPullEvaluation to obtain the system clause. No derived tensor comparison
is constructed. -/
theorem geometricOrdinaryTensor_exists [PreservesFiniteLimits uInv] :
    Nonempty (GeometryOrdinaryTensor.{c, v, r} J B τ J' uInv uPush adjSet O) := by
  classical
  have hl (n : ℕ) := inverse_tensor.{c, v, r} J J' uInv uPush adjSet
    (B n) (O.coefficients n) (O.inverseImage n)
  choose μ hn hp using hl
  let δ (M N : Systems.{c, v, max c v r} J B τ) :
      O.pull.obj (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
        (systemRing.{c, v, max c v r} J B τ) M N) ≅
      ordinaryTensor.{c, v, r} (coefficientSequenceTopology J')
        (systemRing.{c, v, max c v r} J' O.coefficients O.coefficientTransition)
        (O.pull.obj M) (O.pull.obj N) :=
    (systemIsoOfEvaluation_exists.{c, v, r} J' O.coefficients O.coefficientTransition
      (M := O.pull.obj (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
        (systemRing.{c, v, max c v r} J B τ) M N))
      (N := ordinaryTensor.{c, v, r} (coefficientSequenceTopology J')
        (systemRing.{c, v, max c v r} J' O.coefficients O.coefficientTransition)
        (O.pull.obj M) (O.pull.obj N))
      (fun n ↦ geometricTensorComponent.{c, v, r} J B τ J' uInv uPush adjSet O μ n M N)
      (geometricTensorComponent_horizontal.{c, v, r} J B τ J' uInv uPush adjSet O μ hp M N)).choose
  have hδ (n : ℕ) (M N : Systems.{c, v, max c v r} J B τ) :
      (evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).map
        (δ M N).hom =
      (geometricTensorComponent.{c, v, r} J B τ J' uInv uPush adjSet O μ n M N).hom :=
    (systemIsoOfEvaluation_exists.{c, v, r} J' O.coefficients O.coefficientTransition
      (M := O.pull.obj (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
        (systemRing.{c, v, max c v r} J B τ) M N))
      (N := ordinaryTensor.{c, v, r} (coefficientSequenceTopology J')
        (systemRing.{c, v, max c v r} J' O.coefficients O.coefficientTransition)
        (O.pull.obj M) (O.pull.obj N))
      (fun k ↦ geometricTensorComponent.{c, v, r} J B τ J' uInv uPush adjSet O μ k M N)
      (geometricTensorComponent_horizontal.{c, v, r}
        J B τ J' uInv uPush adjSet O μ hp M N)).choose_spec n
  refine ⟨{
    level := μ
    level_natural := hn
    level_pure := hp
    system := δ
    system_natural := ?_
    evaluation := ?_
    level_kflat := ?_
    system_kflat := ?_ }⟩
  · intro M M' N N' f g
    have hj : JointlyFaithful
        (evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition) := by
      constructor
      intro M N f g h
      ext X x
      exact congrArg (fun k ↦ k.val.app (op X.unop.2) x) (h X.unop.1)
    apply hj.map_injective
    intro n
    rw [Functor.map_comp, Functor.map_comp, hδ, hδ]
    exact component_natural.{c, v, r} J B τ J' uInv uPush adjSet O μ hn n f g
  · intro n M N
    rw [hδ]
    exact component_square.{c, v, r} J B τ J' uInv uPush adjSet O μ n M N
  · exact (geometricOrdinary_kflat.{c, v, r} J B τ J' uInv uPush adjSet O).1
  · exact (geometricOrdinary_kflat.{c, v, r} J B τ J' uInv uPush adjSet O).2

end WeilConjectures.SemilinearSections
