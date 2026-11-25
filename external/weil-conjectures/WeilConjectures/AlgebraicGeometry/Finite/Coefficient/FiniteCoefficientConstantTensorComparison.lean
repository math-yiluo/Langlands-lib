/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientLocalHomologyModels
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientPreviousLocalComplexesChartHomology
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.ProEtaleSheafificationTensorComparison
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.LinearAlgebra.TensorProduct.Tower
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence

/-! # Tensor compatibility of ordinary constant coefficient realization

Source: Stacks Project, Modules on Sites, Tags 03CY, 03EL and 0GMW.
(blueprint: lem-weil-pbc-finite-coefficient-constant-tensor-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective ULift.algebra'
attribute [local irreducible] completedAdicChangeData
  SheafOfModules.tensorObjIsoSheafification
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

private abbrev layerLift (B : Type t) [CommRing B] :
    ModuleCat.{t} B ⥤ ModuleCat.{t + 1} (ULift.{t + 1} B) :=
  ModuleCat.uliftFunctor.{t + 1, t} B ⋙ ModuleCat.restrictScalars.{t + 1}
    (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom

private def layerLiftTensor {B : Type t} [CommRing B] (M N : ModuleCat.{t} B) :
    (layerLift B).obj (M ⊗ N) ≅ (layerLift B).obj M ⊗ (layerLift B).obj N :=
  (show ULift.{t + 1} (M ⊗[B] N) ≃ₗ[ULift.{t + 1} B]
      (ULift.{t + 1} M ⊗[ULift.{t + 1} B] ULift.{t + 1} N) from
    { (TensorProduct.AlgebraTensorModule.uliftEquiv B B M N).toAddEquiv with
      map_smul' := fun b x ↦
        (TensorProduct.AlgebraTensorModule.uliftEquiv B B M N).map_smul b.down x
    }).toModuleIso

@[irreducible] private def layerConstantTensor (X : Scheme.{t}) (B : Type t) [CommRing B]
    (N : ModuleCat.{t} B) :
    letI := SheafOfModules.monoidalCategory (adicConstantRing X B)
    baseConstantFunctor X B ⋙ tensorRight ((baseConstantFunctor X B).obj N) ≅
      tensorRight N ⋙ baseConstantFunctor X B := by
  letI := SheafOfModules.monoidalCategory (adicConstantRing X B)
  let O := (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1} B))
  letI : MonoidalCategory (PresheafOfModules.{t + 1}
      ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{t + 1} B)))) :=
    PresheafOfModules.monoidalCategory (R := O)
  let L := layerLift B ⋙
    siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} B)
  have := (koszulConstantUnit_local X B).1
  have := (koszulConstantUnit_local X B).2
  let S := PresheafOfModules.sheafification (koszulConstantUnit X B)
  let e := (PresheafOfModules.exists_sheafificationTensorIso_proEtaleUniverses
    (O := O) (R := adicConstantRing X B) (koszulConstantUnit X B)).choose
  let q : baseConstantFunctor X B ⋙ tensorRight ((baseConstantFunctor X B).obj N) ≅
      L ⋙ tensorRight (L.obj N) ⋙ S := by
    refine NatIso.ofComponents (fun M ↦ e.app (L.obj M, L.obj N)) ?_
    intro M M' f
    have h := e.hom.naturality (X := (L.obj M, L.obj N))
      (Y := (L.obj M', L.obj N)) (L.map f, 𝟙 (L.obj N))
    change (S.map (L.map f) ⊗ₘ S.map (𝟙 (L.obj N))) ≫
        (e.app (L.obj M', L.obj N)).hom =
      (e.app (L.obj M, L.obj N)).hom ≫ S.map (L.map f ⊗ₘ 𝟙 (L.obj N)) at h
    simp only [S.map_id, tensorHom_id] at h
    change S.map (L.map f) ▷ S.obj (L.obj N) ≫
        (e.app (L.obj M', L.obj N)).hom =
      (e.app (L.obj M, L.obj N)).hom ≫ S.map (L.map f ▷ L.obj N)
    exact h
  let k : L ⋙ tensorRight (L.obj N) ≅ tensorRight N ⋙ L := by
    refine NatIso.ofComponents (fun M ↦ PresheafOfModules.isoMk
      (fun _ ↦ (layerLiftTensor M N).symm) ?_) ?_
    · intro U V f
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro x y
      rfl
    · intro M M' f
      apply PresheafOfModules.hom_ext
      intro U
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro x y
      rfl
  exact q ≪≫ Functor.isoWhiskerRight k S

@[irreducible] private def layerChangeTensor (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (N : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) :
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.monoidalCategory S
    tensorRight N ⋙ completedAdicChange X φ ≅
      completedAdicChange X φ ⋙ tensorRight ((completedAdicChange X φ).obj N) := by
  letI : EssentiallySmall.{t + 1} X.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.monoidalCategory S
  let E := completedAdicChange X φ
  let E' := SheafOfModules.CoefficientOrdinaryProof.tensorFunctor.{t + 1, t + 1, t} φ
  let hE : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M :=
    (completedAdicChangeData X φ).choose_spec.choose
  let e : E ≅ E' := NatIso.ofComponents (fun M ↦ eqToIso (hE M)) (by
      intro M M' f
      change E.map f ≫ eqToHom (hE M') =
        eqToHom (hE M) ≫ SheafOfModules.changeOfRingsHom φ M f
      have hm : E.map f = eqToHom (hE M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫
          eqToHom (hE M').symm :=
        (completedAdicChangeData X φ).choose_spec.choose_spec.choose f
      rw [hm]
      simp)
  let c := Classical.choice (SheafOfModules.scalarExtension_constraint_coherence R S φ)
  let q : tensorRight N ⋙ E' ≅ E' ⋙ tensorRight (E'.obj N) := by
    refine NatIso.ofComponents (fun M ↦ c.tensorIso M N) ?_
    intro M M' f
    have h : E'.map (f ⊗ₘ 𝟙 N) ≫ (c.tensorIso M' N).hom =
        (c.tensorIso M N).hom ≫ (E'.map f ⊗ₘ E'.map (𝟙 N)) :=
      c.natural M N M' N f (𝟙 N)
    have hid : E'.map (𝟙 N) = 𝟙 (E'.obj N) := E'.map_id N
    rw [hid] at h
    have ht : (E'.map f ⊗ₘ 𝟙 (E'.obj N)) = E'.map f ▷ E'.obj N :=
      tensorHom_id _ _
    rw [ht, tensorHom_id] at h
    exact h
  exact Functor.isoWhiskerLeft (tensorRight N) e ≪≫ q ≪≫
    Functor.isoWhiskerLeft E' ((curriedTensor _).flip.mapIso (e.app N).symm) ≪≫
      Functor.isoWhiskerRight e.symm (tensorRight (E.obj N))

/-- Ordinary constant realization carries tensor products to sheaf tensor products.

Source: Stacks Project, Modules on Sites, Tags 03CY, 03EL and 0GMW.
(blueprint: lem-weil-pbc-finite-coefficient-constant-tensor-comparison).

Proof: the lifted pure-tensor equivalence identifies the constant presheaf of a
module tensor with the sectionwise tensor of the constant presheaves. Apply the
module-sheafification tensor comparison and its naturality. Ordinary coefficient
extension preserves tensors by the balanced scalar-extension comparison. Identify
that extension with the prescribed completedAdicChange functor using its object
and morphism equalities, then compose the two natural isomorphisms. No flatness,
finite generation, nonzero-ring or nonempty-site hypothesis is used. -/
theorem finiteCoefficient_constant_tensor_comparison (X : Scheme.{t})
    (B : Type t) [CommRing B]
    {R : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : adicConstantRing X B ⟶ R) (N : ModuleCat.{t} B) :
    letI := SheafOfModules.monoidalCategory R
    Nonempty (finiteCoefficientConstantFunctor X B φ ⋙
        tensorRight ((finiteCoefficientConstantFunctor X B φ).obj N) ≅
      tensorRight N ⋙ finiteCoefficientConstantFunctor X B φ) := by
  let := SheafOfModules.monoidalCategory R
  exact ⟨Functor.isoWhiskerLeft (baseConstantFunctor X B)
      (layerChangeTensor X φ ((baseConstantFunctor X B).obj N)).symm ≪≫
    Functor.isoWhiskerRight (layerConstantTensor X B N) (completedAdicChange X φ)⟩

end AlgebraicGeometry.Scheme
