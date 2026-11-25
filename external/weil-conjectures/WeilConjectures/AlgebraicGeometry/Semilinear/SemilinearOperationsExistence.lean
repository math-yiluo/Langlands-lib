/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geometry.SemilinearGeometryOps
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricOperationsExistence
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarOperationsExistence
import WeilConjectures.AlgebraicGeometry.Open.OpenRestrictionEvaluationSections
import all WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Existence of operations on ordinary semilinear systems

## References

* Zheng, Construction 4.1 and Lemma 4.10
* Stacks Project, Tags 079P, 06YS, 06YY, 07A4 and 08J7--08JB
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe c v r k h d w

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [ambientSmall : EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- The geometric, coefficient-extension, and open-localization operations,
over a given ordinary system calculus. -/
structure SemilinearOperationsData (systems : Data.{c, v, r} J B τ) where
  geometric : ∀ {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
    (J' : GrothendieckTopology C')
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adjSet : uInv ⊣ uPush) [PreservesFiniteLimits uInv],
    {G : Geometry.{c, v, r} J B τ systems J' uInv uPush adjSet //
      G.PullTransitionFormula J B τ systems J' uInv uPush adjSet}
  coefficientExtension : ∀ (F : ℕ → Sheaf J CommRingCat.{max c v r})
    (σ : ∀ n : ℕ, F (n + 1) ⟶ F n) (α : ∀ n : ℕ, B n ⟶ F n)
    (hα : ∀ n : ℕ, α (n + 1) ≫ σ n = τ n ≫ α n),
    ScalarSystems.{c, v, r} J B τ F σ α hα
  localization : ∀ U : C, OpenSystems.{c, v, r} J B τ U

set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option Elab.async false

-- The presentation uses free representables over two different site universes.
private noncomputable def operationRepCorepresentable
    {C₀ : Type c} {D₀ : Type d} [Category.{v} C₀] [Category.{w} D₀]
    {F : C₀ ⥤ D₀} {S : C₀ᵒᵖ ⥤ RingCat.{max c d v w r}}
    {R : D₀ᵒᵖ ⥤ RingCat.{max c d v w r}} (φ : S ⟶ F.op ⋙ R) (X : C₀) :
    (PresheafOfModules.pushforward φ ⋙ coyoneda.obj
      (Opposite.op (SheafOfModules.freeRep.{c,v,max c d v w r} S X))).CorepresentableBy
      (SheafOfModules.freeRep.{d,w,max c d v w r} R (F.obj X)) where
  homEquiv {N} := (SheafOfModules.repEquiv.{d,w,max c d v w r}
    (M := N) (X := F.obj X)).trans
      (SheafOfModules.repEquiv.{c,v,max c d v w r}
        (M := (PresheafOfModules.pushforward φ).obj N) (X := X)).symm
  homEquiv_comp g f := by
    apply SheafOfModules.repEquiv.{c,v,max c d v w r}.injective
    dsimp only [Equiv.trans_apply]
    erw [Equiv.apply_symm_apply, SheafOfModules.repEquiv_comp.{d,w,max c d v w r}]
    conv_rhs => erw [SheafOfModules.repEquiv_comp.{c,v,max c d v w r}]
    erw [Equiv.apply_symm_apply]
    rfl

-- The dependent sheaf and module functors require explicit comparison reductions.
private theorem operationPushRightAdjoint
    {C₀ : Type c} {D₀ : Type d} [Category.{v} C₀] [Category.{w} D₀]
    {J₀ : GrothendieckTopology C₀} {K₀ : GrothendieckTopology D₀}
    {F : C₀ ⥤ D₀} [F.IsContinuous J₀ K₀]
    {S : Sheaf J₀ RingCat.{max c d v w r}}
    {R : Sheaf K₀ RingCat.{max c d v w r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J₀ K₀).obj R) :
    (SheafOfModules.pushforward.{max c d v w r} φ).IsRightAdjoint := by
  have : (PresheafOfModules.pushforward.{max c d v w r} φ.hom).IsRightAdjoint := by
    apply Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    ext M
    simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
    apply Functor.leftAdjointObjIsDefined_of_isColimit
      (SheafOfModules.presentation_isColimit.{c, v, max c d v w r} M)
    rintro (_ | _)
    all_goals
      apply Functor.leftAdjointObjIsDefined_colimit
      intro X
      exact (operationRepCorepresentable.{c,v,r,d,w} φ.hom X.as.1.unop).isCorepresentable
  obtain ⟨hs, hw⟩ := SheafOfModules.coefficientSheafification.{d, w, max c d v w r} K₀
  let := hs
  let := hw
  infer_instance

attribute [local irreducible] systemRing ringPresheaf rings

universe a b av bv da db

private theorem operationExactTranspose
    {A : Type a} {B : Type b} [Category.{av} A] [Category.{bv} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{da} A] [HasDerivedCategory.{db} B]
    {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (adj : L ⊣ R)
    (P : CochainComplex A ℤ) (Q : CochainComplex B ℤ)
    (f : (L.mapHomologicalComplex (.up ℤ)).obj P ⟶ Q) :
    (adj.mapExactDerivedCategory.homEquiv _ _)
      (L.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map f) ≫
        R.mapDerivedCategoryFactors.hom.app Q =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv P Q f) := by
  have hu : adj.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        R.mapDerivedCategoryFactors.inv.app
          ((L.mapHomologicalComplex (.up ℤ)).obj P) ≫
        R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.inv.app P) := by
    simp only [Adjunction.mapExactDerivedCategory, Adjunction.localization_unit_app]
    rfl
  rw [Adjunction.homEquiv_unit, hu, R.mapDerivedCategory.map_comp]
  simp only [Category.assoc, ← R.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
  erw [Category.id_comp]
  have hn := R.mapDerivedCategoryFactors.inv.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  simp only [Iso.inv_hom_id_app]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  erw [Category.comp_id]

private theorem operationOpenSystems (systems : Data.{c, v, r} J B τ) (U : C) :
    Nonempty (OpenSystems.{c, v, r} J B τ U) := by
  let := abelianSheafify.{c,v,max c v r} J
  let := locallyBijective.{c,v,max c v r} J
  let φ := eqToHom (openRing.{c, v, r} J B τ U).symm
  have : (openRestriction.{c, v, r} J B τ U).IsRightAdjoint :=
    operationPushRightAdjoint.{max c v, v, r, c, v} (F := openSite U) φ
  let L := (openRestriction.{c, v, r} J B τ U).leftAdjoint
  let adj : L ⊣ openRestriction.{c, v, r} J B τ U :=
    Adjunction.ofIsRightAdjoint _
  let a (n : ℕ) := @SheafOfModules.localizedSystemAdjunction.{c, v, r} C _ J
    (abelianSheafify.{c, v, max c v r} J)
    (locallyBijective.{c, v, max c v r} J) (B n) U
  let δ (n : ℕ) := (openRestrictionEvaluationSections.{c,v,r} J B τ U n).choose
  have : ((𝟭 ℕ).prod (Over.forget U)).IsContinuous
      (coefficientSequenceTopology (J.over U)) (coefficientSequenceTopology J) :=
    openSite_continuous J U
  have hi (n : ℕ) : IsIso ((mateEquiv adj (a n)).symm (δ n).hom) := by
    apply WeilConjectures.SequenceModuleEvaluation.sequenceModulePullbackEvaluation_isIso
      (J.over U) J (Over.forget U)
      (ring.{max c v, v, max c v r} (coefficientSequenceTopology (J.over U))
        (systemRing.{max c v, v, max c v r} (J.over U)
          (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U)))
      (ring.{c, v, max c v r} (coefficientSequenceTopology J)
        (systemRing.{c, v, max c v r} J B τ)) n φ
      (ring.{max c v, v, max c v r} (J.over U) ((B n).over U))
      (ring.{c, v, max c v r} J (B n))
      (evaluation_ring.{max c v, v, max c v r} (J.over U)
        (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U) n)
      (evaluation_ring.{c, v, max c v r} J B τ n) (𝟙 _)
      L _ adj (a n) (δ n)
  let ι (n : ℕ) := (asIso ((mateEquiv adj (a n)).symm (δ n).hom)).symm
  have : L.Additive := adj.left_adjoint_additive
  have he : ∀ S : ShortComplex _, S.Exact → (S.map L).Exact := by
    intro S hs
    apply (systems.componentwise _).mpr
    intro n
    have : (SheafOfModules.localizedSystemExtension.{c,v,r} (B n) U).Additive :=
      (a n).left_adjoint_additive
    change (S.map (L ⋙ evaluation.{c, v, max c v r} J B τ n)).Exact
    let E := evaluation.{max c v, v, max c v r} (J.over U)
      (openRings.{c,v,r} J B U) (openTransitions.{c,v,r} J B τ U) n
    let T := SheafOfModules.localizedSystemExtension.{c,v,r} (B n) U
    have : PreservesFiniteLimits T :=
      SheafOfModules.localizedSystemExtensionLimits.{c,v,r} (B n) U
    have : PreservesFiniteColimits T :=
      SheafOfModules.localizedSystemExtensionColimits.{c,v,r} (B n) U
    let S' := (S.map E).map T
    let e : S.map (L ⋙ evaluation.{c,v,max c v r} J B τ n) ≅ S' :=
      ShortComplex.isoMk ((ι n).app S.X₁) ((ι n).app S.X₂) ((ι n).app S.X₃)
        (by exact ((ι n).hom.naturality S.f).symm)
        (by exact ((ι n).hom.naturality S.g).symm)
    exact ShortComplex.exact_of_iso e.symm ((hs.map E).map T)
  obtain ⟨hl, hc⟩ := ((Functor.exact_tfae L).out 2 4).mp he
  let := hl
  let := hc
  refine ⟨{
    extension := L
    ordinaryAdjunction := adj
    extensionEvaluation := ι
    restrictionEvaluation := δ
    restrictionSections := fun n N V x ↦
      (openRestrictionEvaluationSections.{c, v, r} J B τ U n).choose_spec N V.unop x
    unit_evaluation := ?_
    counit_evaluation := ?_
    adjunction := adj.mapExactDerivedCategory
    transpose_model := ?_ }⟩
  · intro n M
    have h := unit_mateEquiv_symm adj (a n) (δ n).hom M
    change _ ≫ _ ≫ _ = _
    rw [reassoc_of% h, ← Functor.map_comp]
    change (a n).unit.app _ ≫
      (SheafOfModules.localizedSystemRestriction.{c,v,r} (B n) U).map
        ((asIso ((mateEquiv adj (a n)).symm (δ n).hom)).hom.app M ≫
          (asIso ((mateEquiv adj (a n)).symm (δ n).hom)).inv.app M) = _
    rw [Iso.hom_inv_id_app]
    erw [(SheafOfModules.localizedSystemRestriction.{c,v,r} (B n) U).map_id,
      Category.comp_id]
  · intro n N
    exact mateEquiv_counit_symm adj (a n) (δ n).hom N
  · intro P Q f
    exact operationExactTranspose adj P Q f

/-- Geometric and coefficient operations on a fixed semilinear system calculus. -/
theorem semilinearOperationsData (systems : Data.{c, v, r} J B τ) :
    Nonempty (SemilinearOperationsData.{c, v, r} J B τ systems) := by
  classical
  refine ⟨{
    geometric := fun J' uInv uPush adjSet ↦
      (semilinearGeometricOperations J B τ systems J' uInv uPush adjSet).some
    coefficientExtension := fun F σ α hα ↦
      (semilinearScalarOperations J B τ F σ α hα).some
    localization := fun U ↦ (operationOpenSystems J B τ systems U).some }⟩

end WeilConjectures.SemilinearSections
