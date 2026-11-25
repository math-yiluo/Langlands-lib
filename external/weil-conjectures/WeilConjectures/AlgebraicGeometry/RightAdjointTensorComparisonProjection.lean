/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.PerfectTensorHomDuality
import WeilConjectures.CategoryTheory.MonoidalProjectionConjugate
import WeilConjectures.AlgebraicGeometry.DerivedQCohPerfectGeneration
import WeilConjectures.AlgebraicGeometry.PerfectLocalizingIsoLocus
import WeilConjectures.AlgebraicGeometry.DerivedExactStructures
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.DerivedTensorRightCoproducts
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesDirectSums
import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSumsAux
import WeilConjectures.AlgebraicGeometry.DerivedTensorQCohClosure
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh

/-! # The pinned quasi-coherent projection formula

Source: Stacks Project, Tag 08EU, with perfect generation (Tag 09IS) and
perfect tensor-Hom duality (Tags 0B54 and 0A9T).
(blueprint: lem-sc-right-adjoint-tensor-comparison-projection).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
open CategoryTheory.ShiftSaturated
/-- Projection formula isomorphisms with the pinned inverse equation.
Source: Stacks Project, Tag 08EU; perfect generation is Tag 09IS.
Proof: fix E = c(O_Y) and use hRf to regard Rf_*E as quasi-coherent. For perfect K,
tensor-Hom duality identifies the displayed mate with the conjugate of the
monoidal tensorator at its dual, so it is invertible. The mates are natural in K.
Use the predicate that the mate is invertible at every integer translate of K.
This predicate is stable under retracts and coproducts by naturality and
coproduct preservation. It is stable under cones by a five-term exact-sequence
argument using the mate at A, B, A[1] and B[1]. The fourth and fifth vertical
maps use those components transported by the functors' exact shift structures;
no shift compatibility of the mate is required. Perfect objects are closed
under every translate, so perfect generation proves the predicate for all K.
Its value at shift zero gives the required invertibility. Invert the canonical
component to obtain pf; its inverse is the specified mate by construction.
(blueprint: lem-sc-right-adjoint-tensor-comparison-projection) -/
theorem exists_rightAdjointTensorComparison_projection
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (hRf : ∀ E : schemeDerivedQCohCategory Z,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj))
    (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
    [Functor.Monoidal (derivedPullback f)]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory Z) :
    ∃ pf : ∀ K : schemeDerivedQCohCategory Y,
      (schemeDerivedDirectImage f).obj
          (((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
        K.obj ⊗ (schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj,
      ∀ K, (pf K).inv = (a.homEquiv _ _)
          ((Functor.Monoidal.μIso (derivedPullback f) K.obj
            ((schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)).inv ≫
            (derivedPullback f).obj K.obj ◁ a.counit.app (c.obj ⟨𝟙_ _, hO⟩).obj) := by
  classical
  let E := c.obj ⟨𝟙_ _, hO⟩
  let RE : schemeDerivedQCohCategory Y :=
    ⟨(schemeDerivedDirectImage f).obj E.obj, hRf E⟩
  let P : ObjectProperty (schemeDerivedQCohCategory Y) := fun K ↦
    IsIso ((a.homEquiv _ _)
      ((Functor.Monoidal.μIso (derivedPullback f) K.obj
        RE.obj).inv ≫
          (derivedPullback f).obj K.obj ◁ a.counit.app E.obj))
  have hperfect (K : schemeDerivedQCohCategory Y)
      (hK : Scheme.perfectSubcategory Y K.obj) : P K := by
    obtain ⟨L, ⟨pair⟩, _⟩ := perfect_tensor_hom_duality Y K hK
    let : ExactPairing K.obj L.obj := pair
    let F := derivedPullback f
    let R := schemeDerivedDirectImage f
    let : ExactPairing (F.obj K.obj) (F.obj L.obj) := ExactPairing.map F K.obj L.obj
    let b₁ := (tensorLeftAdjunction K.obj L.obj).comp a
    let b₂ := a.comp (tensorLeftAdjunction (F.obj K.obj) (F.obj L.obj))
    have h : IsIso ((conjugateEquiv b₁ b₂
        (Functor.Monoidal.commTensorLeft F L.obj).hom).app E.obj) := by
      infer_instance
    change IsIso _
    rw [← monoidal_projection_conjugate F R a K.obj L.obj E.obj]
    exact h
  let τ : (schemeDerivedQCohProperty Y).ι ⋙
      tensorRight RE.obj ⟶
      (schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙
        tensorRight E.obj ⋙ schemeDerivedDirectImage f :=
    { app := fun K ↦ (a.homEquiv _ _)
        ((Functor.Monoidal.μIso (derivedPullback f) K.obj
          RE.obj).inv ≫
            (derivedPullback f).obj K.obj ◁ a.counit.app E.obj)
      naturality := by
        intro K L g
        change g.hom ▷ RE.obj ≫ _ =
          _ ≫ (schemeDerivedDirectImage f).map
            ((derivedPullback f).map g.hom ▷ E.obj)
        apply a.homEquiv_naturality_left_square
        simp only [Functor.Monoidal.μIso_inv]
        rw [← Category.assoc, ← Functor.OplaxMonoidal.δ_natural_left]
        simp only [Category.assoc]
        rw [← whisker_exchange] }
  let := qc_triangulated Y
  let F := (schemeDerivedQCohProperty Y).ι ⋙ tensorRight RE.obj
  let G := (schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙
    tensorRight E.obj ⋙ schemeDerivedDirectImage f
  obtain ⟨sF, sG, hFexact, hGexact⟩ := projection_exactStructures f a E.obj
  let := sF
  let := sG
  let : F.IsTriangulated := hFexact
  let : G.IsTriangulated := hGexact
  have hFsums (J : Type u) : PreservesColimitsOfShape (Discrete J) F := by
    let : HasCoproducts.{u} (schemeDerivedCategory Y) := derivedAmbientHasCoproducts Y
    let : (schemeDerivedQCohProperty Y).IsClosedUnderColimitsOfShape (Discrete J) :=
      schemeDerivedQCohClosedUnderCoproducts Y J
    let : PreservesColimitsOfShape (Discrete J) (tensorRight RE.obj) :=
      derivedTensorRight_preservesCoproducts Y RE.obj J
    infer_instance
  have hGsums (J : Type u) : PreservesColimitsOfShape (Discrete J) G := by
    let : ∀ K : J → schemeDerivedQCohCategory Y,
        PreservesColimit (Discrete.functor K) G := by
      intro K
      let : HasCoproducts.{u} (schemeDerivedCategory Y) := derivedAmbientHasCoproducts Y
      let : (schemeDerivedQCohProperty Y).IsClosedUnderColimitsOfShape (Discrete J) :=
        schemeDerivedQCohClosedUnderCoproducts Y J
      let : PreservesColimitsOfShape (Discrete J) (derivedPullback f) :=
        a.leftAdjoint_preservesColimits.preservesColimitsOfShape
      let : PreservesColimitsOfShape (Discrete J) (tensorRight E.obj) :=
        derivedTensorRight_preservesCoproducts Z E.obj J
      let H := (schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙ tensorRight E.obj
      have hqcH (A : schemeDerivedQCohCategory Y) : schemeDerivedQCohProperty Z (H.obj A) :=
        canonical_derivedTensor_preserve_QCoh Z _ E.obj
          ((derivedPullback_tensor_preserve_QCoh f).1 A.obj A.property) E.property
      let : PreservesColimit (Discrete.functor K ⋙ H) (schemeDerivedDirectImage f) := by
        apply (preservesColimit_iff_of_iso_diagram (schemeDerivedDirectImage f)
          (Discrete.natIsoFunctor (F := Discrete.functor K ⋙ H))).mpr
        exact derivedDirectImagePreservesDirectSums f J
          (fun j ↦ ⟨H.obj (K j), hqcH (K j)⟩)
      change PreservesColimit (Discrete.functor K) (H ⋙ schemeDerivedDirectImage f)
      exact comp_preservesColimit _ _
    exact preservesColimitsOfShape_of_discrete G
  have hperfectShift (K : schemeDerivedQCohCategory Y)
      (hK : Scheme.perfectSubcategory Y K.obj) : isoOnAllShifts F G τ K := by
    intro n
    exact hperfect (K⟦n⟧) (perfect_iso Y
      (((schemeDerivedQCohProperty Y).ι.commShiftIso n).app K).symm
      (perfect_shift Y hK n))
  have hle := perfectClosure_le_isoOnAllShifts Y F G τ hFsums hGsums hperfectShift
  rw [derivedQCohPerfectGeneration Y] at hle
  have hP (K : schemeDerivedQCohCategory Y) : P K :=
    (NatTrans.isIso_app_iff_of_iso τ ((shiftFunctorZero _ ℤ).app K)).mp (hle K trivial 0)
  refine ⟨fun K ↦ ?_, ?_⟩
  · have : IsIso ((a.homEquiv _ _)
        ((Functor.Monoidal.μIso (derivedPullback f) K.obj RE.obj).inv ≫
          (derivedPullback f).obj K.obj ◁ a.counit.app E.obj)) := hP K
    exact (asIso ((a.homEquiv _ _)
      ((Functor.Monoidal.μIso (derivedPullback f) K.obj RE.obj).inv ≫
        (derivedPullback f).obj K.obj ◁ a.counit.app E.obj))).symm
  · intro K
    rfl

end AlgebraicGeometry
