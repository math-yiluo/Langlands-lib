/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSums
import WeilConjectures.AlgebraicGeometry.DerivedQCohPerfectGeneration
import WeilConjectures.AlgebraicGeometry.ProperPerfectRightAdjointCoproducts
import WeilConjectures.AlgebraicGeometry.SmoothProperTensorPerfectCase
import WeilConjectures.AlgebraicGeometry.PerfectImmersionStalkwiseTorBounds
import WeilConjectures.AlgebraicGeometry.RightAdjointTensorComparisonNatural
import WeilConjectures.AlgebraicGeometry.DerivedTensorRightCoproducts
import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSumsAux
import WeilConjectures.AlgebraicGeometry.PerfectLocalizingIsoLocus
import WeilConjectures.AlgebraicGeometry.DerivedExactStructures
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Tensor formula for the right adjoint of a perfect proper immersion

Source: literature/stacks-project/duality.tex, Tag 0A9U
(projection formula for a perfect proper morphism and its right adjoint)
(blueprint: lem-sc-smooth-proper-diagonal-tensor-formula).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry
open CategoryTheory.ShiftSaturated

/-- For a proper perfect closed immersion, the right adjoint of derived direct image
satisfies the projection formula.  The displayed morphism is the mate, under the
specified adjunction, of the projection-formula morphism.
Source: Stacks Project, Tag 0A9U.
(blueprint: lem-sc-smooth-proper-diagonal-tensor-formula).

Proof (Tag 0A9U, following the five node steps):
1. The closed immersion is proper, finite type and perfect: the stalks of i_*O_Z have
   finite free resolutions by local perfection. By lem-sc-smooth-proper-tensor-direct-sums
   (Tag 0A9R), c commutes with arbitrary set-indexed direct sums.
2. Direct sums exist by lem-pc-derived-qcoh-direct-sums. Use the predicate that the
   natural comparison is invertible at every integer translate. This predicate
   is closed under isomorphisms, shifts, retracts, coproducts and cones. For cones,
   the five-term argument uses independently the components at A, B, A[1] and
   B[1], transported by the two functors' exact shift structures.
3. Perfect objects generate this localizing subcategory by
   lem-pc-derived-qcoh-perfect-generation. The adjoint exists by
   lem-pc-noetherian-derived-direct-image-right-adjoint.
4. The comparison is invertible on perfect K by lem-sc-smooth-proper-tensor-perfect-case
   (Tag 0A9T), with the same counit-pinned projection comparison.
5. The localizing-subcategory argument of Tag 0A9U gives invertibility on every
   translate of every K. Shift zero gives the original counit-pinned conclusion,
   with the same supplied monoidal structure and both specified adjunctions.
-/
theorem smooth_proper_diagonal_tensor_formula
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (i : Z ⟶ Y)
    [IsClosedImmersion i] [IsProper i]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (hperfect : Y.IsPerfect ((schemeDerivedDirectImage i).obj
      (𝟙_ (schemeDerivedCategory Z)))) :
    ∃ (hRf : ∀ E : schemeDerivedQCohCategory Z,
        schemeDerivedQCohProperty Y ((schemeDerivedDirectImage i).obj E.obj))
      (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
      (hTensor : ∀ (K : schemeDerivedQCohCategory Y)
        (E : schemeDerivedQCohCategory Z),
        schemeDerivedQCohProperty Z (((derivedPullback i).obj K.obj) ⊗ E.obj)),
      Nonempty (Functor.Monoidal (derivedPullback i)) ∧
      Nonempty (derivedPullback i ⊣ schemeDerivedDirectImage i) ∧
      ∀ (_ : Functor.Monoidal (derivedPullback i))
        (a : derivedPullback i ⊣ schemeDerivedDirectImage i)
        (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory Z)
        (adj : (schemeDerivedQCohProperty Y).lift
          ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage i) hRf ⊣ c)
        (K : schemeDerivedQCohCategory Y),
        ∃ pf : (schemeDerivedDirectImage i).obj
            (((derivedPullback i).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
          K.obj ⊗ (schemeDerivedDirectImage i).obj (c.obj ⟨𝟙_ _, hO⟩).obj,
          pf.inv = (a.homEquiv _ _)
            ((Functor.Monoidal.μIso (derivedPullback i) K.obj
              ((schemeDerivedDirectImage i).obj (c.obj ⟨𝟙_ _, hO⟩).obj)).inv ≫
              (derivedPullback i).obj K.obj ◁ a.counit.app (c.obj ⟨𝟙_ _, hO⟩).obj) ∧
          IsIso ((adj.homEquiv
            ⟨((derivedPullback i).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj,
              hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩ K)
            (ObjectProperty.homMk (pf.hom ≫
              K.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom))) := by
  obtain ⟨hTor', hTor⟩ := perfectImmersion_stalkwiseTorBounds i hperfect
  obtain ⟨hRf, hO, hTensor, hmon, hadj, hcase⟩ :=
    smoothProper_tensor_perfect_case i hTor'
  refine ⟨hRf, hO, hTensor, hmon, hadj, ?_⟩
  intro mon a c adj K
  let : HasCoproducts.{u} (schemeDerivedQCohCategory Y) := derivedQCohDirectSums Y
  let : HasCoproducts.{u} (schemeDerivedQCohCategory Z) := derivedQCohDirectSums Z
  have hsums := properPerfect_rightAdjoint_preservesCoproducts i hTor
    ((schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage i) hRf)
    ((schemeDerivedQCohProperty Y).liftCompιIso
      ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage i) hRf) c adj
  let := qc_triangulated Y
  let := qc_triangulated Z
  let F := (schemeDerivedQCohProperty Z).lift
    ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback i ⋙
      tensorRight (c.obj ⟨𝟙_ _, hO⟩).obj)
    (fun K ↦ hTensor K (c.obj ⟨𝟙_ _, hO⟩))
  obtain ⟨τ, hτ⟩ := rightAdjointTensorComparison_natural i hRf hO hTensor a c adj
  let P : ObjectProperty (schemeDerivedQCohCategory Y) := fun K ↦
    ∃ pf : (schemeDerivedDirectImage i).obj
            (((derivedPullback i).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
          K.obj ⊗ (schemeDerivedDirectImage i).obj (c.obj ⟨𝟙_ _, hO⟩).obj,
          pf.inv = (a.homEquiv _ _)
            ((Functor.Monoidal.μIso (derivedPullback i) K.obj
              ((schemeDerivedDirectImage i).obj (c.obj ⟨𝟙_ _, hO⟩).obj)).inv ≫
              (derivedPullback i).obj K.obj ◁ a.counit.app (c.obj ⟨𝟙_ _, hO⟩).obj) ∧
          IsIso ((adj.homEquiv
            ⟨((derivedPullback i).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj,
              hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩ K)
            (ObjectProperty.homMk (pf.hom ≫
              K.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom)))
  have hcriterion (K : schemeDerivedQCohCategory Y) : P K ↔ IsIso (τ.app K) := by
    obtain ⟨pf, hpin, heq⟩ := hτ K
    constructor
    · rintro ⟨pf', hpin', h⟩
      have hpf : pf' = pf := Iso.ext_inv (hpin'.trans hpin.symm)
      subst pf'
      rwa [heq]
    · intro h
      exact ⟨pf, hpin, heq ▸ h⟩
  obtain ⟨sF, sc, hFexact, hcexact⟩ :=
    rightAdjointTensor_exactStructures i hRf hO hTensor a c adj
  let := sF
  let := sc
  let : F.IsTriangulated := hFexact
  let : c.IsTriangulated := hcexact
  have hFsums (J : Type u) : PreservesColimitsOfShape (Discrete J) F := by
    let : PreservesColimitsOfShape (Discrete J)
        (tensorRight (c.obj ⟨𝟙_ _, hO⟩).obj) :=
      derivedTensorRight_preservesCoproducts Z (c.obj ⟨𝟙_ _, hO⟩).obj J
    let : PreservesColimitsOfShape (Discrete J) (derivedPullback i) :=
      a.leftAdjoint_preservesColimits.preservesColimitsOfShape
    let : HasCoproducts.{u} (schemeDerivedCategory Y) := derivedAmbientHasCoproducts Y
    let : (schemeDerivedQCohProperty Y).IsClosedUnderColimitsOfShape (Discrete J) :=
      schemeDerivedQCohClosedUnderCoproducts Y J
    have : PreservesColimitsOfShape (Discrete J)
        (F ⋙ (schemeDerivedQCohProperty Z).ι) := by
      change PreservesColimitsOfShape (Discrete J)
        ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback i ⋙
          tensorRight (c.obj ⟨𝟙_ _, hO⟩).obj)
      infer_instance
    exact preservesColimitsOfShape_of_reflects_of_preserves F (schemeDerivedQCohProperty Z).ι
  have hperfectShift (E : schemeDerivedQCohCategory Y)
      (hE : Scheme.perfectSubcategory Y E.obj) : isoOnAllShifts F c τ E := by
    intro n
    apply (hcriterion (E⟦n⟧)).mp
    exact hcase mon a c adj (E⟦n⟧) (perfect_iso Y
      (((schemeDerivedQCohProperty Y).ι.commShiftIso n).app E).symm
      (perfect_shift Y hE n))
  have hle := perfectClosure_le_isoOnAllShifts Y F c τ hFsums hsums hperfectShift
  rw [derivedQCohPerfectGeneration Y] at hle
  have hK : isoOnAllShifts F c τ K := hle K trivial
  apply (hcriterion K).mpr
  exact (NatTrans.isIso_app_iff_of_iso τ ((shiftFunctorZero _ ℤ).app K)).mp (hK 0)

end AlgebraicGeometry
