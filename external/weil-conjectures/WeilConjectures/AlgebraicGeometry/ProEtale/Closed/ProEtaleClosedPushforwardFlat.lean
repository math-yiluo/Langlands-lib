/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-! # Flatness of closed direct images of pro-etale module sheaves -/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

open scoped CategoryTheory

private theorem flat_of_closed_open_restrictions
    (A : Type (u + 1)) [CommRing A] {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
    (hi : ObjectProperty.flat ((upperStar (ModuleCat.{u + 1} A) i).obj F))
    (hj : ObjectProperty.flat ((upperStar (ModuleCat.{u + 1} A) j).obj F)) :
    ObjectProperty.flat F := by
  let C := ModuleCat.{u + 1} A
  let P := pairFunctor (upperStar C i) (upperStar C j)
  have hP : JointlyReflectIsomorphisms P :=
    jointlyReflectIsomorphisms_pairFunctor _ _ (fun {_ _} f hi hj ↦ by
      have := hi
      have := hj
      exact isIso_of_isIso_upperStar_of_isCompl i j hij f)
  let (b : Bool) : Preadditive (cond b
      (Sheaf (Scheme.ProEt.topology Z) C) (Sheaf (Scheme.ProEt.topology U) C)) :=
    Abelian.toPreadditive
  let T' : ∀ b : Bool, cond b
      (Sheaf (Scheme.ProEt.topology Z) C) (Sheaf (Scheme.ProEt.topology U) C) ⥤
      cond b (Sheaf (Scheme.ProEt.topology Z) C) (Sheaf (Scheme.ProEt.topology U) C) :=
    Bool.rec (motive := fun b ↦ cond b
      (Sheaf (Scheme.ProEt.topology Z) C) (Sheaf (Scheme.ProEt.topology U) C) ⥤
      cond b (Sheaf (Scheme.ProEt.topology Z) C) (Sheaf (Scheme.ProEt.topology U) C))
      (by
        change Sheaf (Scheme.ProEt.topology U) C ⥤ Sheaf (Scheme.ProEt.topology U) C
        exact tensorLeft ((upperStar C j).obj F))
      (by
        change Sheaf (Scheme.ProEt.topology Z) C ⥤ Sheaf (Scheme.ProEt.topology Z) C
        exact tensorLeft ((upperStar C i).obj F))
  let (b : Bool) : (T' b).Additive := by
    cases b
    · change (tensorLeft ((upperStar C j).obj F)).Additive
      infer_instance
    · change (tensorLeft ((upperStar C i).obj F)).Additive
      infer_instance
  have hT' (b : Bool) : exactFunctor _ _ (T' b) := by
    cases b
    · change exactFunctor _ _ (tensorLeft ((upperStar C j).obj F))
      exact hj.tensorLeft
    · change exactFunctor _ _ (tensorLeft ((upperStar C i).obj F))
      exact hi.tensorLeft
  apply (ObjectProperty.flat_iff_preservesFiniteLimits F).2
  exact (@JointlyReflectIsomorphisms.exactFunctor_of_iso
    _ _ _ _ _ _ Bool
    (fun b ↦ cond b (Sheaf (Scheme.ProEt.topology Z) C)
      (Sheaf (Scheme.ProEt.topology U) C))
    (fun b ↦ inferInstance) (fun b ↦ inferInstance)
    (fun b ↦ cond b (Sheaf (Scheme.ProEt.topology Z) C)
      (Sheaf (Scheme.ProEt.topology U) C))
    (fun b ↦ inferInstance) (fun b ↦ inferInstance)
    P (fun b ↦ inferInstance) (fun b ↦ inferInstance)
    P (fun b ↦ inferInstance) (fun b ↦ inferInstance)
    hP (tensorLeft F) inferInstance T' (fun b ↦ by
      cases b
      · change (tensorLeft ((upperStar C j).obj F)).Additive
        infer_instance
      · change (tensorLeft ((upperStar C i).obj F)).Additive
        infer_instance)
    hT'
    (fun b ↦ by
      cases b
      · change tensorLeft F ⋙ upperStar C j ≅
          upperStar C j ⋙ tensorLeft ((upperStar C j).obj F)
        exact (Functor.Monoidal.commTensorLeft (upperStar C j) F).symm
      · change tensorLeft F ⋙ upperStar C i ≅
          upperStar C i ⋙ tensorLeft ((upperStar C i).obj F)
        exact (Functor.Monoidal.commTensorLeft (upperStar C i) F).symm)).1

/-- Closed direct image preserves flat module sheaves on a locally Noetherian scheme. -/
theorem lowerStar_preserves_flat_closed
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]
    (M : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))
    (hM : ObjectProperty.flat M) :
    ObjectProperty.flat ((lowerStar (ModuleCat.{u + 1} A) i).obj M) := by
  let C := ModuleCat.{u + 1} A
  let j := i.openComplement.ι
  have hij : IsCompl (Set.range i.base) (Set.range j.base) := by
    rw [show Set.range j.base = (Set.range i.base)ᶜ by
      simp [j, Scheme.Hom.coe_openComplement]]
    exact isCompl_compl
  apply flat_of_closed_open_restrictions A i j hij
  · exact ObjectProperty.prop_of_iso ObjectProperty.flat
      (asIso ((upperStarLowerStarAdjunction C i).counit.app M)).symm hM
  · exact ObjectProperty.flat_of_isZero
      (isZero_upperStar_lowerStar_of_disjoint C i j hij.disjoint M)

end AlgebraicGeometry.ProEtale
