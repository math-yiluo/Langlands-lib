/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.BoundedKunnethSpectralSequence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # The canonical tensor model on a K-flat left representative
Source: Stacks Project, Tags 064L and 06Y0.
(blueprint: lem-pur-kunneth-flat-model)
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory
variable (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- The lax tensor comparison is invertible on a K-flat left representative.
Source: Stacks Project, Tags 064L and 06Y0. (blueprint: lem-pur-kunneth-flat-model)
Proof: on the homotopy category this is the fixed-left K-flat comparison counit. The
comparison for Q is transported through quotientCompQhIso; the quotient is strong monoidal.
Thus it is a composite of invertible maps. -/
theorem laxDerivedTensorMap_isIso_of_kFlat
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P) :
    IsIso (laxDerivedTensorMap.{u, w} R P Q) := by
  let π := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
  have hP' : (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat (π.obj P) :=
    (HomotopyCategory.kFlat_quotient_obj_iff _).2 hP
  have := DerivedCategory.isIso_tensorLeftCounit (π.obj P) hP'
  have : IsIso (Functor.LaxMonoidal.μ
      (DerivedCategory.Qh (C := ModuleCat.{u} R)) (π.obj P) (π.obj Q)) :=
    inferInstanceAs (IsIso ((DerivedCategory.tensorLeftCounit (π.obj P)).app (π.obj Q)))
  unfold laxDerivedTensorMap
  change IsIso (((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.app P ⊗ₘ
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.app Q) ≫
    (Functor.LaxMonoidal.μ DerivedCategory.Qh (π.obj P) (π.obj Q) ≫
      DerivedCategory.Qh.map (Functor.LaxMonoidal.μ π P Q)) ≫
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app (P ⊗ Q))
  infer_instance

/-- Every derived module complex admits a K-flat representative.
Source: Stacks Project, Tag 06Y0. (blueprint: lem-pur-kunneth-flat-model)
Proof: choose an ordinary representative using essential surjectivity of Q, take its
K-flat resolution, and invert the resulting quasi-isomorphism in the derived category. -/
theorem exists_kFlat_model (K : DerivedCategory.{w} (ModuleCat.{u} R)) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  let L := DerivedCategory.Q.objPreimage K
  obtain ⟨P, π, hπ, _, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat L
  have := hπ
  exact ⟨P, hP, ⟨asIso (DerivedCategory.Q.map π) ≪≫
    DerivedCategory.Q.objObjPreimageIso K⟩⟩

end CategoryTheory
