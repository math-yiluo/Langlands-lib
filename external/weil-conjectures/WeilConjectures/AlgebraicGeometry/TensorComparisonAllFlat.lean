/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory

/-! # Tensor comparison in a category whose objects are flat

This is the K-flat comparison step in the diagonal-summand argument for field coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- If every object is flat, the tensor localization comparison is invertible on all
cochain complexes, including unbounded complexes.
Source: the first paragraph of the finite-ring Kunneth proof, K-flat comparison step.

Proof. Each bounded-above good truncation of L is K-flat since all its terms are flat.
The filtered colimit of these truncations is L, and K-flat complexes are closed under
these colimits. Thus L is K-flat. The homotopy-to-derived tensor counit is invertible
when its right input is K-flat. The complex-to-homotopy tensor comparison is an identity,
so the composite lax structure on Q has invertible tensor comparison as well.
(blueprint: lem-pur-tensor-comparison-all-flat). -/
theorem tensorComparisonIsoOfAllFlat
    {C : Type (u + 2)} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
    [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C]
    [HasDerivedCategory.{u + 1} C]
    (hflat : ∀ X : C, ObjectProperty.flat X) (K L : CochainComplex C ℤ) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q K L) := by
  have hL : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat L := by
    apply ObjectProperty.prop_of_isColimit _ L.isColimitFiltrationLECocone
    intro n
    exact CochainComplex.kFlat_of_isStrictlyLE_of_flat (L.truncLE n) n
      (fun i ↦ hflat _)
  have hμ : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient C (.up ℤ)).obj K)
      ((HomotopyCategory.quotient C (.up ℤ)).obj L)) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_right DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (.up ℤ)) _ _
      ((HomotopyCategory.kFlat_quotient_obj_iff L).2 hL)
  have : IsIso (Functor.LaxMonoidal.μ (HomotopyCategory.quotient C (.up ℤ)) K L) := by
    change IsIso (𝟙 _)
    infer_instance
  change IsIso ((_ ⊗ₘ _) ≫
    (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map _) ≫ _)
  infer_instance

end AlgebraicGeometry.Etale
