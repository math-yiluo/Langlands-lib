/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
import WeilConjectures.AlgebraicGeometry.EtaleSingleCochainMonoidal
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor

/-! # The specified degree-zero lax tensorator

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, exact single realization of exterior products
(blueprint: lem-pur-coordinate-single-tensor-lax).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity

/-- The specified degree-zero tensor comparison is the tensorator of a lax structure.
Source: degree-zero realization in the affine-space exterior-product argument.
(blueprint: lem-pur-coordinate-single-tensor-lax).

Proof: use the proved canonical monoidal structure on single cochain complexes,
compose with the localization functor, and transport the resulting lax structure
along singleFunctorIsoCompQ. The transported tensorator is, term for term, the
specified cupSingleTensorMap: the two single/quotient comparisons, localization
tensorator, ordinary single-complex tensor comparison, and inverse comparison. -/
theorem coordinate_single_tensor_lax
    {C : Type*} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [HasDerivedCategory.{u + 1} C]
    [Abelian.HasFunctorialFlatResolution C] :
    ∃ m : (DerivedCategory.singleFunctor C 0).LaxMonoidal,
      ∀ L M : C, letI := m
        Functor.LaxMonoidal.μ (DerivedCategory.singleFunctor C 0) L M =
          cupSingleTensorMap L M := by
  obtain ⟨ms, hms⟩ := Etale.exists_singleCochainMonoidal (C := C)
  let := ms
  let : (CochainComplex.singleFunctor C 0).Monoidal := ms
  let e := DerivedCategory.singleFunctorIsoCompQ C 0
  let m := Functor.LaxMonoidal.transport e.symm
  refine ⟨m, ?_⟩
  intro L M
  rw [Functor.LaxMonoidal.transport_μ e.symm]
  simp only [Functor.LaxMonoidal.comp_μ]
  have hμ : Functor.LaxMonoidal.μ (CochainComplex.singleFunctor C 0) L M =
      (Etale.singleCochainTensorIso L M).hom := hms L M
  rw [hμ]
  simp only [cupSingleTensorMap, Etale.singleCochainTensorIso, Iso.symm_inv,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv, Iso.trans_hom,
    Category.assoc, tensorIso_hom, e]
  rfl

end AlgebraicGeometry.ProEtale.AffineZeroPurity
