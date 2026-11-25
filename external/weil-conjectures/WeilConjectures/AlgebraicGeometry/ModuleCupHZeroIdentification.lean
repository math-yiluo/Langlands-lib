/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Canonical H-zero identification for flat tensor models

Source: Stacks Project, Tag 06YH (derived tensor), using right exactness of tensor.
-/

@[expose] public section

universe v u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [MonoidalPreadditive C]

/-- Tensoring a nonpositive flat resolution preserves its degree-zero augmentation class.
Source: Stacks Project, Tag 06YH; right exactness of tensor.
(blueprint: lem-sc-module-cup-hzero-identification)
Proof: since P is zero in positive degrees, H-zero of its tensor with G is the
cokernel of P^{-1} tensor G to P^0 tensor G. The augmentation identifies the
cokernel of P^{-1} to P^0 with F. Tensoring with G preserves this cokernel,
because tensor is a left adjoint. Thus the augmentation induces an isomorphism
on H-zero. This is the model calculation only; the canonical derived-to-ordinary
comparison and its flat-model transport are stated separately in
ModuleCupCanonicalHZeroIdentification. No flatness of F or G is assumed. -/
theorem moduleCup_hzero_identification (F G : C) (P : CochainComplex C ℤ)
    (p : P ⟶ (CochainComplex.singleFunctor C 0).obj F)
    [P.IsStrictlyLE 0] [QuasiIso p]
    (_hflat : ∀ i : ℤ, ObjectProperty.flat (P.X i)) :
    IsIso (HomologicalComplex.homologyMap
      (((tensorRight G).mapHomologicalComplex (ComplexShape.up ℤ)).map p) 0) := by
  have : PreservesColimitsOfSize.{0, 0} (tensorRight G) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight G)
  have hP : (P.sc 0).g = 0 := by
    have hz : IsZero (P.sc 0).X₃ := by
      simpa [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor] using
        P.isZero_of_isStrictlyLE 0 1
    exact hz.eq_of_tgt _ _
  have hF : (((CochainComplex.singleFunctor C 0).obj F).sc 0).g = 0 := by
    have hz : IsZero (((CochainComplex.singleFunctor C 0).obj F).sc 0).X₃ := by
      simpa [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor] using
        ((CochainComplex.singleFunctor C 0).obj F).isZero_of_isStrictlyLE 0 1
    exact hz.eq_of_tgt _ _
  have := Functor.preservesRightHomology_of_zero_g (tensorRight G) (P.sc 0) hP
  have := Functor.preservesRightHomology_of_zero_g (tensorRight G)
    (((CochainComplex.singleFunctor C 0).obj F).sc 0) hF
  rw [← quasiIsoAt_iff_isIso_homologyMap,
    quasiIsoAt_iff]
  have : ShortComplex.QuasiIso
      ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) 0).map p) :=
    (quasiIsoAt_iff p 0).1 inferInstance
  exact ShortComplex.quasiIso_map_of_preservesRightHomology (tensorRight G)
    ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) 0).map p)

end DerivedCategory
