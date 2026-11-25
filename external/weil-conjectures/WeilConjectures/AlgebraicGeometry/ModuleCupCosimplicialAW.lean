/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementCosimplicialInput
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

import WeilConjectures.AlgebraicGeometry.ModuleCupAWLeibniz

/-! # Alexander--Whitney map for cosimplicial module sheaves -/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial

namespace AlgebraicGeometry.Scheme.Modules


private theorem tensor_summand_d (X : Scheme.{u}) [MonoidalPreadditive X.Modules]
    (P K : CochainComplex X.Modules ℤ) (p q r r' : ℤ)
    (h : p + q = r) (h' : r + 1 = r') :
    HomologicalComplex.ιTensorObj P K p q r h ≫
        (HomologicalComplex.tensorObj P K).d r r' =
      P.d p (p + 1) ▷ K.X q ≫
          HomologicalComplex.ιTensorObj P K (p + 1) q r' (by omega) +
        p.negOnePow • (P.X p ◁ K.d q (q + 1) ≫
          HomologicalComplex.ιTensorObj P K p (q + 1) r' (by omega)) := by
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (rfl : (ComplexShape.up ℤ).Rel p (p + 1)) _ _ (show p + 1 + q = r' by omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _
      (rfl : (ComplexShape.up ℤ).Rel q (q + 1)) _ (show p + (q + 1) = r' by omega)]
  simp

/-- A pointwise cosimplicial multiplication induces a tensor cochain map.
Source: Banerjee, Tensor Structure on Smooth Motives, arXiv:1004.1491,
§1.1.4, p. 16, Alexander--Whitney front/back formula and (1.1.2).
The same formula applies to the sheaf tensor product since tensoring is additive
and the simplex identities are identities of sheaf morphisms.
(blueprint: lem-sc-module-cup-cosimplicial-aw)
Proof: on the summand in bidegree (r,s), r,s nonnegative, apply to the first
factor the cofaces associated with the inclusion [r] → [r+s] of the first
r+1 vertices, and to the second factor those associated with the inclusion
[s] → [r+s] of the last s+1 vertices. Tensor these two maps and follow by
μ in degree r+s. The other summands have a zero factor. The coproduct universal
property assembles these maps into the components of the total-complex map.
Expand the alternating coface differential. Naturality of μ moves each coface
past μ; the front/back inclusion identities cancel all interior terms and
leave exactly the left differential and (-1)^r times the right differential.
This is the cochain-map identity. In bidegree (0,0) both inclusions are identities,
so the resulting map is precisely μ in degree zero, conjugated by the extension
identifications. No exactness, flasqueness, or augmentations are used. -/
theorem moduleCup_cosimplicial_aw (X : Scheme.{u}) [MonoidalPreadditive X.Modules]
    (A B C : CosimplicialObject X.Modules) (μ : moduleCup_cosimplicialTensor X A B ⟶ C) :
    ∃ t : HomologicalComplex.tensorObj (moduleCup_cosimplicialComplex X A)
        (moduleCup_cosimplicialComplex X B) ⟶ moduleCup_cosimplicialComplex X C,
      HomologicalComplex.ιTensorObj (moduleCup_cosimplicialComplex X A)
        (moduleCup_cosimplicialComplex X B) 0 0 0 (by simp) ≫ t.f 0 =
        moduleCup_cosimplicialZeroPair X A B C μ := by
  let t : HomologicalComplex.tensorObj (moduleCup_cosimplicialComplex X A)
      (moduleCup_cosimplicialComplex X B) ⟶ moduleCup_cosimplicialComplex X C :=
    CochainComplex.ofHom (moduleCup_awComponent X A B C μ) (by
      intro n
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro r s h
      have h' : r + s = n := h
      by_cases hr : 0 ≤ r
      · by_cases hs : 0 ≤ s
        · rw [moduleCup_ι_awComponent_assoc, ← Category.assoc]
          erw [tensor_summand_d X _ _ r s n (n + 1) h' rfl]
          rw [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc,
            Category.assoc]
          rw [moduleCup_ι_awComponent, moduleCup_ι_awComponent]
          exact moduleCup_awSummand_leibniz X A B C μ r s n h' hr hs
        · have hz : IsZero ((moduleCup_cosimplicialComplex X B).X s) := by
            apply HomologicalComplex.isZero_extend_X
            intro i hi
            change (i : ℤ) = s at hi
            omega
          exact (((curriedTensor X.Modules).obj _).map_isZero hz).eq_of_src _ _
      · have hz : IsZero ((moduleCup_cosimplicialComplex X A).X r) := by
          apply HomologicalComplex.isZero_extend_X
          intro i hi
          change (i : ℤ) = r at hi
          omega
        exact (((curriedTensor X.Modules).map_isZero hz).obj _).eq_of_src _ _)
  refine ⟨t, ?_⟩
  exact (moduleCup_ι_awComponent X A B C μ 0 0 0 (by simp)).trans
    (moduleCup_awSummand_zero X A B C μ)

end AlgebraicGeometry.Scheme.Modules
