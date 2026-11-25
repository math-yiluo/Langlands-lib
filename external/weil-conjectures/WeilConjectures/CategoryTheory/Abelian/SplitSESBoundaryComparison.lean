/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-!
# Comparing the cone and split-row boundaries

Source: Stacks Project, Derived Categories, Tag 0152.
(blueprint: lem-sc-p1-split-ses-boundary-comparison).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical cone boundary is the image of the split-row boundary.
Source: Stacks Project, Derived Categories, Tag 0152, the formula for the canonical
boundary through the cone quasi-isomorphism.
(blueprint: lem-sc-p1-split-ses-boundary-comparison).

Proof: Let q : Cone(S.f) -> S.X₃ be the cone comparison. Its components are the
projection onto S.X₂ followed by S.g. In the chosen splitting write S.X₂ⁿ as
S.X₁ⁿ ⊞ S.X₃ⁿ. The differential has diagonal entries d₁,d₃ and upper-right entry
sⁿ d₂ rⁿ⁺¹. Multiplying q by this entry gives the split boundary. Subtracting the
third cone map, which is minus the first projection, gives a null-homotopic map;
the homotopy in degree k is Hᵏ = proj₂ ≫ rᵏ, landing in S.X₁[1]ᵏ⁻¹.
Indeed d_Cone ≫ H + H ≫ d_{X₁[1]} = proj₁ + proj₂ ≫ g ≫ s ≫ d₂ ≫ r,
which is q followed by the split boundary minus the third cone map. Here the
shifted differential is -d₁. Expand r f + g s = id, f r = id and f d₂ = d₁ f.
Apply Q, which identifies homotopic maps, and cancel Q(q), a quasi-isomorphism.
The commutation of Q with shift gives exactly the displayed formula. This works
for every degreewise splitting, including the zero row, and does not require a
splitting by chain maps. -/
theorem triangleOfSESδ_eq_degreewiseSplit
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
    (σ : ∀ k : ℤ,
      (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) k)).Splitting) :
    triangleOfSESδ hS =
      ShiftedHom.map (CochainComplex.homOfDegreewiseSplit S σ) Q := by
  -- The retractions give the degree -1 part of the cone homotopy.
  let γ : CochainComplex.HomComplex.Cochain S.X₂ (S.X₁⟦(1 : ℤ)⟧) (-1) :=
    CochainComplex.HomComplex.Cochain.mk (fun p q hpq ↦
      (σ p).r ≫ (S.X₁.XIsoOfEq (by omega : p = q + 1)).hom)
  have h : Homotopy
      (CochainComplex.mappingCone.descShortComplex S ≫ CochainComplex.homOfDegreewiseSplit S σ)
      (CochainComplex.mappingCone.triangle S.f).mor₃ := by
    refine CochainComplex.mappingCone.descHomotopy S.f _ _ 0 γ ?_ ?_
    · -- On the first cone summand, the retraction cancels the negative projection.
      ext p q hpq
      rw [CochainComplex.HomComplex.Cochain.comp_v _ _ (add_zero (-1)) p q q hpq (add_zero q),
        CochainComplex.HomComplex.Cochain.add_v, CochainComplex.HomComplex.Cochain.add_v,
        CochainComplex.HomComplex.δ_zero, CochainComplex.HomComplex.Cochain.zero_v,
        CochainComplex.HomComplex.Cochain.comp_v _ _ (zero_add (-1)) p p q (add_zero p) hpq,
        CochainComplex.HomComplex.Cochain.comp_v _ _ (add_zero (-1)) p q q hpq (add_zero q)]
      simp only [CochainComplex.HomComplex.Cochain.ofHom_v, HomologicalComplex.comp_f,
        CochainComplex.mappingCone.inl_v_descShortComplex_f_assoc, zero_comp, zero_add,
        CochainComplex.mappingCone.inl_v_triangle_mor₃_f]
      have hf := (σ p).f_r
      dsimp at hf
      dsimp [γ, CochainComplex.shiftFunctorObjXIso]
      rw [← Category.assoc, hf, Category.id_comp]
      simp [HomologicalComplex.XIsoOfEq]
    · -- On the second summand, expand g s = id - r f and use the chain-map identity.
      ext p
      simp only [CochainComplex.HomComplex.Cochain.ofHom_v, HomologicalComplex.comp_f,
        CochainComplex.mappingCone.inr_f_descShortComplex_f_assoc,
        CochainComplex.homOfDegreewiseSplit_f,
        CochainComplex.cocycleOfDegreewiseSplit, CochainComplex.HomComplex.Cocycle.mk_coe,
        CochainComplex.HomComplex.Cochain.mk_v,
        CochainComplex.HomComplex.Cochain.add_v, CochainComplex.mappingCone.inr_f_triangle_mor₃_f]
      rw [CochainComplex.HomComplex.δ_v (-1) 0 (by omega) γ p p (by omega) (p - 1) (p + 1) rfl rfl]
      dsimp [γ]
      simp only [Units.neg_smul, one_smul, Preadditive.comp_neg, Category.assoc, Category.comp_id,
        add_zero, HomologicalComplex.XIsoOfEq_hom_comp_d]
      have hg := (σ p).g_s
      have hf := (σ (p + 1)).f_r
      dsimp at hg hf
      rw [← Category.assoc, hg]
      simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc, S.f.comm_assoc,
        hf, Category.comp_id]
      abel
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  apply (cancel_epi (Q.map (CochainComplex.mappingCone.descShortComplex S))).mp
  rw [descShortComplex_triangleOfSESδ]
  dsimp [ShiftedHom.map]
  rw [← Category.assoc, ← Q.map_comp, DerivedCategory.Q_map_eq_of_homotopy C h]

end DerivedCategory
