/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleRestrictedTotalResolution

/-! # Augmentation and inclusion of the restricted total

Source: Stacks Project, Tags 015J and 0133, restricted augmented total.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Totalization of the column inclusion before applying global sections.
Source: Stacks Project, Tag 015J, proof remark (3).
(blueprint: lem-weil-pbc-etale-restricted-augmentation-inclusion). -/
noncomputable def etaleRestrictedTotalInclusion
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q : ℤ) :=
  HomologicalComplex₂.total.map
    ((HomologicalComplex₂.flipFunctor
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
        ((CartanEilenbergPresentation.mappedFunctor
          (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))).map
            (T.I.ιStupidTrunc (ComplexShape.embeddingUpIntGE q)))) (ComplexShape.up ℤ)

set_option backward.isDefEq.respectTransparency false in
/-- The restricted augmentation commutes with the two truncation inclusions.
Source: Stacks Project, Tag 015J, proof remark (3), and Tag 0133.

Proof: Evaluate in total degree n and use the formula for a totalized map on
its degree-zero resolution summand. Naturality of extension by zero transports
that summand to the degree-zero summand of the full total. If n ≥ q, the
stupid-truncation projection followed by its inclusion is the identity on
T.I.X n. Cancel this pair in etaleRestrictedAugmentationComponent and apply
T.aug_formula. If n < q, the source term of the truncated K is zero, so the
two maps are equal. Chain-map extensionality now proves the equation. The
calculation has no positivity condition on q, and also covers the zero complex
and empty diagonals.
(blueprint: lem-weil-pbc-etale-restricted-augmentation-inclusion). -/
theorem etaleRestrictedAugmentation_inclusion
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q : ℤ) :
    etaleRestrictedAugmentation X K T q ≫ etaleRestrictedTotalInclusion X K T q =
      K.obj.ιStupidTrunc (ComplexShape.embeddingUpIntGE q) ≫ T.aug := by
  classical
  ext n : 1
  simp only [HomologicalComplex.comp_f]
  rw [T.aug_formula]
  dsimp only [etaleRestrictedAugmentation, etaleRestrictedAugmentationComponent,
    etaleRestrictedTotalInclusion]
  simp only [Category.assoc, HomologicalComplex₂.ιTotal_map]
  change _ ≫ (T.a.f n).f 0 ≫
    (T.I.πStupidTruncf (ComplexShape.embeddingUpIntGE q) n).f 0 ≫
    _ ≫ (HomologicalComplex.extendMap
      ((𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})).mapHomologicalComplex
        (ComplexShape.up ℕ) |>.map
          ((T.I.ιStupidTrunc (ComplexShape.embeddingUpIntGE q)).f n))
      ComplexShape.embeddingUpNat).f 0 ≫ _ = _
  rw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat
    (i := 0) (i' := 0) rfl]
  dsimp only [etaleRestrictedBicomplex]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  by_cases hn : q ≤ n
  · obtain ⟨i, hi⟩ : ∃ i : ℕ, (ComplexShape.embeddingUpIntGE q).f i = n := by
      refine ⟨(n - q).toNat, ?_⟩
      change q + ((n - q).toNat : ℤ) = n
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    subst n
    simp only [HomologicalComplex.ιStupidTrunc, HomologicalComplex.ιStupidTruncf_eq,
      HomologicalComplex.πStupidTruncf_eq]
    change _ ≫ (T.a.f ((ComplexShape.embeddingUpIntGE q).f i)).f 0 ≫
      (((T.I.restriction (ComplexShape.embeddingUpIntGE q)).extendXIso
        (ComplexShape.embeddingUpIntGE q) rfl).inv).f 0 ≫
      (((T.I.restriction (ComplexShape.embeddingUpIntGE q)).extendXIso
        (ComplexShape.embeddingUpIntGE q) rfl).hom).f 0 ≫ _ = _
    rw [← Category.assoc
      (((T.I.restriction (ComplexShape.embeddingUpIntGE q)).extendXIso
        (ComplexShape.embeddingUpIntGE q) rfl).inv.f 0),
      ← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f,
      Category.id_comp]
    rfl
  · exact (K.obj.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE q) n
      (fun i hi ↦ by change q + (i : ℤ) = n at hi; omega)).eq_of_src _ _

end AlgebraicGeometry.Etale
