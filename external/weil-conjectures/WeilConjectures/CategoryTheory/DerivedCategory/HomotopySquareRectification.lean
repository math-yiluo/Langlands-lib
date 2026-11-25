/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Cylinder rectification retaining a specified cone map -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex
namespace CochainComplex

noncomputable section
variable {E : Type u} [Category E] [Abelian E]
variable {C D C' D' : CochainComplex E ℤ}

private abbrev rectT (_t : C ⟶ D) := D ⊞ mappingCone (𝟙 C)
private def rectI (t : C ⟶ D) : C ⟶ rectT t :=
  biprod.lift t (mappingCone.inr (𝟙 C))
private def rectK (t : C ⟶ D) (t' : C' ⟶ D') (α : C ⟶ C') (β : D ⟶ D')
    (H : Homotopy (t ≫ β) (α ≫ t')) : mappingCone (𝟙 C) ⟶ D' :=
  mappingCone.desc (𝟙 C) (-Cochain.ofHomotopy H) (α ≫ t' - t ≫ β) (by simp)
private def rectB (t : C ⟶ D) (t' : C' ⟶ D') (α : C ⟶ C') (β : D ⟶ D')
    (H : Homotopy (t ≫ β) (α ≫ t')) : rectT t ⟶ D' :=
  biprod.desc β (rectK t t' α β H)
private lemma rect_comm (t : C ⟶ D) (t' : C' ⟶ D') (α : C ⟶ C') (β : D ⟶ D')
    (H : Homotopy (t ≫ β) (α ≫ t')) : rectI t ≫ rectB t t' α β H = α ≫ t' := by
  simp [rectI, rectB, rectK]

variable [HasDerivedCategory.{w} E]
private lemma rect_coneId_zero (f : mappingCone (𝟙 C) ⟶ D) :
    DerivedCategory.Q.map f = 0 := by
  have hz := DerivedCategory.Q_map_eq_of_homotopy E (mappingCone.homotopyToZeroOfId C)
  have h := congrArg (fun k ↦ k ≫ DerivedCategory.Q.map f) hz
  simpa using h
private def rectIso (t : C ⟶ D) :
    DerivedCategory.Q.obj (rectT t) ≅ DerivedCategory.Q.obj D where
  hom := DerivedCategory.Q.map biprod.fst
  inv := DerivedCategory.Q.map biprod.inl
  hom_inv_id := by
    have hz := rect_coneId_zero (biprod.inr : mappingCone (𝟙 C) ⟶ rectT t)
    have h := congrArg (fun k ↦ DerivedCategory.Q.map k)
      (biprod.total (X := D) (Y := mappingCone (𝟙 C)))
    simp only [Functor.map_add, Functor.map_comp, CategoryTheory.Functor.map_id, hz,
      comp_zero, add_zero] at h
    exact h
  inv_hom_id := by rw [← Functor.map_comp, biprod.inl_fst, CategoryTheory.Functor.map_id]
private lemma rectB_eq (t : C ⟶ D) (t' : C' ⟶ D') (α : C ⟶ C') (β : D ⟶ D')
    (H : Homotopy (t ≫ β) (α ≫ t')) :
    DerivedCategory.Q.map (rectB t t' α β H) =
      (rectIso t).hom ≫ DerivedCategory.Q.map β := by
  have hz := rect_coneId_zero (rectK t t' α β H)
  simp only [rectB, biprod.desc_eq, Functor.map_add, Functor.map_comp, hz,
    comp_zero, add_zero, rectIso]


private def rectQ (t : C ⟶ D) : mappingCone (rectI t) ⟶ mappingCone t :=
  mappingCone.map (rectI t) t (𝟙 C) biprod.fst (by simp [rectI])

private lemma rectQ_isIso (t : C ⟶ D) : IsIso (DerivedCategory.Q.map (rectQ t)) := by
  let m := DerivedCategory.Q.mapTriangle.map
    (mappingCone.triangleMap (rectI t) t (𝟙 C) biprod.fst (by simp [rectI]))
  have h₁ : IsIso m.hom₁ := by
    change IsIso (DerivedCategory.Q.map (𝟙 C))
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  have h₂ : IsIso m.hom₂ := by
    change IsIso (rectIso t).hom
    infer_instance
  exact CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂ m
    (DerivedCategory.mappingCone_triangle_distinguished (rectI t))
    (DerivedCategory.mappingCone_triangle_distinguished t) h₁ h₂

omit [HasDerivedCategory.{w} E] in
private lemma rect_cone_homotopy (t : C ⟶ D) (t' : C' ⟶ D')
    (α : C ⟶ C') (β : D ⟶ D') (H : Homotopy (t ≫ β) (α ≫ t')) :
    Nonempty (Homotopy
      (mappingCone.map (rectI t) t' α (rectB t t' α β H) (rect_comm t t' α β H))
      (rectQ t ≫ mappingCone.mapOfHomotopy H)) := by
  let z : Cochain (rectT t) (mappingCone t') (-1) :=
    (Cochain.ofHom (biprod.snd : rectT t ⟶ mappingCone (𝟙 C))).comp
      ((mappingCone.descCochain (𝟙 C) (0 : Cochain C D' (-2))
        (-Cochain.ofHomotopy H) (by omega)).comp
          (Cochain.ofHom (mappingCone.inr t')) (add_zero _)) (zero_add _)
  refine ⟨mappingCone.descHomotopy (rectI t) _ _ 0 z ?_ ?_⟩
  · ext p q hpq
    simp [z, rectQ, mappingCone.map, mappingCone.mapOfHomotopy,
      rectI, Cochain.equivHomotopy]
  · dsimp only [z]
    simp only [δ_zero_cochain_comp _ _ _ (neg_add_cancel 1),
      δ_comp_zero_cochain _ _ _ (neg_add_cancel 1),
      δ_ofHom, Cochain.zero_comp, Cochain.comp_zero, zero_add,
      mappingCone.δ_descCochain _ _ _ _ 0 (neg_add_cancel 1), δ_zero,
      δ_ofHomotopy, δ_neg]
    ext p
    · simp only [mappingCone.map, Int.reduceNeg, rectB, rectK, mappingCone.inr_desc,
        Cochain.ofHom_comp, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
        HomologicalComplex.biprod_inl_desc_f_assoc, Int.negOnePow_zero, Cochain.comp_neg,
        Cochain.id_comp, smul_neg, one_smul, neg_sub, Cochain.comp_sub, Cochain.add_comp,
        Cochain.neg_comp, Cochain.comp_assoc_of_third_is_zero_cochain, Cochain.sub_comp,
        Cochain.comp_add, Int.negOnePow_neg,
        Int.negOnePow_one, smul_zero, add_zero, rectQ, mappingCone.mapOfHomotopy,
        Cochain.equivHomotopy, Equiv.coe_fn_mk, mappingCone.inr_desc_assoc, Category.assoc,
        Cochain.add_v, Cochain.neg_v, Cochain.sub_v, Preadditive.comp_add, Preadditive.comp_neg,
        HomologicalComplex.biprod_inl_snd_f_assoc, zero_comp, neg_zero, Preadditive.comp_sub,
        sub_self, HomologicalComplex.biprod_inl_fst_f_assoc, zero_add]
    · simp only [mappingCone.map, Int.reduceNeg, rectB, rectK, mappingCone.inr_desc,
        Cochain.ofHom_comp, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
        HomologicalComplex.biprod_inr_desc_f_assoc, Int.negOnePow_zero, Cochain.comp_neg,
        Cochain.id_comp, smul_neg, one_smul, neg_sub, Cochain.comp_sub, Cochain.add_comp,
        Cochain.neg_comp, Cochain.comp_assoc_of_third_is_zero_cochain, Cochain.sub_comp,
        Cochain.comp_add, Int.negOnePow_neg,
        Int.negOnePow_one, smul_zero, add_zero, rectQ, mappingCone.mapOfHomotopy,
        Cochain.equivHomotopy, Equiv.coe_fn_mk, mappingCone.inr_desc_assoc, Category.assoc,
        Cochain.add_v, Cochain.neg_v, Cochain.sub_v, Preadditive.comp_add, Preadditive.comp_neg,
        HomologicalComplex.biprod_inr_snd_f_assoc, Preadditive.comp_sub,
        HomologicalComplex.biprod_inr_fst_f_assoc, zero_comp]
      rw [mappingCone.desc_f _ _ _ _ p (p + 1) rfl]
      simp only [Preadditive.add_comp, Preadditive.sub_comp, Preadditive.neg_comp,
        Preadditive.comp_sub, Preadditive.comp_neg,
        Cochain.neg_v, HomologicalComplex.sub_f_apply, HomologicalComplex.comp_f,
        Cochain.comp_v (mappingCone.fst (𝟙 C)).1
          ((Cochain.ofHomotopy H).comp (Cochain.ofHom (mappingCone.inr t')) (add_zero _))
          (show (1 : ℤ) + -1 = 0 by omega) p (p + 1) p rfl (by omega),
        Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Category.assoc]


/-- Rectification changes only the source middle term and preserves the cone
map induced by the specified homotopy, after localization.
Source: Stacks Project, Tags 013N and 013O, with the cone formulas of Tag 014P.
(blueprint: lem-pc-homotopy-square-cone-rectification).

Proof: Write T = D biproduct Cone(id C), i = (t,inr(id C)) and p = fst.
For H : t beta homotopic to alpha t', write h for its degree-minus-one cochain,
so delta h = t beta - alpha t'. The map k : Cone(id C) -> D' with components
(-h, alpha t' - t beta) is a chain map by this equation. Put b = (beta,k).
Then i b = alpha t' strictly. Cone(id C) is contractible, so Q(p) is an
isomorphism and Q(b) = Q(p) Q(beta). The square (id C,p) from i to t is
strict and induces q : Cone(i) -> Cone(t); q is a quasi-isomorphism by the
cone triangle since id C and p are quasi-isomorphisms. Expanding the cone
maps, Cone.map(i,t',alpha,b) and q Cone.mapOfHomotopy(H) differ by the
boundary of the cochain whose only nonzero component is -h on the extra
contractible summand. Thus they are homotopic and their Q images agree.
Take eD = Q(p) and eCone = Q(q), using their isomorphism structures. This
also covers zero complexes and H = 0; it uses no geometric hypotheses. -/
theorem homotopy_square_cone_rectification
    {E : Type u} [Category E] [Abelian E] [HasDerivedCategory.{w} E]
    {C D C' D' : CochainComplex E ℤ}
    (t : C ⟶ D) (t' : C' ⟶ D') (α : C ⟶ C') (β : D ⟶ D')
    (H : Homotopy (t ≫ β) (α ≫ t')) :
    ∃ (T : CochainComplex E ℤ) (i : C ⟶ T) (b : T ⟶ D')
      (hc : i ≫ b = α ≫ t')
      (eD : DerivedCategory.Q.obj T ≅ DerivedCategory.Q.obj D)
      (eCone : DerivedCategory.Q.obj (mappingCone i) ≅
        DerivedCategory.Q.obj (mappingCone t)),
      DerivedCategory.Q.map b = eD.hom ≫ DerivedCategory.Q.map β ∧
      DerivedCategory.Q.map (mappingCone.map i t' α b hc) =
        eCone.hom ≫ DerivedCategory.Q.map (mappingCone.mapOfHomotopy H) := by
  have := rectQ_isIso t
  obtain ⟨h⟩ := rect_cone_homotopy t t' α β H
  refine ⟨rectT t, rectI t, rectB t t' α β H, rect_comm t t' α β H,
    rectIso t, asIso (DerivedCategory.Q.map (rectQ t)), rectB_eq t t' α β H, ?_⟩
  simpa only [Functor.map_comp, asIso_hom] using
    DerivedCategory.Q_map_eq_of_homotopy E h

end
end CochainComplex
