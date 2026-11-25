/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Additive adjunctions transpose specified cone squares -/

@[expose] public section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex

/-- Transposing a homotopy square through an additive adjunction preserves its specified
cone map, using the canonical additive cone comparisons.
Source: Stacks Project, Derived Categories, Tag 014P (cone formulas), combined with
the termwise additive adjunction.
(blueprint: lem-pc-additive-adjunction-cone-square).

Proof: transpose the two chain maps using the termwise adjunction. Apply the left functor
to the given homotopy, then postcompose with the counit. Naturality of the counit
identifies its endpoints with the required composites. Its degree-minus-one component
is the transpose of the original degree-minus-one component. In each degree the cone
map has diagonal components given by the two chain maps and off-diagonal component
given by that homotopy. Additivity of the adjunction identifies all three components;
the canonical cone comparisons identify the two direct sums. Thus the displayed chain
maps agree, including the homotopy sign. This also applies to zero objects and homotopies. -/
theorem additiveAdjunction_cone_square
    {E : Type u} {E' : Type u'} [Category.{v} E] [Category.{v'} E']
    [Preadditive E] [Preadditive E'] [HasBinaryBiproducts E] [HasBinaryBiproducts E']
    {L : E ⥤ E'} {R : E' ⥤ E} [L.Additive] [R.Additive] (adj : L ⊣ R)
    {P Q : CochainComplex E ℤ} {A B : CochainComplex E' ℤ}
    (p : P ⟶ Q) (t : A ⟶ B)
    (α : P ⟶ (R.mapHomologicalComplex (.up ℤ)).obj A)
    (β : Q ⟶ (R.mapHomologicalComplex (.up ℤ)).obj B)
    (H : Homotopy (p ≫ β) (α ≫ (R.mapHomologicalComplex (.up ℤ)).map t)) :
    let ac := adj.mapHomologicalComplex (.up ℤ)
    let a := (ac.homEquiv _ _).symm α
    let b := (ac.homEquiv _ _).symm β
    ∃ H' : Homotopy ((L.mapHomologicalComplex (.up ℤ)).map p ≫ b) (a ≫ t),
      mappingCone.mapOfHomotopy H' =
        (mappingCone.mapHomologicalComplexIso p L).inv ≫
          (ac.homEquiv _ _).symm
            (mappingCone.mapOfHomotopy H ≫
              (mappingCone.mapHomologicalComplexIso t R).inv) := by
  dsimp only
  let ac := adj.mapHomologicalComplex (.up ℤ)
  let a := (ac.homEquiv _ _).symm α
  let b := (ac.homEquiv _ _).symm β
  let H' : Homotopy ((L.mapHomologicalComplex (.up ℤ)).map p ≫ b) (a ≫ t) :=
    (Homotopy.ofEq (ac.homEquiv_naturality_left_symm p β).symm).trans
      (((L.mapHomotopy H).compRight (ac.counit.app B)).trans
        (Homotopy.ofEq (by
          change (L.mapHomologicalComplex (.up ℤ)).map
            (α ≫ (R.mapHomologicalComplex (.up ℤ)).map t) ≫ ac.counit.app B = a ≫ t
          rw [Functor.map_comp, Category.assoc]
          erw [ac.counit.naturality t]
          simp only [a, Adjunction.homEquiv_counit, Category.assoc, Functor.id_map])))
  refine ⟨H', ?_⟩
  apply HomologicalComplex.Hom.ext
  funext n
  apply (mappingCone.ext_from_iff
    ((L.mapHomologicalComplex (.up ℤ)).map p) (n + 1) n rfl _ _).2
  constructor
  · simp only [Int.reduceNeg, mappingCone.mapOfHomotopy, Adjunction.mapHomologicalComplex,
      Functor.id_obj, Functor.comp_obj, Adjunction.homEquiv_counit,
      HomComplex.Cochain.ofHom_comp, HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain,
      HomComplex.Cochain.equivHomotopy, HomComplex.Cochain.ofHomotopy, Homotopy.trans,
      Homotopy.ofEq, Homotopy.compRight, Functor.mapHomotopy, add_zero, zero_add,
      Equiv.coe_fn_mk, Category.assoc, mappingCone.inl_v_desc_f, HomComplex.Cochain.add_v,
      HomComplex.Cochain.zero_cochain_comp_v, HomComplex.Cochain.ofHom_v,
      Functor.mapHomologicalComplex_map_f, HomComplex.Cochain.comp_zero_cochain_v,
      HomComplex.Cochain.mk_v, mappingCone.mapHomologicalComplexIso, Functor.map_comp,
      HomologicalComplex.comp_f, HomologicalComplex.Hom.isoOfComponents_inv_f,
      mappingCone.mapHomologicalComplexXIso, mappingCone.mapHomologicalComplexXIso',
      Functor.map_add, Preadditive.add_comp, Adjunction.counit_naturality,
      Preadditive.comp_add, mappingCone.inl_v_fst_v_assoc,
      mappingCone.inl_v_snd_v_assoc, zero_comp, H', ac, a]
    simp only [← L.map_comp_assoc, mappingCone.inl_v_desc_f_assoc,
      HomComplex.Cochain.add_v, HomComplex.Cochain.zero_cochain_comp_v,
      HomComplex.Cochain.ofHom_v, HomComplex.Cochain.comp_zero_cochain_v,
      HomComplex.Cochain.mk_v, Preadditive.add_comp, Category.assoc,
      mappingCone.inl_v_fst_v, Category.comp_id, mappingCone.inr_f_fst_v,
      comp_zero, add_zero, mappingCone.inl_v_snd_v, mappingCone.inr_f_snd_v, zero_add]
  · simp only [mappingCone.mapOfHomotopy, Int.reduceNeg, Adjunction.mapHomologicalComplex,
      Functor.id_obj, Functor.comp_obj, Adjunction.homEquiv_counit,
      HomComplex.Cochain.ofHom_comp, HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain,
      HomComplex.Cochain.equivHomotopy_apply_coe, Category.assoc, mappingCone.inr_f_desc_f,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      mappingCone.mapHomologicalComplexIso, Functor.map_comp,
      HomologicalComplex.Hom.isoOfComponents_inv_f, mappingCone.mapHomologicalComplexXIso,
      mappingCone.mapHomologicalComplexXIso', Functor.map_add, Preadditive.add_comp,
      Adjunction.counit_naturality, Preadditive.comp_add, mappingCone.inr_f_fst_v_assoc,
      zero_comp, mappingCone.inr_f_snd_v_assoc, zero_add, ac, b]
    simp only [← L.map_comp_assoc, mappingCone.inr_f_desc_f_assoc,
      HomologicalComplex.comp_f, Category.assoc, mappingCone.inr_f_fst_v,
      comp_zero, L.map_zero, zero_comp, mappingCone.inr_f_snd_v, Category.comp_id, zero_add]

end CochainComplex
