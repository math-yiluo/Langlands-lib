/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # The normalized degree-zero cohomology identification

Source: Stacks Project, Derived Categories, Tags 08J5 and 05RU.
(blueprint: lem-amb-derived-degree-zero-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe w v u
open CategoryTheory CategoryTheory.Limits
namespace DerivedCategory

private theorem homology_map_injective_single
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {M N : C} {f g : (singleFunctor C 0).obj M ⟶ (singleFunctor C 0).obj N}
    (h : (homologyFunctor C 0).map f = (homologyFunctor C 0).map g) : f = g := by
  obtain ⟨a, rfl⟩ := (singleFunctor C 0).map_surjective f
  obtain ⟨b, rfl⟩ := (singleFunctor C 0).map_surjective g
  have : (singleFunctor C 0 ⋙ homologyFunctor C 0).Faithful :=
    Functor.Faithful.of_iso (singleFunctorCompHomologyFunctorIso C 0).symm
  exact congrArg ((singleFunctor C 0).map)
    ((singleFunctor C 0 ⋙ homologyFunctor C 0).map_injective h)

/-- Cohomology in degree zero gives the unique normalized identification of a complex
concentrated in degree zero with its cohomology object placed in degree zero.
Source: Stacks Project, Tags 08J5 and 05RU.
(blueprint: lem-amb-derived-degree-zero-normalization).

Proof: vanishing gives the two halves of the standard t-structure. Its heart is the
image of the fully faithful single-degree embedding. Choose an identification with a
single object Y and compose it with the single-degree image of the inverse of the
induced isomorphism H^0(X) → Y. Naturality of the single-cohomology comparison makes
the result induce the identity. For uniqueness, compose two candidates with a fixed
inverse and use full faithfulness of the single-degree embedding. -/
theorem existsUnique_iso_single_homology_zero
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X : DerivedCategory C)
    (hX : ∀ q : ℤ, q ≠ 0 → IsZero ((homologyFunctor C q).obj X)) :
    ∃! e : X ≅ (singleFunctor C 0).obj ((homologyFunctor C 0).obj X),
      (homologyFunctor C 0).map e.hom ≫
        (singleFunctorCompHomologyFunctorIso C 0).hom.app ((homologyFunctor C 0).obj X) =
      𝟙 ((homologyFunctor C 0).obj X) := by
  let : X.IsGE 0 := (isGE_iff X 0).2 (fun q hq ↦ hX q (ne_of_lt hq))
  let : X.IsLE 0 := (isLE_iff X 0).2 (fun q hq ↦ hX q (ne_of_gt hq))
  obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE X 0
  let ε := singleFunctorCompHomologyFunctorIso C 0
  let c := (homologyFunctor C 0).mapIso e ≪≫ ε.app Y
  let α := e ≪≫ (singleFunctor C 0).mapIso c.symm
  have hα : (homologyFunctor C 0).map α.hom ≫
      ε.hom.app ((homologyFunctor C 0).obj X) = 𝟙 _ := by
    have hn := ε.hom.naturality c.inv
    simp only [Functor.comp_map, Functor.id_map] at hn
    dsimp only [α, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [Functor.map_comp, Category.assoc, hn]
    simpa only [c, Iso.trans_hom, Functor.mapIso_hom, Category.assoc, Iso.app_hom,
      Functor.id_obj] using c.hom_inv_id
  refine ⟨α, hα, ?_⟩
  intro β hβ
  apply Iso.ext
  apply (cancel_epi α.inv).mp
  apply homology_map_injective_single
  rw [Functor.map_comp, Functor.map_comp]
  congr 1
  apply (cancel_mono (ε.hom.app ((homologyFunctor C 0).obj X))).mp
  exact hβ.trans hα.symm

/-- A uniquely characterized map from each normalized heart identification gives
one unique normalized pair. Source: the degree-zero gluing argument.
(blueprint: lem-amb-derived-degree-zero-normalization).

Proof: the preceding theorem fixes the identification. At that identification the
hypothesis fixes the sheaf map. Any other pair has the same first component by the
cohomology normalization and the same second component by its characterization. -/
theorem existsUnique_normalized_iso_and_map
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X : DerivedCategory C) (N : C)
    (hX : ∀ q : ℤ, q ≠ 0 → IsZero ((homologyFunctor C q).obj X))
    (P : (X ⟶ (singleFunctor C 0).obj N) → Prop)
    (hP : ∀ e : X ≅ (singleFunctor C 0).obj ((homologyFunctor C 0).obj X),
      ∃! f : (homologyFunctor C 0).obj X ⟶ N, P (e.hom ≫ (singleFunctor C 0).map f)) :
    ∃! p : (X ≅ (singleFunctor C 0).obj ((homologyFunctor C 0).obj X)) ×
        ((homologyFunctor C 0).obj X ⟶ N),
      (homologyFunctor C 0).map p.1.hom ≫
          (singleFunctorCompHomologyFunctorIso C 0).hom.app ((homologyFunctor C 0).obj X) =
        𝟙 ((homologyFunctor C 0).obj X) ∧ P (p.1.hom ≫ (singleFunctor C 0).map p.2) := by
  obtain ⟨α, hα, hαuniq⟩ := existsUnique_iso_single_homology_zero X hX
  obtain ⟨f, hf, hfuniq⟩ := hP α
  refine ⟨(α, f), ⟨hα, hf⟩, ?_⟩
  rintro ⟨β, g⟩ ⟨hβ, hg⟩
  have heq : β = α := hαuniq β hβ
  subst β
  exact Prod.ext rfl (hfuniq g hg)

end DerivedCategory
