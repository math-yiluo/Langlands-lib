/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.LocallySurjective

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

universe u v w

/-! # Local sections after sheafification
Source: literature/stacks-project/sites.tex, Sites, Theorem 00WB and Lemma 00WK
(blueprint: lem-weil-pbc-site-sheafification-sections-local)
-/

-- The unit is locally surjective even without a relation between u and w:
-- its locally generated image is a subsheaf of its target, and the universal
-- property provides a retraction of that image's inclusion.
private theorem unit_locally_surjective
    {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)
    [HasWeakSheafify K (Type w)] (F : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallySurjective K (toSheafify K F) := by
  let G := sheafify K F
  let η := toSheafify K F
  have hG : Presheaf.IsSheaf K G := (presheafToSheaf K (Type w)).obj F |>.property
  have hG' := (isSheaf_iff_isSheaf_of_type K G).mp hG
  let R := (Subfunctor.range η).sheafify K
  have hR : Presheaf.IsSheaf K R.toFunctor :=
    (isSheaf_iff_isSheaf_of_type K R.toFunctor).mpr
      ((Subfunctor.range η).sheafify_isSheaf hG')
  let l := sheafifyLift K (Subfunctor.toRangeSheafify K η) hR
  have hl : l ≫ R.ι = 𝟙 G := by
    apply sheafify_hom_ext K _ _ hG
    dsimp [l]
    rw [← Category.assoc, toSheafify_sheafifyLift]
    simp [Subfunctor.toRangeSheafify, R, η, G]
  rw [Presheaf.isLocallySurjective_iff_range_sheafify_eq_top']
  apply le_antisymm le_top
  intro U s _
  have e : (l.app U s).val = s := by
    have := congrArg (fun t ↦ t.app U s) hl
    simpa [G] using this
  exact e ▸ (l.app U s).property

-- Source: Stacks Project, Sites, Lemma 00WK, local representability.
-- Extract a precoverage cover inside the unit's covering image sieve,
-- then choose a preimage on each covering arrow.
private theorem local_representatives
    {C : Type u} [Category.{v} C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [HasWeakSheafify J.toGrothendieck (Type w)]
    (F : Cᵒᵖ ⥤ Type w) (U : C) (s : (sheafify J.toGrothendieck F).obj (op U)) :
    ∃ (S : Presieve U) (x : ∀ (V : C) (f : V ⟶ U), S f → F.obj (op V)),
      S ∈ J U ∧ ∀ (V : C) (f : V ⟶ U) (hf : S f),
        (sheafify J.toGrothendieck F).map f.op s =
          (toSheafify J.toGrothendieck F).app (op V) (x V f hf) := by
  classical
  have : Presheaf.IsLocallySurjective J.toGrothendieck
      (toSheafify J.toGrothendieck F) := unit_locally_surjective _ _
  obtain ⟨S, hS, hle⟩ :=
    J.mem_toGrothendieck_iff_of_isStableUnderComposition.mp
      (Presheaf.imageSieve_mem J.toGrothendieck (toSheafify J.toGrothendieck F)
        (U := op U) s)
  exact ⟨S, fun V f hf ↦ (hle V f hf).choose, hS,
    fun V f hf ↦ (hle V f hf).choose_spec.symm⟩

-- Source: Stacks Project, Sites, Lemma 00WK, converse. Local agreement
-- maps to local agreement in G; separatedness gives compatibility, and
-- the sheaf condition glues the family uniquely.
private theorem local_descent
    {C : Type u} [Category.{v} C]
    (J : Precoverage C) {F G : Cᵒᵖ ⥤ Type w} (η : F ⟶ G)
    (hG : Presieve.IsSheaf J.toGrothendieck G) :
    (∀ (U : C) (S : Presieve U) (_ : S ∈ J U)
      (x : ∀ (V : C) (f : V ⟶ U), S f → F.obj (op V)),
      (∀ (V W : C) (f : V ⟶ U) (g : W ⟶ U)
        (hf : S f) (hg : S g),
        ∀ (Z : C) (a : Z ⟶ V) (b : Z ⟶ W), a ≫ f = b ≫ g →
          ∃ (T : Presieve Z), T ∈ J Z ∧
            ∀ (Y : C) (h : Y ⟶ Z), T h →
              F.map (h ≫ a).op (x V f hf) = F.map (h ≫ b).op (x W g hg)) →
      ∃! s : G.obj (op U),
        ∀ (V : C) (f : V ⟶ U) (hf : S f),
          G.map f.op s =
            η.app (op V) (x V f hf)) := by
  intro U S hS x hx
  let y : S.FamilyOfElements G := fun V f hf ↦ η.app (op V) (x V f hf)
  have hy : y.Compatible := by
    intro V W Z a b f g hf hg hab
    obtain ⟨T, hT, ht⟩ := hx V W f g hf hg Z a b hab
    apply (hG.isSheafFor_of_mem_precoverage hT).isSeparatedFor.ext
    intro Y h hh
    dsimp [y]
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply,
      ← op_comp, ← op_comp, ← NatTrans.naturality_apply, ← NatTrans.naturality_apply,
      ht Y h hh]
  exact hG.isSheafFor_of_mem_precoverage hS y hy

/-- Local representability and descent for sheafification on a site.
Source: Sites, Theorem Tag 00WB and Lemma Tag 00WK
(blueprint: lem-weil-pbc-site-sheafification-sections-local).
The unit is locally surjective by the image-subsheaf argument above. Extract a
precoverage cover and representatives from each covering image sieve. Local
injectivity of the unit gives local equality of representatives on every overlap.
Conversely, local agreement gives compatibility in the sheaf by separatedness;
the sheaf condition then glues uniquely. Finally, local injectivity and the
precoverage criterion give local equality of any sections with equal images.
The value universe includes both site universes, as required for the plus construction.
-/
theorem sheafification_sections_local
    {C : Type u} [Category.{w} C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [HasWeakSheafify J.toGrothendieck (Type (max u w))]
    (F : Cᵒᵖ ⥤ Type (max u w)) :
    (∀ (U : C) (s : (sheafify J.toGrothendieck F).obj (op U)),
      ∃ (S : Presieve U) (x : ∀ (V : C) (f : V ⟶ U), S f → F.obj (op V)),
        S ∈ J U ∧
        (∀ (V : C) (f : V ⟶ U) (hf : S f),
          (sheafify J.toGrothendieck F).map f.op s =
            (toSheafify J.toGrothendieck F).app (op V) (x V f hf)) ∧
        (∀ (V W : C) (f : V ⟶ U) (g : W ⟶ U)
          (hf : S f) (hg : S g),
          ∀ (Z : C) (a : Z ⟶ V) (b : Z ⟶ W), a ≫ f = b ≫ g →
            ∃ (T : Presieve Z), T ∈ J Z ∧
              ∀ (Y : C) (h : Y ⟶ Z), T h →
                F.map (h ≫ a).op (x V f hf) = F.map (h ≫ b).op (x W g hg))) ∧
    (∀ (U : C) (S : Presieve U) (_ : S ∈ J U)
      (x : ∀ (V : C) (f : V ⟶ U), S f → F.obj (op V)),
      (∀ (V W : C) (f : V ⟶ U) (g : W ⟶ U)
        (hf : S f) (hg : S g),
        ∀ (Z : C) (a : Z ⟶ V) (b : Z ⟶ W), a ≫ f = b ≫ g →
          ∃ (T : Presieve Z), T ∈ J Z ∧
            ∀ (Y : C) (h : Y ⟶ Z), T h →
              F.map (h ≫ a).op (x V f hf) = F.map (h ≫ b).op (x W g hg)) →
      ∃! s : (sheafify J.toGrothendieck F).obj (op U),
        ∀ (V : C) (f : V ⟶ U) (hf : S f),
          (sheafify J.toGrothendieck F).map f.op s =
            (toSheafify J.toGrothendieck F).app (op V) (x V f hf)) ∧
    (∀ (U : C) (p q : F.obj (op U)),
      (toSheafify J.toGrothendieck F).app (op U) p =
        (toSheafify J.toGrothendieck F).app (op U) q →
      ∃ (S : Presieve U), S ∈ J U ∧
        ∀ (V : C) (f : V ⟶ U) (_ : S f),
          F.map f.op p = F.map f.op q) := by
  have hlocal : ∀ (U : C) (p q : F.obj (op U)),
      (toSheafify J.toGrothendieck F).app (op U) p =
        (toSheafify J.toGrothendieck F).app (op U) q →
      ∃ (S : Presieve U), S ∈ J U ∧
        ∀ (V : C) (f : V ⟶ U), S f → F.map f.op p = F.map f.op q := by
    intro U p q hpq
    obtain ⟨S, hS, hle⟩ :=
      J.mem_toGrothendieck_iff_of_isStableUnderComposition.mp
        (Presheaf.equalizerSieve_mem J.toGrothendieck
          (toSheafify J.toGrothendieck F) p q hpq)
    exact ⟨S, hS, fun V f hf ↦ hle V f hf⟩
  refine ⟨?_, ?_, hlocal⟩
  · intro U s
    obtain ⟨S, x, hS, hx⟩ := local_representatives J F U s
    refine ⟨S, x, hS, hx, ?_⟩
    intro V W f g hf hg Z a b hab
    obtain ⟨T, hT, ht⟩ := hlocal Z
      (F.map a.op (x V f hf)) (F.map b.op (x W g hg)) (by
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply,
        ← hx V f hf, ← hx W g hg, ← Functor.map_comp_apply,
        ← Functor.map_comp_apply, ← op_comp, ← op_comp, hab])
    refine ⟨T, hT, ?_⟩
    intro Y h hh
    simpa only [op_comp, Functor.map_comp_apply] using ht Y h hh
  · exact local_descent J (toSheafify J.toGrothendieck F)
      ((isSheaf_iff_isSheaf_of_type J.toGrothendieck _).mp
        ((presheafToSheaf J.toGrothendieck (Type (max u w))).obj F).property)

end CategoryTheory
