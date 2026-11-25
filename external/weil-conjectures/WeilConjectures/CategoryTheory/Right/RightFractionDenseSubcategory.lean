/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Right-fraction localization of a dense full subcategory

Source: Stacks Project, `derived.tex`, Tag 0GSL (blueprint:
lem-trf-right-fraction-dense-subcategory).
-/

@[expose] public section

universe u₁ v₁ u₂ v₂ u₃ v₃

open CategoryTheory

namespace CategoryTheory

/-
The hypotheses package the ambient right-fraction axioms, the full subcategory
and its objectwise supply of denominators, and universal-property localizations
of the ambient and restricted categories.  The conclusion records both the
restricted right calculus and the equivalence induced by the inclusion.
-/
/--
(blueprint: lem-trf-right-fraction-dense-subcategory)

Let `C` be a category and `W` a class of arrows containing identities and closed
under composition, satisfying the right-fraction Ore and cancellation axioms.
Let `P` define a full subcategory, and suppose every object of `C` receives a
`W`-arrow from an object of this subcategory.  If `Q` and `QB` are
localizations of `C` at `W` and of the full subcategory at the restricted class,
then the restricted class has a right calculus of fractions and the inclusion
induces an equivalence of the two localized categories.

Source: Stacks Project, Tag 0GSL, categorical right-fraction refinement argument.
Proof plan:
1. Identities and composition restrict to the full subcategory. For an Ore square
   in `C`, choose a denominator from the subcategory into its auxiliary source.
   Precomposing both legs gives the restricted Ore square by fullness; only the
   original denominator, not the other original leg, must belong to `W`.
2. Apply ambient cancellation and precompose the resulting equalizer with a
   denominator from the subcategory. This proves restricted cancellation and
   hence the first conclusion.
3. The localization universal property
   (`lem-weil-pbc-localization-universal-property`) gives `F` and a natural
   isomorphism `QB ⋙ F ≅ P.ι ⋙ Q`. Naturality identifies its conjugated Hom map
   on roofs with the corresponding ambient roof map.
4. Represent an ambient localized arrow by a right fraction
   (`lem-pc-right-fraction-representation`). Refine its source by a denominator
   from the subcategory; the numerator and denominator then lie in the full
   subcategory and represent the same arrow. This proves Hom surjectivity.
5. Represent two restricted arrows by roofs. If their ambient images agree,
   `lem-pc-right-fraction-common-refinement` supplies a common refinement.
   Refine its source again into the subcategory and use the restricted
   common-refinement criterion to obtain equality. Only the common composite
   denominator must belong to `W`; the two refinement legs need not do so.
6. Essential surjectivity of `QB`
   (`lem-trf-localization-essentially-surjective`) transports these Hom
   bijections by conjugation to every pair of objects of `E`. Thus `F` is full
   and faithful.
7. Essential surjectivity of `Q` and a denominator from the subcategory show
   that every object of `D` is isomorphic to an image under `F`. The criterion
   `lem-trf-fully-faithful-ess-surj-equivalence` now gives `F.IsEquivalence`.
-/
theorem rightFractionDenseSubcategory
    {C : Type u₁} [Category.{v₁} C]
    (W : MorphismProperty C)
    (hW : W.HasRightCalculusOfFractions)
    (P : ObjectProperty C)
    (hP : ∀ X : C, ∃ (B : P.FullSubcategory) (s : P.ι.obj B ⟶ X), W s)
    {D : Type u₂} [Category.{v₂} D]
    (Q : C ⥤ D) [Q.IsLocalization W]
    {E : Type u₃} [Category.{v₃} E]
    (QB : P.FullSubcategory ⥤ E)
    [QB.IsLocalization (W.inverseImage P.ι)] :
    (W.inverseImage P.ι).HasRightCalculusOfFractions ∧
      ∃ (F : E ⥤ D), F.IsEquivalence ∧ Nonempty (QB ⋙ F ≅ P.ι ⋙ Q) := by
  classical
  let := hW
  let WB := W.inverseImage P.ι
  -- Refine the ambient Ore and cancellation witnesses into the full subcategory.
  have hWB : WB.HasRightCalculusOfFractions := by
    refine { exists_rightFraction := ?_, ext := ?_ }
    · intro X Y φ
      obtain ⟨ψ, hψ⟩ := (MorphismProperty.LeftFraction.mk
        φ.f.hom φ.s.hom φ.hs).exists_rightFraction
      obtain ⟨B, r, hr⟩ := hP ψ.X'
      refine ⟨⟨ObjectProperty.homMk (r ≫ ψ.s),
        W.comp_mem _ _ hr ψ.hs, ObjectProperty.homMk (r ≫ ψ.f)⟩, ?_⟩
      apply ObjectProperty.hom_ext
      dsimp
      rw [Category.assoc, hψ, ← Category.assoc]
    · intro X Y Y' f g s hs hfg
      obtain ⟨T, t, ht, heq⟩ := hW.ext f.hom g.hom s.hom hs
        (congrArg InducedCategory.Hom.hom hfg)
      obtain ⟨B, r, hr⟩ := hP T
      refine ⟨B, ObjectProperty.homMk (r ≫ t), W.comp_mem _ _ hr ht, ?_⟩
      apply ObjectProperty.hom_ext
      dsimp
      rw [Category.assoc, heq, ← Category.assoc]
  let := hWB
  refine ⟨hWB, ?_⟩
  have hIQ : WB.IsInvertedBy (P.ι ⋙ Q) :=
    fun _ _ f hf ↦ Localization.inverts Q W f.hom hf
  let F := Localization.lift (P.ι ⋙ Q) hIQ QB
  let α : QB ⋙ F ≅ P.ι ⋙ Q := Localization.fac (P.ι ⋙ Q) hIQ QB
  let ambient {X Y : P.FullSubcategory} (z : WB.RightFraction X Y) :
      W.RightFraction X.obj Y.obj := ⟨z.s.hom, z.hs, z.f.hom⟩
  -- Conjugation by the factorization isomorphism preserves the represented roof.
  have hroof {X Y : P.FullSubcategory} (z : WB.RightFraction X Y) :
      α.inv.app X ≫ F.map (z.map QB (Localization.inverts QB WB)) ≫ α.hom.app Y =
        (ambient z).map Q (Localization.inverts Q W) := by
    have : IsIso (Q.map z.s.hom) := Localization.inverts Q W _ z.hs
    apply (cancel_epi (Q.map z.s.hom)).1
    change (P.ι ⋙ Q).map z.s ≫ _ = _
    rw [← Category.assoc, ← Category.assoc, α.inv.naturality z.s]
    simp only [Functor.comp_map, Category.assoc, ← F.map_comp_assoc,
      MorphismProperty.RightFraction.map_s_comp_map]
    exact (α.inv.naturality_assoc z.f _).symm.trans
      (by simp [ambient, MorphismProperty.RightFraction.map])
  have := Localization.essSurj QB WB
  have := Localization.essSurj Q W
  -- Refine the source of an ambient roof to obtain a restricted roof.
  have hsurj {X Y : P.FullSubcategory} (u : Q.obj X.obj ⟶ Q.obj Y.obj) :
      ∃ v : QB.obj X ⟶ QB.obj Y, α.inv.app X ≫ F.map v ≫ α.hom.app Y = u := by
    obtain ⟨z, rfl⟩ := Localization.exists_rightFraction Q W u
    obtain ⟨B, r, hr⟩ := hP z.X'
    let b : WB.RightFraction X Y :=
      ⟨ObjectProperty.homMk (r ≫ z.s), W.comp_mem _ _ hr z.hs,
        ObjectProperty.homMk (r ≫ z.f)⟩
    refine ⟨b.map QB (Localization.inverts QB WB), (hroof b).trans ?_⟩
    apply (MorphismProperty.RightFraction.map_eq_iff Q W _ _).2
    refine ⟨B.obj, 𝟙 _, r, ?_, ?_, ?_⟩
    · simp [ambient, b]
    · simp [ambient, b]
    · simpa [ambient, b] using W.comp_mem _ _ hr z.hs
  -- Refine a common ambient refinement to obtain a restricted common refinement.
  have hinj {X Y : P.FullSubcategory} (u v : QB.obj X ⟶ QB.obj Y)
      (huv : F.map u = F.map v) : u = v := by
    obtain ⟨z, rfl⟩ := Localization.exists_rightFraction QB WB u
    obtain ⟨z', rfl⟩ := Localization.exists_rightFraction QB WB v
    have heq : (ambient z).map Q (Localization.inverts Q W) =
        (ambient z').map Q (Localization.inverts Q W) := by
      rw [← hroof z, ← hroof z', huv]
    obtain ⟨T, t, t', hs, hf, ht⟩ :=
      (MorphismProperty.RightFraction.map_eq_iff Q W _ _).1 heq
    obtain ⟨B, r, hr⟩ := hP T
    apply (MorphismProperty.RightFraction.map_eq_iff QB WB _ _).2
    refine ⟨B, ObjectProperty.homMk (r ≫ t), ObjectProperty.homMk (r ≫ t'),
      ?_, ?_, ?_⟩
    · apply ObjectProperty.hom_ext
      simpa only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
        ambient, Category.assoc] using
        congrArg (fun k ↦ r ≫ k) hs
    · apply ObjectProperty.hom_ext
      simpa only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
        ambient, Category.assoc] using
        congrArg (fun k ↦ r ≫ k) hf
    · change W ((r ≫ t) ≫ z.s.hom)
      rw [Category.assoc]
      exact W.comp_mem _ _ hr ht
  -- Transport Hom bijectivity from objects in the image of QB to all of E.
  have : F.Full := F.full_of_comp_essSurj QB (by
    intro X Y u
    obtain ⟨v, hv⟩ := hsurj (α.inv.app X ≫ u ≫ α.hom.app Y)
    refine ⟨v, ?_⟩
    simpa only [← cancel_epi (α.inv.app X), ← cancel_mono (α.hom.app Y),
      Category.assoc] using hv)
  have : F.Faithful := F.faithful_of_comp_essSurj QB (fun {_ _} u v h ↦ hinj u v h)
  have : F.EssSurj := ⟨fun Y ↦ by
    obtain ⟨B, s, hs⟩ := hP (Q.objPreimage Y)
    exact ⟨QB.obj B, ⟨α.app B ≪≫ Localization.isoOfHom Q W s hs ≪≫
      Q.objObjPreimageIso Y⟩⟩⟩
  exact ⟨F, {}, ⟨α⟩⟩

end CategoryTheory
