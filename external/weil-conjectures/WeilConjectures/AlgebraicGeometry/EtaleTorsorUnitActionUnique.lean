/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.CategoryTheory.Sites.Torsor

import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAbelianLiftHom
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat

/-!
# Uniqueness of the inverse-image torsor action

Source: Stacks Project Tag 03Q1 (2), with the adjunction description of inverse image.
(blueprint: lem-weil-pbc-etale-torsor-unit-action-unique)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

private noncomputable def torsorAction {Z : Scheme.{u}}
    (H : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (S : Sheaf.Torsor H) :
    (sheafForget Z.smallEtaleTopology).obj H ⨯ S.sheaf ⟶ S.sheaf :=
  ⟨{ app := fun U ↦ ↾fun x ↦ S.vadd U
        ((prod.fst : (sheafForget Z.smallEtaleTopology).obj H ⨯ S.sheaf ⟶
          (sheafForget Z.smallEtaleTopology).obj H).hom.app U x)
        ((prod.snd : (sheafForget Z.smallEtaleTopology).obj H ⨯ S.sheaf ⟶
          S.sheaf).hom.app U x)
     naturality := by
       intro U V f
       ext x
       dsimp
       rw [S.map_vadd]
       congr 1
       · exact ConcreteCategory.congr_hom
           ((prod.fst : (sheafForget Z.smallEtaleTopology).obj H ⨯ S.sheaf ⟶
             (sheafForget Z.smallEtaleTopology).obj H).hom.naturality f) x
       · exact ConcreteCategory.congr_hom
           ((prod.snd : (sheafForget Z.smallEtaleTopology).obj H ⨯ S.sheaf ⟶
             S.sheaf).hom.naturality f) x }⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- Two inverse-image actions specified on the adjunction units agree via their sheaf iso.
Source: Stacks Project Tag 03Q1 (2), and Tag 0A5G action-transport argument.
(blueprint: lem-weil-pbc-etale-torsor-unit-action-unique)

Proof: Regard each action as a morphism from the product of the underlying coefficient
sheaf and the underlying torsor sheaf. The set inverse image preserves binary products,
and its comparison with abelian inverse image is compatible with the adjunction units.
Conjugate the two downstairs action maps through E₁ and E₂ to maps with common source
the inverse image of that product and common target the inverse image of T.sheaf.
Apply the adjunction hom-set bijection. Its unit on the product is the pair of the
units on its factors. The two stated equations imply equality of the adjoints at
every section (g,t) over every W. Therefore the adjoints are equal as sheaf morphisms,
and injectivity of the adjunction bijection gives equality of the two action maps.
Conjugating back proves the displayed equivariance for every downstairs section,
including those that are only locally in the image of a unit. No finiteness,
representability, or equivalence of scheme categories is used. -/
theorem etale_torsor_unit_action_unique
    {Y Y₀ : Scheme.{u}} (i : Y₀ ⟶ Y)
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (T : Sheaf.Torsor G)
    (S₁ S₂ : Sheaf.Torsor ((upperStar AddCommGrpCat.{u + 1} i).obj G))
    (E₁ : (Scheme.etaleSetPullback i).obj T.sheaf ≅ S₁.sheaf)
    (E₂ : (Scheme.etaleSetPullback i).obj T.sheaf ≅ S₂.sheaf)
    (h₁ :
    (∀ (W : Y.Etale) (g : G.obj.obj (op W)) (t : T.sheaf.obj.obj (op W)),
      E₁.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
          (Y.smallGrothendieckTopology @Etale)
          (Y₀.smallGrothendieckTopology @Etale)).unit.app T.sheaf).hom.app (op W)
            (T.vadd (op W) g t)) =
      S₁.vadd (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G).hom.app
          (op W) g)
        (E₁.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
            (Y.smallGrothendieckTopology @Etale)
            (Y₀.smallGrothendieckTopology @Etale)).unit.app T.sheaf).hom.app (op W) t))))
    (h₂ :
    (∀ (W : Y.Etale) (g : G.obj.obj (op W)) (t : T.sheaf.obj.obj (op W)),
      E₂.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
          (Y.smallGrothendieckTopology @Etale)
          (Y₀.smallGrothendieckTopology @Etale)).unit.app T.sheaf).hom.app (op W)
            (T.vadd (op W) g t)) =
      S₂.vadd (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G).hom.app
          (op W) g)
        (E₂.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
            (Y.smallGrothendieckTopology @Etale)
            (Y₀.smallGrothendieckTopology @Etale)).unit.app T.sheaf).hom.app (op W) t))))
    : ∀ (U : Y₀.Etaleᵒᵖ)
      (g : ((upperStar AddCommGrpCat.{u + 1} i).obj G).obj.obj U)
      (x : S₁.sheaf.obj.obj U),
      (E₁.symm ≪≫ E₂).hom.hom.app U (S₁.vadd U g x) =
        S₂.vadd U g ((E₁.symm ≪≫ E₂).hom.hom.app U x) := by
  let b := MorphismProperty.Over.pullback @Etale ⊤ i
  let L := Scheme.etaleSetPullback i
  let F := sheafForget (D := AddCommGrpCat.{u + 1}) Y.smallEtaleTopology
  let F₀ := sheafForget (D := AddCommGrpCat.{u + 1}) Y₀.smallEtaleTopology
  let R := b.sheafPushforwardContinuous (Type (u + 1))
    (Y.smallGrothendieckTopology @Etale) (Y₀.smallGrothendieckTopology @Etale)
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
    (Type (u + 1)) (Y.smallGrothendieckTopology @Etale)
    (Y₀.smallGrothendieckTopology @Etale)
  have hL : PreservesFiniteLimits L := by
    unfold L Scheme.etaleSetPullback Functor.sheafPullbackConstruction.sheafPullback
    let : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
      AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} (Type (u + 1))
    infer_instance
  obtain ⟨ea, ha⟩ := etaleInverseImageAbelianLift_hom Y₀ Y i hL
  let c := ea.app G
  have hu : F.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G) ≫
      R.map c.hom = a.unit.app (F.obj G) := by
    have hh := ha G _ (𝟙 _)
    rw [(upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).homEquiv_id] at hh
    have hh' : F.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G) =
        a.homEquiv _ _ c.inv := by simpa [F, a, b, c] using hh
    rw [hh', Adjunction.homEquiv_unit, Category.assoc, ← R.map_comp,
      c.inv_hom_id]
    exact (congrArg (fun f ↦ a.unit.app (F.obj G) ≫ f)
      (R.map_id (L.obj (F.obj G)))).trans (Category.comp_id _)
  have hu' : a.unit.app (F.obj G) ≫ R.map c.inv =
      F.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G) := by
    rw [← hu, Category.assoc, ← R.map_comp, c.hom_inv_id, R.map_id]
    rfl
  let p := prodComparison L (F.obj G) T.sheaf
  let k₁ := p ≫ prod.map c.inv E₁.hom
  let k₂ := p ≫ prod.map c.inv E₂.hom
  let q := E₁.inv ≫ E₂.hom
  have hkfst (S : Sheaf.Torsor ((upperStar AddCommGrpCat.{u + 1} i).obj G))
      (E : L.obj T.sheaf ≅ S.sheaf) :
      a.unit.app (F.obj G ⨯ T.sheaf) ≫ R.map (p ≫ prod.map c.inv E.hom) ≫
        R.map (prod.fst : F₀.obj ((upperStar AddCommGrpCat.{u + 1} i).obj G) ⨯
          S.sheaf ⟶ _) =
      (prod.fst : F.obj G ⨯ T.sheaf ⟶ _) ≫
        F.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G) := by
    simp only [← R.map_comp, Category.assoc, prod.map_fst]
    change a.unit.app (F.obj G ⨯ T.sheaf) ≫
      R.map (prodComparison L _ _ ≫ prod.fst ≫ c.inv) = _
    rw [prodComparison_fst_assoc, R.map_comp, ← Category.assoc]
    have hn := a.unit.naturality (prod.fst : F.obj G ⨯ T.sheaf ⟶ F.obj G)
    change prod.fst ≫ a.unit.app (F.obj G) =
      a.unit.app (F.obj G ⨯ T.sheaf) ≫ R.map (L.map prod.fst) at hn
    rw [← hn, Category.assoc, hu']
    rfl
  have hksnd (S : Sheaf.Torsor ((upperStar AddCommGrpCat.{u + 1} i).obj G))
      (E : L.obj T.sheaf ≅ S.sheaf) :
      a.unit.app (F.obj G ⨯ T.sheaf) ≫ R.map (p ≫ prod.map c.inv E.hom) ≫
        R.map (prod.snd : F₀.obj ((upperStar AddCommGrpCat.{u + 1} i).obj G) ⨯
          S.sheaf ⟶ _) =
      (prod.snd : F.obj G ⨯ T.sheaf ⟶ _) ≫ a.unit.app T.sheaf ≫ R.map E.hom := by
    have hs : p ≫ prod.map c.inv E.hom ≫
        (prod.snd : F₀.obj ((upperStar AddCommGrpCat.{u + 1} i).obj G) ⨯ S.sheaf ⟶ _) =
        p ≫ prod.snd ≫ E.hom := by
      exact congrArg (fun h ↦ p ≫ h) (prod.map_snd c.inv E.hom)
    rw [← R.map_comp, Category.assoc, hs]
    change a.unit.app (F.obj G ⨯ T.sheaf) ≫
      R.map (prodComparison L _ _ ≫ prod.snd ≫ E.hom) = _
    rw [prodComparison_snd_assoc, R.map_comp, ← Category.assoc]
    have hn := a.unit.naturality (prod.snd : F.obj G ⨯ T.sheaf ⟶ T.sheaf)
    change prod.snd ≫ a.unit.app T.sheaf =
      a.unit.app (F.obj G ⨯ T.sheaf) ≫ R.map (L.map prod.snd) at hn
    rw [← hn, Category.assoc]
    rfl
  have hk : k₁ ≫ torsorAction _ S₁ ≫ q = k₂ ≫ torsorAction _ S₂ := by
    apply (a.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    ext W z
    let g := (prod.fst : F.obj G ⨯ T.sheaf ⟶ F.obj G).hom.app W z
    let t := (prod.snd : F.obj G ⨯ T.sheaf ⟶ T.sheaf).hom.app W z
    have hf₁ := congrArg (fun f : F.obj G ⨯ T.sheaf ⟶
      R.obj (F₀.obj ((upperStar AddCommGrpCat.{u + 1} i).obj G)) ↦
        f.hom.app W z) (hkfst S₁ E₁)
    have hf₂ := congrArg (fun f : F.obj G ⨯ T.sheaf ⟶
      R.obj (F₀.obj ((upperStar AddCommGrpCat.{u + 1} i).obj G)) ↦
        f.hom.app W z) (hkfst S₂ E₂)
    have hs₁ := congrArg (fun f : F.obj G ⨯ T.sheaf ⟶ R.obj S₁.sheaf ↦
      f.hom.app W z) (hksnd S₁ E₁)
    have hs₂ := congrArg (fun f : F.obj G ⨯ T.sheaf ⟶ R.obj S₂.sheaf ↦
      f.hom.app W z) (hksnd S₂ E₂)
    change E₂.hom.hom.app (op (b.obj W.unop))
      (E₁.inv.hom.app (op (b.obj W.unop))
        (S₁.vadd (op (b.obj W.unop)) _ _)) = S₂.vadd (op (b.obj W.unop)) _ _
    change (prod.fst : F₀.obj ((upperStar AddCommGrpCat.{u + 1} i).obj G) ⨯
        S₁.sheaf ⟶ _).hom.app (op (b.obj W.unop))
          (k₁.hom.app (op (b.obj W.unop))
            ((a.unit.app (F.obj G ⨯ T.sheaf)).hom.app W z)) =
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G).hom.app W g
      at hf₁
    change (prod.snd : F₀.obj ((upperStar AddCommGrpCat.{u + 1} i).obj G) ⨯
        S₁.sheaf ⟶ _).hom.app (op (b.obj W.unop))
          (k₁.hom.app (op (b.obj W.unop))
            ((a.unit.app (F.obj G ⨯ T.sheaf)).hom.app W z)) =
      E₁.hom.hom.app (op (b.obj W.unop)) ((a.unit.app T.sheaf).hom.app W t) at hs₁
    change (prod.fst : F₀.obj ((upperStar AddCommGrpCat.{u + 1} i).obj G) ⨯
        S₂.sheaf ⟶ _).hom.app (op (b.obj W.unop))
          (k₂.hom.app (op (b.obj W.unop))
            ((a.unit.app (F.obj G ⨯ T.sheaf)).hom.app W z)) =
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G).hom.app W g
      at hf₂
    change (prod.snd : F₀.obj ((upperStar AddCommGrpCat.{u + 1} i).obj G) ⨯
        S₂.sheaf ⟶ _).hom.app (op (b.obj W.unop))
          (k₂.hom.app (op (b.obj W.unop))
            ((a.unit.app (F.obj G ⨯ T.sheaf)).hom.app W z)) =
      E₂.hom.hom.app (op (b.obj W.unop)) ((a.unit.app T.sheaf).hom.app W t) at hs₂
    erw [hf₁, hs₁, hf₂, hs₂, ← h₁ W.unop g t]
    have hi := congrArg (fun f : L.obj T.sheaf ⟶ L.obj T.sheaf ↦
      f.hom.app (op (b.obj W.unop))
        ((a.unit.app T.sheaf).hom.app W (T.vadd W g t))) E₁.hom_inv_id
    change E₁.inv.hom.app (op (b.obj W.unop))
      (E₁.hom.hom.app (op (b.obj W.unop)) _) = _ at hi
    erw [hi]
    exact h₂ W.unop g t
  have hm : k₁ ≫ prod.map (𝟙 (F₀.obj ((upperStar AddCommGrpCat.{u + 1} i).obj G))) q =
      k₂ := by
    dsimp only [k₁, k₂, q]
    rw [Category.assoc, prod.map_map]
    simp only [Iso.hom_inv_id_assoc]
    rfl
  have : IsIso k₁ := by
    dsimp only [k₁, p]
    infer_instance
  have hq : torsorAction _ S₁ ≫ q =
      prod.map (𝟙 (F₀.obj ((upperStar AddCommGrpCat.{u + 1} i).obj G))) q ≫
        torsorAction _ S₂ := by
    apply (cancel_epi k₁).mp
    calc
      k₁ ≫ torsorAction _ S₁ ≫ q = k₂ ≫ torsorAction _ S₂ := hk
      _ = k₁ ≫ prod.map (𝟙 _) q ≫ torsorAction _ S₂ := by
        rw [← hm, Category.assoc]
        rfl
  intro U g x
  let ev := (sheafSections Y₀.smallEtaleTopology (Type (u + 1))).obj U
  have : PreservesLimitsOfShape (Discrete WalkingPair) ev := by
    dsimp [ev, sheafSections]
    change PreservesLimitsOfShape (Discrete WalkingPair)
      (sheafToPresheaf Y₀.smallEtaleTopology (Type (u + 1)) ⋙
        (evaluation _ _).obj U)
    infer_instance
  let B := F₀.obj ((upperStar AddCommGrpCat.{u + 1} i).obj G)
  let z := (PreservesLimitPair.iso ev B S₁.sheaf).inv
    ((Types.binaryProductIso (ev.obj B) (ev.obj S₁.sheaf)).inv (g, x))
  have hzfst : (prod.fst : B ⨯ S₁.sheaf ⟶ B).hom.app U z = g := by
    have hf := ConcreteCategory.congr_hom
      (PreservesLimitPair.iso_inv_fst ev B S₁.sheaf)
      ((Types.binaryProductIso (ev.obj B) (ev.obj S₁.sheaf)).inv (g, x))
    exact hf.trans (Types.binaryProductIso_inv_comp_fst_apply _ _ _)
  have hzsnd : (prod.snd : B ⨯ S₁.sheaf ⟶ S₁.sheaf).hom.app U z = x := by
    have hf := ConcreteCategory.congr_hom
      (PreservesLimitPair.iso_inv_snd ev B S₁.sheaf)
      ((Types.binaryProductIso (ev.obj B) (ev.obj S₁.sheaf)).inv (g, x))
    exact hf.trans (Types.binaryProductIso_inv_comp_snd_apply _ _ _)
  have hh := congrArg (fun f : B ⨯ S₁.sheaf ⟶ S₂.sheaf ↦ f.hom.app U z) hq
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    types_comp_apply, torsorAction] at hh
  have hmf := congrArg (fun f : B ⨯ S₁.sheaf ⟶ B ↦ f.hom.app U z)
    (prod.map_fst (𝟙 B) q)
  have hms := congrArg (fun f : B ⨯ S₁.sheaf ⟶ S₂.sheaf ↦ f.hom.app U z)
    (prod.map_snd (𝟙 B) q)
  change (prod.fst : B ⨯ S₂.sheaf ⟶ B).hom.app U
      ((prod.map (𝟙 B) q).hom.app U z) =
    (prod.fst : B ⨯ S₁.sheaf ⟶ B).hom.app U z at hmf
  change (prod.snd : B ⨯ S₂.sheaf ⟶ S₂.sheaf).hom.app U
      ((prod.map (𝟙 B) q).hom.app U z) =
    q.hom.app U ((prod.snd : B ⨯ S₁.sheaf ⟶ S₁.sheaf).hom.app U z) at hms
  change q.hom.app U (S₁.vadd U
      ((prod.fst : B ⨯ S₁.sheaf ⟶ B).hom.app U z)
      ((prod.snd : B ⨯ S₁.sheaf ⟶ S₁.sheaf).hom.app U z)) =
    S₂.vadd U
      ((prod.fst : B ⨯ S₂.sheaf ⟶ B).hom.app U ((prod.map (𝟙 B) q).hom.app U z))
      ((prod.snd : B ⨯ S₂.sheaf ⟶ S₂.sheaf).hom.app U
        ((prod.map (𝟙 B) q).hom.app U z)) at hh
  erw [hmf, hms, hzfst, hzsnd] at hh
  exact hh

end AlgebraicGeometry.Etale
