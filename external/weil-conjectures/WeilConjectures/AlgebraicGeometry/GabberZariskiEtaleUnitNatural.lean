/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Sheaves.Functors
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
/-! # Naturality of the restricted étale inverse-image unit
Source: Stacks Project, Tag 09ZF, first proof paragraph.
(blueprint: lem-weil-pbc-gabber-zariski-etale-unit-natural)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The étale unit, transported by the open/base-change identifications, is natural.
Source: Stacks Project, Tag 09ZF (lemma-gabber-h0), first proof paragraph,
and Sites, Tag 00WX, the inverse-image adjunction.
(blueprint: lem-weil-pbc-gabber-zariski-etale-unit-natural).
Proof: restrict the étale adjunction unit along the open-subscheme inclusion.
For an inclusion of opens, the square of base-change identifications commutes:
compose both proposed scheme morphisms with the two pullback projections.
The first projection equality follows from `ha` and functoriality of restriction;
the second follows because the identifications are morphisms over Z. Pullback
uniqueness proves the square commutes. Naturality of the étale unit and of `eX`
and `eZ` now proves naturality of the displayed component functions. These
functions therefore form a presheaf morphism. Both presheaves are sheaves, so
this is a morphism of sheaves to the topological direct image. Its component
formula is the construction itself. No closedness assumption is used here.
-/
theorem gabber_zariski_etale_unit_natural
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v)))
    (Fzar : TopCat.Sheaf (Type (max (u + 1) v)) X.carrier)
    (eX : Fzar.obj ≅
      (MorphismProperty.Comma.lift (P := @Etale) (Q := ⊤) (W := ⊤)
        X.restrictFunctor (fun U => (inferInstance : Etale U.ι)) (fun _ => trivial)
        (fun _ => trivial)).op ⋙ F.obj)
    (iFzar : TopCat.Sheaf (Type (max (u + 1) v)) Z.carrier)
    (eZ : iFzar.obj ≅
      (MorphismProperty.Comma.lift (P := @Etale) (Q := ⊤) (W := ⊤)
        Z.restrictFunctor (fun U => (inferInstance : Etale U.ι)) (fun _ => trivial)
        (fun _ => trivial)).op ⋙
      ((Functor.sheafPullbackConstruction.sheafPullback
        (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
        (X.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)).obj F).obj)
    (a : ∀ W : X.Opens, Scheme.Etale.mk (i ⁻¹ᵁ W).ι ≅
      (MorphismProperty.Over.pullback @Etale ⊤ i).obj (Scheme.Etale.mk W.ι))
    (ha : ∀ W : X.Opens,
      (a W).hom.left ≫ pullback.fst W.ι i = i ∣_ W) :
    ∃ alpha : Fzar ⟶
      ((Opens.map i.base).sheafPushforwardContinuous (Type (max (u + 1) v))
        (Opens.grothendieckTopology X.carrier)
        (Opens.grothendieckTopology Z.carrier)).obj iFzar,
      ∀ (W : X.Opens) (s : Fzar.obj.obj (op W)),
        alpha.hom.app (op W) s =
        eZ.inv.app (op (i ⁻¹ᵁ W))
          (((Functor.sheafPullbackConstruction.sheafPullback
            (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
            (X.smallGrothendieckTopology @Etale)
            (Z.smallGrothendieckTopology @Etale)).obj F).obj.map (a W).hom.op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
              (X.smallGrothendieckTopology @Etale)
              (Z.smallGrothendieckTopology @Etale)).unit.app F).hom.app
                (op (Scheme.Etale.mk W.ι)) (eX.hom.app (op W) s))) := by
  let B := MorphismProperty.Over.pullback @Etale ⊤ i
  let IX := MorphismProperty.Comma.lift (P := @Etale) (Q := ⊤) (W := ⊤)
    X.restrictFunctor (fun U => (inferInstance : Etale U.ι))
    (fun _ => trivial) (fun _ => trivial)
  let IZ := MorphismProperty.Comma.lift (P := @Etale) (Q := ⊤) (W := ⊤)
    Z.restrictFunctor (fun U => (inferInstance : Etale U.ι))
    (fun _ => trivial) (fun _ => trivial)
  let L := Functor.sheafPullbackConstruction.sheafPullback
    B (Type (max (u + 1) v))
    (X.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)
  let eta := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    B (Type (max (u + 1) v))
    (X.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)).unit.app F
  have square {U V : X.Opens} (f : U ⟶ V) :
      IZ.map ((Opens.map i.base).map f) ≫ (a V).hom =
        (a U).hom ≫ B.map (IX.map f) := by
    apply MorphismProperty.Over.Hom.ext
    have hc : ((a U).hom ≫ B.map (IX.map f)).left =
        (a U).hom.left ≫ (B.map (IX.map f)).left := rfl
    rw [hc]
    have hb : (B.map (IX.map f)).left =
        pullback.lift (pullback.fst U.ι i ≫ (IX.map f).left)
          (pullback.snd U.ι i) (by
            rw [Category.assoc, MorphismProperty.Over.w (IX.map f)]
            change pullback.fst U.ι i ≫ U.ι = pullback.snd U.ι i ≫ i
            exact pullback.condition) := rfl
    have hbfst : (B.map (IX.map f)).left ≫ pullback.fst V.ι i =
        pullback.fst U.ι i ≫ (IX.map f).left := by
      rw [hb]
      exact pullback.lift_fst _ _ _
    have hbsnd : (B.map (IX.map f)).left ≫ pullback.snd V.ι i =
        pullback.snd U.ι i := by
      rw [hb]
      exact pullback.lift_snd _ _ _
    apply pullback.hom_ext
    · simp only [MorphismProperty.Comma.comp_left, Category.assoc]
      change _ ≫ (a V).hom.left ≫ pullback.fst V.ι i =
        (a U).hom.left ≫ (B.map (IX.map f)).left ≫ pullback.fst V.ι i
      rw [hbfst, ha, ← Category.assoc, ha]
      change Z.homOfLE (i.preimage_mono f.le) ≫ i ∣_ V = i ∣_ U ≫ X.homOfLE f.le
      exact (morphismRestrict_homOfLE i U V f.le).symm
    · simp only [MorphismProperty.Comma.comp_left, Category.assoc]
      have hV : (a V).hom.left ≫ pullback.snd V.ι i = (i ⁻¹ᵁ V).ι := by
        simpa using (a V).hom.w
      have hU : (a U).hom.left ≫ pullback.snd U.ι i = (i ⁻¹ᵁ U).ι := by
        simpa using (a U).hom.w
      change _ ≫ (a V).hom.left ≫ pullback.snd V.ι i =
        (a U).hom.left ≫ (B.map (IX.map f)).left ≫ pullback.snd V.ι i
      rw [hbsnd, hV, hU]
      simp [IZ]
  let alpha : Fzar ⟶
      ((Opens.map i.base).sheafPushforwardContinuous (Type (max (u + 1) v))
        (Opens.grothendieckTopology X.carrier)
        (Opens.grothendieckTopology Z.carrier)).obj iFzar :=
    ⟨{ app := fun W ↦ eX.hom.app W ≫ eta.hom.app (IX.op.obj W) ≫
          (L.obj F).obj.map (a W.unop).hom.op ≫
          eZ.inv.app ((Opens.map i.base).op.obj W)
       naturality := by
         intro U V f
         dsimp only [Functor.op_obj, Functor.op_map]
         change Fzar.obj.map f ≫ _ = _ ≫ iFzar.obj.map ((Opens.map i.base).map f.unop).op
         rw [eX.hom.naturality_assoc]
         dsimp only [Functor.comp_map, Functor.op_map]
         have hEta := eta.hom.naturality ((IX.map f.unop).op)
         change F.obj.map (IX.map f.unop).op ≫ eta.hom.app (op (IX.obj V.unop)) =
           eta.hom.app (op (IX.obj U.unop)) ≫ (L.obj F).obj.map (B.map (IX.map f.unop)).op
           at hEta
         rw [← Category.assoc (F.obj.map _) _, hEta]
         simp only [Category.assoc]
         rw [← eZ.inv.naturality]
         dsimp only [Functor.comp_map, Functor.op_map]
         rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
           ← op_comp, ← op_comp]
         exact congrArg (fun k ↦ eX.hom.app U ≫ eta.hom.app (op (IX.obj U.unop)) ≫
           (L.obj F).obj.map k.op ≫ eZ.inv.app (op ((Opens.map i.base).obj V.unop)))
           (square f.unop).symm }⟩
  exact ⟨alpha, fun _ _ ↦ rfl⟩

end AlgebraicGeometry
