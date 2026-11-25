/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.EtaleFpqcMatchingFamily

/-! # EtaleSectionsFpqcExistence

Source: Stacks Project, Tag 09XN
(blueprint: lem-weil-pbc-etale-sections-fpqc-existence). -/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Source: Stacks Project, Tag 09XN, existence argument.
(blueprint: lem-weil-pbc-etale-sections-fpqc-existence).

Proof:
For each etale V and section t, take the largest agreement opens between its
pullbacks and the prescribed sections. Overlap compatibility identifies their two
pullbacks. Fpqc open descent gives an open W in V. The local description of inverse
image sections supplies etale local representatives t_ia on V_ia. Apply the preceding
construction to each representative. Compatibility and joint surjectivity imply that
its test scheme factors through W_ia. These W_ia therefore cover S in the etale site.
Two restricted representatives agree on their overlap: their largest agreement open
pulls back to the entire overlap under every T_i, and joint surjectivity makes it the
entire overlap. The sheaf axiom glues the representatives to t. Its pullback agrees
with each prescribed section on its etale representative cover, hence globally by
sheaf separatedness. -/
theorem exists_etaleSection_of_fpqc_cover
    {S : Scheme.{u}} {I : Type v} (T : I → Scheme.{u}) (g : ∀ i, T i ⟶ S)
    (hcover : Presieve.ofArrows T g ∈ Scheme.fpqcPrecoverage S)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (s : ∀ i, ((Scheme.etaleSetPullback (g i)).obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 (T i)))))
    (hcompat : ∀ i j,
      ((Classical.choose etaleSetInverseImageCompositionUnits.2.2
          S (T i) (pullback (g i) (g j)) (g i) (pullback.fst (g i) (g j))).hom.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 (pullback (g i) (g j)))))
        (((Scheme.etaleSetPullback (pullback.fst (g i) (g j))).obj
            ((Scheme.etaleSetPullback (g i)).obj F)).obj.map
          (MorphismProperty.Over.homMk
            (pullback.lift (pullback.fst (g i) (g j)) (𝟙 (pullback (g i) (g j)))
              ((Category.comp_id _).trans (Category.id_comp _).symm))
            (by simp) :
            Scheme.Etale.mk (𝟙 (pullback (g i) (g j))) ⟶
              (MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst (g i) (g j))).obj
                (Scheme.Etale.mk (𝟙 (T i)))).op
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst (g i) (g j))) _
            ((T i).smallGrothendieckTopology @Etale)
            ((pullback (g i) (g j)).smallGrothendieckTopology @Etale)).unit.app
              ((Scheme.etaleSetPullback (g i)).obj F)).hom.app
            (op (Scheme.Etale.mk (𝟙 (T i)))) (s i))) =
        Eq.mp (congrArg (fun k : pullback (g i) (g j) ⟶ S ↦
          ((Scheme.etaleSetPullback k).obj F).obj.obj
            (op (Scheme.Etale.mk (𝟙 (pullback (g i) (g j))))))
          (pullback.condition (f := g i) (g := g j)).symm)
        (((Classical.choose etaleSetInverseImageCompositionUnits.2.2
            S (T j) (pullback (g i) (g j)) (g j) (pullback.snd (g i) (g j))).hom.app F).hom.app
          (op (Scheme.Etale.mk (𝟙 (pullback (g i) (g j)))))
          (((Scheme.etaleSetPullback (pullback.snd (g i) (g j))).obj
              ((Scheme.etaleSetPullback (g j)).obj F)).obj.map
            (MorphismProperty.Over.homMk
              (pullback.lift (pullback.snd (g i) (g j)) (𝟙 (pullback (g i) (g j)))
                ((Category.comp_id _).trans (Category.id_comp _).symm))
              (by simp) :
              Scheme.Etale.mk (𝟙 (pullback (g i) (g j))) ⟶
                (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd (g i) (g j))).obj
                  (Scheme.Etale.mk (𝟙 (T j)))).op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd (g i) (g j))) _
              ((T j).smallGrothendieckTopology @Etale)
              ((pullback (g i) (g j)).smallGrothendieckTopology @Etale)).unit.app
                ((Scheme.etaleSetPullback (g j)).obj F)).hom.app
              (op (Scheme.Etale.mk (𝟙 (T j)))) (s j))))) :
    ∃ t : F.obj.obj (op (Scheme.Etale.mk (𝟙 S))), ∀ i,
      ((Scheme.etaleSetPullback (g i)).obj F).obj.map
        (MorphismProperty.Over.homMk (pullback.lift (g i) (𝟙 (T i))
          ((Category.comp_id _).trans (Category.id_comp _).symm)) (by simp) :
          Scheme.Etale.mk (𝟙 (T i)) ⟶
            (MorphismProperty.Over.pullback @Etale ⊤ (g i)).obj (Scheme.Etale.mk (𝟙 S))).op
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ (g i)) _
          (S.smallGrothendieckTopology @Etale)
          ((T i).smallGrothendieckTopology @Etale)).unit.app F).hom.app
            (op (Scheme.Etale.mk (𝟙 S))) t) = s i := by
  classical
  obtain ⟨R, x, hR, hx, hmatch⟩ :=
    etaleFpqcSections_exists_matching_family T g hcover F s hcompat
  let hF := F.property.isSheafFor R hR
  let t := hF.amalgamate x hx
  refine ⟨t, ?_⟩
  intro i
  let β := MorphismProperty.Over.pullback @Etale ⊤ (g i)
  let H := (Scheme.etaleSetPullback (g i)).obj F
  let η := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    β (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
    ((T i).smallGrothendieckTopology @Etale)).unit.app F
  let E := Scheme.Etale.mk (𝟙 S)
  let q : β.obj E ⟶ Scheme.Etale.mk (𝟙 (T i)) :=
    MorphismProperty.Over.homMk (β.obj E).hom (Category.comp_id _)
  have hRp : R.functorPushforward β ∈ (T i).smallEtaleTopology (β.obj E) :=
    (Scheme.Hom.coverPreserving_etale (g i)).cover_preserve hR
  have heq : η.hom.app (op E) t = H.obj.map q.op (s i) := by
    apply (H.property.isSheafFor _ hRp).isSeparatedFor.ext
    intro Z a ha
    obtain ⟨V, f, b, hf, rfl⟩ := ha
    have hn := η.hom.naturality_apply f.op t
    change η.hom.app (op V) (F.obj.map f.op t) =
      H.obj.map (β.map f).op (η.hom.app (op E) t) at hn
    have ht : F.obj.map f.op t = x f hf := hF.valid_glue hx f hf
    have hq : β.map f ≫ q =
        (MorphismProperty.Over.homMk (β.obj V).hom (Category.comp_id _) :
          β.obj V ⟶ Scheme.Etale.mk (𝟙 (T i))) := by
      apply MorphismProperty.Over.Hom.ext
      exact (β.map f).w
    have hu : H.obj.map (β.map f).op (η.hom.app (op E) t) =
        H.obj.map (β.map f).op (H.obj.map q.op (s i)) := by
      calc
        _ = η.hom.app (op V) (F.obj.map f.op t) := hn.symm
        _ = η.hom.app (op V) (x f hf) := congrArg (η.hom.app (op V)) ht
        _ = H.obj.map (MorphismProperty.Over.homMk (β.obj V).hom
            (Category.comp_id _) : β.obj V ⟶ Scheme.Etale.mk (𝟙 (T i))).op (s i) :=
          hmatch i V f hf
        _ = _ := by
          have h := congrArg (fun k ↦ H.obj.map k.op (s i)) hq
          simpa only [op_comp, Functor.map_comp, types_comp_apply] using h.symm
    simpa only [op_comp, Functor.map_comp, types_comp_apply] using
      congrArg (fun z ↦ H.obj.map b.op z) hu
  let δ : Scheme.Etale.mk (𝟙 (T i)) ⟶ β.obj E :=
    MorphismProperty.Over.homMk (pullback.lift (g i) (𝟙 (T i))
      ((Category.comp_id _).trans (Category.id_comp _).symm)) (by
        change pullback.lift _ _ _ ≫ pullback.snd _ _ = 𝟙 (T i)
        simp)
  change H.obj.map δ.op (η.hom.app (op E) t) = s i
  rw [heq, ← types_comp_apply, ← H.obj.map_comp, ← op_comp]
  have hδq : δ ≫ q = 𝟙 _ := by
    apply MorphismProperty.Over.Hom.ext
    change pullback.lift _ _ _ ≫ pullback.snd _ _ = 𝟙 (T i)
    simp
  rw [hδq, op_id, H.obj.map_id]
  rfl

end AlgebraicGeometry
