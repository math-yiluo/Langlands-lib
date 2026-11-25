/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits

import WeilConjectures.AlgebraicGeometry.EtaleSectionsFpqcExistence
import WeilConjectures.AlgebraicGeometry.EtaleSectionsFpqcSeparated

/-!
# Fpqc descent of sections of an etale sheaf of sets

Source: Stacks Project, Etale Cohomology, Lemma 59.39.2, Tag 09XN
(blueprint: lem-weil-pbc-etale-sections-fpqc-descent).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Source: Stacks Project, Tag 09XN, second assertion and proof
(blueprint: lem-weil-pbc-etale-sections-fpqc-descent).
Every compatible family has a unique global section; this is precisely bijectivity
onto the equalizer. Global sections are evaluated at `Scheme.Etale.mk (𝟙 _)`. The
pullback of a global section along `e : T ⟶ S` is the adjunction unit followed by
restriction along the canonical map `Etale.mk (𝟙 T) ⟶ (Etale.mk (𝟙 S)) ×_S T`
(`pullback.lift e (𝟙 T)`). On an overlap the two pullbacks are compared through the
composition isomorphism, the unique unit-compatible one of
`etaleSetInverseImageCompositionUnits`, and `pullback.condition`. For a singleton
family this says a section descends uniquely iff its two pullbacks agree.

Proof:
1. For an etale V over S and t in F(V), use
   lem-weil-pbc-etale-sections-equal-open (Tag 09XM) to form the largest agreement
   opens in T_i times_S V. Compatibility makes their overlap pullbacks equal,
   using lem-weil-pbc-sets-etale-inverse-image-composition-units.
2. Descend these opens by lem-weil-pbc-etale-open-fpqc-descent (Tag 03N0).
3. By lem-weil-pbc-etale-inverse-image-section-description, each local section
   comes etale locally from a section t_ia on an etale V_ia over S. Steps 1 and 2
   give opens W_ia of V_ia on which t_ia agrees with every s_j after pullback.
   Joint surjectivity implies T_ia maps into W_ia.
4. The W_ia cover S etale locally. Their sections agree on overlaps: their
   agreement open pulls back to the whole overlap under each T_k, hence is the
   whole overlap by joint surjectivity. The sheaf axiom of
   situation-conventions glues them to s. Local agreement gives the
   prescribed pullbacks. The agreement open of two such s contains the images
   of every T_i, hence is S, proving uniqueness. Specialize to a singleton. -/
theorem existsUnique_etaleSection_of_fpqc_cover
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
    ∃! t : F.obj.obj (op (Scheme.Etale.mk (𝟙 S))), ∀ i,
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
  obtain ⟨t, ht⟩ := exists_etaleSection_of_fpqc_cover T g hcover F s hcompat
  refine ⟨t, ht, ?_⟩
  intro t' ht'
  exact etaleSections_eq_of_fpqc_pullbacks T g hcover F t' t
    (fun i ↦ (ht' i).trans (ht i).symm)

end AlgebraicGeometry
