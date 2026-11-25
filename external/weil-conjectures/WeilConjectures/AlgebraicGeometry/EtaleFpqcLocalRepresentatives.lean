/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageSectionDescription
import WeilConjectures.AlgebraicGeometry.EtaleFpqcRepresentativeOpen

/-! # Étale local existence for compatible fpqc section data

Source: Stacks Project, Tag 09XN, agreement opens and local representatives.
(blueprint: lem-weil-pbc-etale-fpqc-local-representatives). -/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Source: Stacks Project, Tag 09XN, proof, paragraphs beginning "Let V" and
"By construction"; Tag 09XM for the agreement-open universal property.
(blueprint: lem-weil-pbc-etale-fpqc-local-representatives).

This asserts local existence only. It neither chooses sections nor asserts that
representatives are compatible on common test objects.

Proof:
For every étale V/S and t in F(V), take the largest agreement opens on each
T_i ×_S V between the unit image of t and the restriction of s_i. The overlap
hypothesis and the unit-compatible composition isomorphisms identify their two
inverse images on double overlaps. Descend these opens to W in V using fpqc
open descent. Restricting t to W gives the matching equation on every T_i ×_S W
by the agreement-open universal property and unit naturality.
Locally on T_i, the inverse-image section description expresses s_i as the
restriction of a unit image of some t on an étale V/S. Apply the preceding
construction to every representative. Its test scheme factors through W: after
base change by every T_j it lies in the corresponding agreement open by the
overlap hypothesis; joint surjectivity detects containment in the descended open.
These test schemes cover all T_i. Since the T_i jointly cover S, the resulting
W jointly cover S, and therefore generate a covering sieve in the small étale
topology. Take P to be their arrows into the identity object. Every such arrow
admits its restricted section satisfying the displayed matching equation.
For an empty base, take the empty covering presieve; no choice of a point or a
nonempty index type is needed. -/
theorem etaleFpqcSections_exists_local_representatives
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
    ∃ P : Presieve (Scheme.Etale.mk (𝟙 S)),
      Sieve.generate P ∈ S.smallEtaleTopology (Scheme.Etale.mk (𝟙 S)) ∧
      ∀ (V : S.Etale) (f : V ⟶ Scheme.Etale.mk (𝟙 S)), P f →
        ∃ t : F.obj.obj (op V), ∀ i,
      let β := MorphismProperty.Over.pullback @Etale ⊤ (g i)
      let H := (Scheme.etaleSetPullback (g i)).obj F
      let η := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        β (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
        ((T i).smallGrothendieckTopology @Etale)).unit.app F
      η.hom.app (op V) t =
        H.obj.map (MorphismProperty.Over.homMk (β.obj V).hom
          (Category.comp_id _) : β.obj V ⟶ Scheme.Etale.mk (𝟙 (T i))).op (s i) := by
  classical
  let M (V : S.Etale) (t : F.obj.obj (op V)) : Prop := ∀ i,
    let β := MorphismProperty.Over.pullback @Etale ⊤ (g i)
    let H := (Scheme.etaleSetPullback (g i)).obj F
    let η := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      β (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
      ((T i).smallGrothendieckTopology @Etale)).unit.app F
    η.hom.app (op V) t =
      H.obj.map (MorphismProperty.Over.homMk (β.obj V).hom
        (Category.comp_id _) : β.obj V ⟶ Scheme.Etale.mk (𝟙 (T i))).op (s i)
  have local_rep (x : S) : ∃ (W : S.Etale) (w : W.left) (t : F.obj.obj (op W)),
      W.hom w = x ∧ M W t := by
    obtain ⟨Y, f, hf, y, hy⟩ := Scheme.JointlySurjective.exists_eq
      (Presieve.ofArrows T g) (Scheme.propQCPrecoverage_le_precoverage S hcover) x
    obtain ⟨i⟩ := hf
    obtain ⟨J, Z, π, hπ, hrep⟩ := etaleInverseImageSectionDescription S (T i) (g i) F (s i)
    have hsurj := (Scheme.ofArrows_mem_smallEtaleTopology_iff π).mp hπ
    have hym : y ∈ ⋃ j, Set.range (π j).left := by
      rw [hsurj]
      trivial
    obtain ⟨j, z, hz⟩ := Set.mem_iUnion.mp hym
    obtain ⟨V, a, t, ht⟩ := hrep j
    obtain ⟨U, hu, hU⟩ := etaleFpqcSections_descend_representative_open
      T g hcover F s hcompat i (Z j) (π j) V a t ht
    let W : S.Etale := Scheme.Etale.mk (U.ι ≫ V.hom)
    let b : W ⟶ V := MorphismProperty.Over.homMk U.ι rfl
    let w : W.left := ⟨(a.left ≫ pullback.fst V.hom (g i)) z, hu ⟨z, rfl⟩⟩
    refine ⟨W, w, F.obj.map b.op t, ?_, hU⟩
    have ha : (a.left ≫ pullback.fst V.hom (g i)) ≫ V.hom =
        (π j).left ≫ g i := by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      have ha := a.w
      change a.left ≫ pullback.snd V.hom (g i) = (Z j).hom at ha
      rw [ha]
      have hp := (π j).w
      change (π j).left ≫ 𝟙 (T i) = (Z j).hom at hp
      have hp' : (π j).left = (Z j).hom := (Category.comp_id _).symm.trans hp
      exact congrArg (fun e : (Z j).left ⟶ T i ↦ e ≫ g i) hp'.symm
    change V.hom ((a.left ≫ pullback.fst V.hom (g i)) z) = x
    have hpoint := congrArg (fun e : (Z j).left ⟶ S ↦ e z) ha
    simp only [Scheme.Hom.comp_apply] at hpoint ⊢
    exact hpoint.trans ((congrArg (g i) hz).trans hy)
  choose W w t ht hm using local_rep
  let f (x : S) : W x ⟶ Scheme.Etale.mk (𝟙 S) :=
    MorphismProperty.Over.homMk (W x).hom (Category.comp_id _)
  refine ⟨Presieve.ofArrows W f, ?_, ?_⟩
  · change Sieve.ofArrows W f ∈ S.smallEtaleTopology (Scheme.Etale.mk (𝟙 S))
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨x, w x, ht x⟩
  · intro V f' hf
    obtain ⟨x⟩ := hf
    exact ⟨t x, hm x⟩

end AlgebraicGeometry
