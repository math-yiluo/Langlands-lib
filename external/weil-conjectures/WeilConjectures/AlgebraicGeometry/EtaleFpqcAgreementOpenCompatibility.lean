/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenArbitraryCriterion
import WeilConjectures.AlgebraicGeometry.EtaleFpqcAgreementSectionsOverlap

/-! # Compatibility of agreement opens for a matching family
Source: Stacks Project, Tag 09XN, agreement-open paragraph.
(blueprint: lem-weil-pbc-etale-fpqc-agreement-open-compatibility). -/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Source: Stacks Project, Tag 09XN (lemma-describe-pullback), paragraph
beginning "Let V", using Tag 09XM and composition units in Tags 03CB and 03CC.
(blueprint: lem-weil-pbc-etale-fpqc-agreement-open-compatibility).

Proof: On Q_j = V ×_S T_j compare the unit image of t with the pullback of s_j.
The given E_j is their agreement open, tested by every étale restriction.
First compare E_j with the canonical largest agreement open of the two sections
on Q_j. Test each candidate's own open immersion in the ordinary étale criterion;
the restriction isomorphism identifies this criterion with the canonical one,
so the two inclusions prove equality. Thus E_j also has the arbitrary-scheme-map
criterion. On D = Q_i ×_V Q_j, both projections to Q_i and Q_j are arbitrary maps.
Use inverse-image restriction and the agreement-open universal property to
identify the inverse images of E_i and E_j as agreement opens on D. The two
unit images of t agree after the composition isomorphisms: the composition unit
formula and unit naturality identify both with pullback of t along D → V → S.
The other two sections agree because D maps to T_i ×_S T_j; pull back hcompat
along this map. Fibre-product associativity is determined by its projections,
so the identifications use exactly those in hcompat. Injectivity of the
composition and restriction isomorphisms reflects these equalities. Uniqueness
of the agreement open on D now gives the asserted equality of opens. No fpqc
hypothesis is needed for this calculation. Empty D gives equality of empty opens. -/
theorem etaleFpqcAgreementOpens_compatible
    {S : Scheme.{u}} {I : Type v} (T : I → Scheme.{u}) (g : ∀ i, T i ⟶ S)
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
              (op (Scheme.Etale.mk (𝟙 (T j)))) (s j)))))
    (V : S.Etale) (t : F.obj.obj (op V))
    (E : ∀ j, (pullback V.hom (g j)).Opens)
    (hE : ∀ j (A : (T j).Etale)
      (m : A ⟶ (MorphismProperty.Over.pullback @Etale ⊤ (g j)).obj V),
      Set.range m.left ⊆ (E j : Set (pullback V.hom (g j) : Scheme.{u})) ↔
        ((Scheme.etaleSetPullback (g j)).obj F).obj.map m.op
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ (g j)) (Type (u + 1))
            (S.smallGrothendieckTopology @Etale)
            ((T j).smallGrothendieckTopology @Etale)).unit.app F).hom.app (op V) t) =
        ((Scheme.etaleSetPullback (g j)).obj F).obj.map
          (m ≫ MorphismProperty.Over.homMk
            (pullback.snd V.hom (g j)) (Category.comp_id _) :
            A ⟶ Scheme.Etale.mk (𝟙 (T j))).op (s j)) :
    ∀ j k,
      (pullback.fst (pullback.fst V.hom (g j)) (pullback.fst V.hom (g k))) ⁻¹ᵁ E j =
        (pullback.snd (pullback.fst V.hom (g j)) (pullback.fst V.hom (g k))) ⁻¹ᵁ E k := by
  classical
  let Q (j : I) := (MorphismProperty.Over.pullback @Etale ⊤ (g j)).obj V
  let G (j : I) := (Scheme.etaleSetPullback (g j)).obj F
  let x (j : I) := ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ (g j)) (Type (u + 1))
    (S.smallGrothendieckTopology @Etale)
    ((T j).smallGrothendieckTopology @Etale)).unit.app F).hom.app (op V) t
  let y (j : I) := (G j).obj.map
    (MorphismProperty.Over.homMk (pullback.snd V.hom (g j)) (Category.comp_id _) :
      Q j ⟶ Scheme.Etale.mk (𝟙 (T j))).op (s j)
  have htest (j : I) (A : (T j).Etale) (m : A ⟶ Q j) :
      Set.range m.left ⊆ (E j : Set (pullback V.hom (g j) : Scheme.{u})) ↔
        (G j).obj.map m.op (x j) = (G j).obj.map m.op (y j) := by
    simpa only [y, op_comp, Functor.map_comp, comp_apply] using hE j A m
  intro j k
  let D := pullback (pullback.fst V.hom (g j)) (pullback.fst V.hom (g k))
  let p : D ⟶ (Q j).left :=
    pullback.fst (pullback.fst V.hom (g j)) (pullback.fst V.hom (g k))
  let q : D ⟶ (Q k).left :=
    pullback.snd (pullback.fst V.hom (g j)) (pullback.fst V.hom (g k))
  have hall (Z : Scheme.{u}) (a : Z ⟶ D) :
      Set.range (a ≫ p) ⊆ (E j : Set (pullback V.hom (g j) : Scheme.{u})) ↔
        Set.range (a ≫ q) ⊆ (E k : Set (pullback V.hom (g k) : Scheme.{u})) :=
    (etaleSections_equal_open_arbitrary_criterion (T j) (G j) (Q j)
      (x j) (y j) (E j) (htest j) Z (a ≫ p)).trans
      ((etaleFpqcAgreementSections_overlap_eq_iff T g F s hcompat V t j k Z a).trans
        (etaleSections_equal_open_arbitrary_criterion (T k) (G k) (Q k)
          (x k) (y k) (E k) (htest k) Z (a ≫ q)).symm)
  change p ⁻¹ᵁ E j = q ⁻¹ᵁ E k
  apply le_antisymm
  · let U := p ⁻¹ᵁ E j
    have hU : Set.range (U.ι ≫ p) ⊆ (E j : Set (pullback V.hom (g j) : Scheme.{u})) := by
      rintro z ⟨w, rfl⟩
      exact w.property
    have hW := (hall U.toScheme U.ι).mp hU
    intro z hz
    exact hW ⟨⟨z, hz⟩, rfl⟩
  · let U := q ⁻¹ᵁ E k
    have hU : Set.range (U.ι ≫ q) ⊆ (E k : Set (pullback V.hom (g k) : Scheme.{u})) := by
      rintro z ⟨w, rfl⟩
      exact w.property
    have hW := (hall U.toScheme U.ι).mpr hU
    intro z hz
    exact hW ⟨⟨z, hz⟩, rfl⟩

end AlgebraicGeometry
