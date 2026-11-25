/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardFunctor
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.CategoryTheory.Filtered.Final

/-!
# Ring charts of a base changed inverse system

Source: Stacks Project, Limits, Tags 01YZ and 01ZR (3).
(blueprint: lem-pc-affine-base-change-chart-colimit).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AffineBaseChangeChart

variable {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u})
  (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i)) (j : I) (hij : i ≤ j)
  (U : Xi.Opens)

/-- The stage over the original base. Source: Stacks, Tag 01YZ
(blueprint: lem-pc-affine-base-change-chart-colimit). -/
noncomputable def stage (k : {k : I // j ≤ k}) : Over (Spec (R.obj i)) :=
  Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property))))

/-- Transition over the original base. Source: Stacks, Tag 01YZ
(blueprint: lem-pc-affine-base-change-chart-colimit). -/
noncomputable def transition {k l : {k : I // j ≤ k}} (a : k ⟶ l) :
    stage R i j hij l ⟶ stage R i j hij k :=
  Over.homMk (Spec.map (R.map (homOfLE (leOfHom a))))
    (by dsimp [stage]; rw [← Spec.map_comp, ← R.map_comp]; rfl)

/-- The inverse image chart. Source: Stacks, Tag 01ZR (3)
(blueprint: lem-pc-affine-base-change-chart-colimit). -/
noncomputable def chart (k : {k : I // j ≤ k}) :
    (pullback f (stage R i j hij k).hom).Opens :=
  (pullback.fst f (stage R i j hij k).hom) ⁻¹ᵁ U

/-- Chart preimages agree under transition. Source: Stacks, Tag 01YZ
(blueprint: lem-pc-affine-base-change-chart-colimit). -/
theorem chart_le {k l : {k : I // j ≤ k}} (a : k ⟶ l) :
    chart R i f j hij U l ≤ baseChangeMap f (transition R i j hij a) ⁻¹ᵁ
      chart R i f j hij U k := by
  simp [chart, ← Scheme.Hom.comp_preimage, baseChangeMap]

/-- The diagram of section rings on the charts. Source: Stacks, Tag 01ZR (3)
(blueprint: lem-pc-affine-base-change-chart-colimit). -/
noncomputable def rings : {k : I // j ≤ k} ⥤ CommRingCat.{u} where
  obj k := Γ(pullback f (stage R i j hij k).hom, chart R i f j hij U k)
  map a := (baseChangeMap f (transition R i j hij a)).appLE _ _
    (chart_le R i f j hij U a)
  map_id k := by
    have ht : transition R i j hij (𝟙 k) = 𝟙 _ := by
      ext
      change Spec.map (R.map (homOfLE (le_refl k.val))) = 𝟙 _
      simp
    simp only [ht, baseChangeMap_id]
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app,
      Category.id_comp, homOfLE_refl, op_id]
    exact (pullback f (stage R i j hij k).hom).presheaf.map_id _
  map_comp {k l m} a b := by
    have ht : transition R i j hij (a ≫ b) =
        transition R i j hij b ≫ transition R i j hij a := by
      ext
      change Spec.map (R.map (homOfLE _)) =
        Spec.map (R.map (homOfLE _)) ≫ Spec.map (R.map (homOfLE _))
      rw [← Spec.map_comp, ← R.map_comp]
      rfl
    rw [Scheme.Hom.appLE_comp_appLE]
    congr 1
    exact (congrArg (baseChangeMap f) ht).trans (baseChangeMap_comp f _ _)

variable (c : Cone (R.op ⋙ Scheme.Spec))

/-- Limit-to-stage transition. Source: Stacks, Tag 01YZ
(blueprint: lem-pc-affine-base-change-chart-colimit). -/
noncomputable def projection (k : {k : I // j ≤ k}) :
    Over.mk (c.π.app (op i)) ⟶ stage R i j hij k :=
  Over.homMk (c.π.app (op k.val)) (c.w (homOfLE (hij.trans k.property)).op)

/-- The chart on the limit. Source: Stacks, Tag 01ZR (3)
(blueprint: lem-pc-affine-base-change-chart-colimit). -/
noncomputable def limitChart : (pullback f (c.π.app (op i))).Opens :=
  (pullback.fst f (c.π.app (op i))) ⁻¹ᵁ U

/-- Chart preimages agree under projection. Source: Stacks, Tag 01YZ
(blueprint: lem-pc-affine-base-change-chart-colimit). -/
theorem limitChart_le (k : {k : I // j ≤ k}) :
    limitChart R i f U c ≤ baseChangeMap f (projection R i j hij c k) ⁻¹ᵁ
      chart R i f j hij U k := by
  simp [limitChart, chart, ← Scheme.Hom.comp_preimage, baseChangeMap]

/-- The cocone of actual chart section rings. Source: Stacks, Tag 01ZR (3)
(blueprint: lem-pc-affine-base-change-chart-colimit). -/
noncomputable def cocone : Cocone (rings R i f j hij U) where
  pt := Γ(pullback f (c.π.app (op i)), limitChart R i f U c)
  ι.app k := (baseChangeMap f (projection R i j hij c k)).appLE _ _
    (limitChart_le R i f j hij U c k)
  ι.naturality {k l} a := by
    dsimp only [Functor.const_obj_obj, Functor.const_obj_map, rings]
    rw [Category.comp_id]
    rw [Scheme.Hom.appLE_comp_appLE]
    congr 1
    rw [← baseChangeMap_comp]
    congr 1
    ext
    exact c.w (homOfLE (show k.val ≤ l.val from leOfHom a)).op

/-- The ring on the limit chart is the filtered colimit of the stage chart rings.
Source: Stacks Project, Limits, Tags 01YZ, 01YW, and 01ZR (3).
(blueprint: lem-pc-affine-base-change-chart-colimit).

Proof: Restrict to the nonempty directed upper tail of j, which is cofinal in I.
Base change the inverse spectrum diagram along f, and restrict each stage to the
inverse image of U. Base change and restriction preserve this cofiltered limit
(Tag 01YZ). The charts are affine because the maps to Xi are affine and U is
affine. The affine Spec/Gamma equivalence converts this limit into a colimit of
rings. Its structure maps are precisely appLE along the base-change maps, by the
naturality of the chart restrictions. This also applies to empty affine charts. -/
theorem isColimit_cocone [IsDirected I (· ≤ ·)]
    (hc : IsLimit c) [IsAffine c.pt] (hU : IsAffineOpen U) :
    Nonempty (IsColimit (cocone R i f j hij U c)) := by
  classical
  let J := {k : I // j ≤ k}
  let : Nonempty J := ⟨⟨j, le_rfl⟩⟩
  let : IsDirected J (· ≤ ·) := ⟨fun a b ↦ by
    obtain ⟨k, ha, hb⟩ := exists_ge_ge a.val b.val
    exact ⟨⟨k, a.property.trans ha⟩, ha, hb⟩⟩
  let : IsConnected Jᵒᵖ := IsCofiltered.isConnected _
  let E : Jᵒᵖ ⥤ Iᵒᵖ := (Subtype.mono_coe (fun k : I ↦ j ≤ k)).functor.op
  let : E.Initial := Functor.initial_of_exists_of_isCofiltered E
    (fun k ↦ by
      obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j k.unop
      exact ⟨op ⟨l, hjl⟩, ⟨(homOfLE hkl).op⟩⟩)
    (fun {_} {k} a b ↦ ⟨k, 𝟙 _, Subsingleton.elim _ _⟩)
  let Z := E ⋙ (R.op ⋙ Scheme.Spec)
  let z : Cone Z := c.whisker E
  have hz : IsLimit z := (Functor.Initial.isLimitWhiskerEquiv E c).symm hc
  let D : Jᵒᵖ ⥤ Scheme.{u} :=
    { obj := fun k ↦ pullback f (stage R i j hij k.unop).hom
      map := fun a ↦ baseChangeMap f (transition R i j hij a.unop)
      map_id := by
        intro k
        have ht : transition R i j hij (𝟙 k.unop) = 𝟙 _ := by
          ext
          change Spec.map (R.map (homOfLE (le_refl k.unop.val))) = 𝟙 _
          simp
        simpa only [unop_id, ht] using baseChangeMap_id f (stage R i j hij k.unop)
      map_comp := by
        intro k l m a b
        rw [← baseChangeMap_comp]
        congr 1
        ext
        change Spec.map (R.map (homOfLE _)) =
          Spec.map (R.map (homOfLE _)) ≫ Spec.map (R.map (homOfLE _))
        rw [← Spec.map_comp, ← R.map_comp]
        rfl }
  let P : Cone D :=
    { pt := pullback f (c.π.app (op i))
      π :=
        { app := fun k ↦ baseChangeMap f (projection R i j hij c k.unop)
          naturality := by
            intro k l a
            dsimp [D]
            rw [Category.id_comp, ← baseChangeMap_comp]
            congr 1
            ext
            exact (c.w (homOfLE
              (show l.unop.val ≤ k.unop.val from leOfHom a.unop)).op).symm } }
  let α : D ⟶ Z :=
    { app := fun k ↦ pullback.snd f (stage R i j hij k.unop).hom
      naturality := by
        intro k l a
        simp [D, Z, E, baseChangeMap, transition]
        congr 2 }
  have hP : IsLimit P := isLimitOfIsPullbackOfIsConnected α P z
    { hom := pullback.snd f (c.π.app (op i))
      w := fun k ↦ by simp [P, α, z, baseChangeMap, Z, E, projection] }
    (fun k ↦ isPullback_baseChangeMap f (projection R i j hij c k.unop)) hz
  let QD : Jᵒᵖ ⥤ Scheme.{u} :=
    { obj := fun k ↦ (chart R i f j hij U k.unop).toScheme
      map := fun a ↦ (D.map a).resLE _ _ (chart_le R i f j hij U a.unop)
      map_id := by
        intro k
        apply (cancel_mono (chart R i f j hij U k.unop).ι).mp
        simp only [Scheme.Hom.resLE_comp_ι, Category.id_comp]
        rw [D.map_id, Category.comp_id]
      map_comp := by
        intro k l m a b
        apply (cancel_mono (chart R i f j hij U m.unop).ι).mp
        simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
        rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, ← D.map_comp] }
  let Q : Cone QD :=
    { pt := (limitChart R i f U c).toScheme
      π :=
        { app := fun k ↦ (P.π.app k).resLE _ _ (limitChart_le R i f j hij U c k.unop)
          naturality := by
            intro k l a
            apply (cancel_mono (chart R i f j hij U l.unop).ι).mp
            dsimp only [Functor.const_obj_map, QD]
            simp only [Category.assoc, Scheme.Hom.resLE_comp_ι,
              Scheme.Hom.resLE_comp_ι_assoc]
            exact (congrArg (fun g ↦ (limitChart R i f U c).ι ≫ g) (P.w a)).symm } }
  let β : QD ⟶ D :=
    { app := fun k ↦ (chart R i f j hij U k.unop).ι
      naturality := by intro k l a; exact Scheme.Hom.resLE_comp_ι _ _ }
  have hQ : IsLimit Q := isLimitOfIsPullbackOfIsConnected β Q P
    { hom := (limitChart R i f U c).ι
      w := fun k ↦ (Scheme.Hom.resLE_comp_ι _ _).symm }
    (fun k ↦ IsOpenImmersion.isPullback _ _ _ _
      (Scheme.Hom.resLE_comp_ι _ _).symm (by
        dsimp [P, β]
        simp only [Scheme.Opens.opensRange_ι]
        simp [limitChart, chart, ← Scheme.Hom.comp_preimage, baseChangeMap])) hP
  let : ∀ k : Jᵒᵖ, IsAffine (QD.obj k) := fun k ↦ by
    let : IsAffineHom (stage R i j hij k.unop).hom :=
      @isAffineHom_of_isAffine (Spec (R.obj k.unop.val)) (Spec (R.obj i))
        (stage R i j hij k.unop).hom inferInstance inferInstance
    let : IsAffineHom (pullback.fst f (stage R i j hij k.unop).hom) :=
      MorphismProperty.pullback_fst _ _ inferInstance
    exact hU.preimage (pullback.fst f (stage R i j hij k.unop).hom)
  let : ∀ {k l : Jᵒᵖ} (a : k ⟶ l), IsAffineHom (QD.map a) := fun a ↦
    @isAffineHom_of_isAffine _ _ (QD.map a) inferInstance inferInstance
  obtain ⟨hC⟩ := nonempty_isColimit_Γ_mapCocone QD Q hQ
  let T := (opOpEquivalence J).inverse
  let C := (Scheme.Γ.mapCocone Q.op).whisker T
  have hC' : IsColimit C :=
    (Functor.Final.isColimitWhiskerEquiv T (Scheme.Γ.mapCocone Q.op)).symm hC
  let e : rings R i f j hij U ≅ T ⋙ QD.op ⋙ Scheme.Γ :=
    NatIso.ofComponents (fun k ↦ (chart R i f j hij U k).topIso.symm) (by
      intro k l a
      change (baseChangeMap f (transition R i j hij a)).appLE _ _ _ ≫
        (chart R i f j hij U l).topIso.inv =
          (chart R i f j hij U k).topIso.inv ≫
            ((baseChangeMap f (transition R i j hij a)).resLE _ _ _).appTop
      rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
      simp only [Iso.inv_hom_id_assoc])
  let b : cocone R i f j hij U c ≅ (Cocone.precompose e.hom).obj C :=
    Cocone.ext (limitChart R i f U c).topIso.symm (fun k ↦ by
      change (baseChangeMap f (projection R i j hij c k)).appLE _ _ _ ≫
        (limitChart R i f U c).topIso.inv =
          (chart R i f j hij U k).topIso.inv ≫
            ((baseChangeMap f (projection R i j hij c k)).resLE _ _ _).appTop
      rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
      simp only [Iso.inv_hom_id_assoc])
  exact ⟨((IsColimit.precomposeHomEquiv e C).symm hC').ofIsoColimit b.symm⟩

end AffineBaseChangeChart
end AlgebraicGeometry
