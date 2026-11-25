/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
import WeilConjectures.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Descent of a comparison between two existing finite etale models

## References

* Stacks Project, Tag 0BQ5, comparison descent in its proof
* Stacks Project, Tag 0BQ5, the last paragraph of the proof, using
  the morphism and equality parts of Tag 01ZM
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private noncomputable def finiteEtaleCompIso {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (P : Z.FiniteEtale) :
    (FiniteEtale.pullback (f ≫ g)).obj P ≅
      (FiniteEtale.pullback f).obj ((FiniteEtale.pullback g).obj P) :=
  ObjectProperty.isoMk _ (MorphismProperty.Over.isoMk
    (pullbackLeftPullbackSndIso P.obj.hom g f).symm (by simp))

private noncomputable def comparisonMap {A B T : Scheme.{u}} (p : T ⟶ B)
    (a : A ⟶ B) {L : Scheme.{u}} (q : L ⟶ B) (w : L ⟶ A) (hw : w ≫ a = q) :
    pullback p q ⟶ pullback p a :=
  pullback.map p q p a (𝟙 T) w (𝟙 B) (by simp) (by simp [hw])

private theorem comparisonMap_square {A B T : Scheme.{u}} (p : T ⟶ B)
    (a : A ⟶ B) {L : Scheme.{u}} (q : L ⟶ B) (w : L ⟶ A) (hw : w ≫ a = q) :
    IsPullback (comparisonMap p a q w hw) (pullback.snd p q) (pullback.snd p a) w :=
  isPullback_pullback_map p q a w hw

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem finiteEtale_stageIso {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (d : Cone D) (hd : IsLimit d)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    {A B : Scheme.{u}} (a : D ⟶ (Functor.const I).obj A)
    (b : D ⟶ (Functor.const I).obj B) (aL : d.pt ⟶ A) (bL : d.pt ⟶ B)
    (ha : ∀ i, d.π.app i ≫ a.app i = aL) (hb : ∀ i, d.π.app i ≫ b.app i = bL)
    (P : A.FiniteEtale) (Q : B.FiniteEtale)
    (e : (FiniteEtale.pullback aL).obj P ≅ (FiniteEtale.pullback bL).obj Q) :
    ∃ i, Nonempty ((FiniteEtale.pullback (a.app i)).obj P ≅
      (FiniteEtale.pullback (b.app i)).obj Q) := by
  classical
  let PL := (FiniteEtale.pullback aL).obj P
  let QL := (FiniteEtale.pullback bL).obj Q
  let ei : PL.obj.left ≅ QL.obj.left :=
    { hom := e.hom.hom.left
      inv := e.inv.hom.left
      hom_inv_id := by
        have h := congrArg (fun z : PL ⟶ PL ↦ z.hom.left) e.hom_inv_id
        exact h
      inv_hom_id := by
        have h := congrArg (fun z : QL ⟶ QL ↦ z.hom.left) e.inv_hom_id
        exact h }
  have he : ei.hom ≫ QL.obj.hom = PL.obj.hom := FiniteEtale.hom_left_comp e.hom
  let hP (i : I) := comparisonMap P.obj.hom (a.app i) aL (d.π.app i) (ha i)
  let hQ (i : I) := comparisonMap Q.obj.hom (b.app i) bL (d.π.app i) (hb i)
  have HP (i : I) : IsPullback (hP i) PL.obj.hom
      ((FiniteEtale.pullback (a.app i)).obj P).obj.hom (d.π.app i) :=
    comparisonMap_square ..
  have HQ (i : I) : IsPullback (ei.hom ≫ hQ i) PL.obj.hom
      ((FiniteEtale.pullback (b.app i)).obj Q).obj.hom (d.π.app i) := by
    exact (comparisonMap_square Q.obj.hom (b.app i) bL (d.π.app i) (hb i)).of_iso'
      ei (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [hQ]) (by exact he)
      (by simp) (by simp)
  obtain ⟨k⟩ := IsCofiltered.nonempty (C := I)
  let Pk := (FiniteEtale.pullback (a.app k)).obj P
  let Qk := (FiniteEtale.pullback (b.app k)).obj Q
  have : Etale Pk.obj.hom := Pk.obj.prop
  have : IsFinite Pk.obj.hom := Pk.property
  have : Etale Qk.obj.hom := Qk.obj.prop
  have : IsFinite Qk.obj.hom := Qk.property
  have : CompactSpace Pk.obj.left :=
    QuasiCompact.compactSpace_of_compactSpace
      (show Pk.obj.left ⟶ D.obj k from Pk.obj.hom)
  have : QuasiSeparatedSpace Pk.obj.left :=
    quasiSeparatedSpace_of_quasiSeparated
      (show Pk.obj.left ⟶ D.obj k from Pk.obj.hom)
  have : CompactSpace Qk.obj.left :=
    QuasiCompact.compactSpace_of_compactSpace
      (show Qk.obj.left ⟶ D.obj k from Qk.obj.hom)
  have : QuasiSeparatedSpace Qk.obj.left :=
    quasiSeparatedSpace_of_quasiSeparated
      (show Qk.obj.left ⟶ D.obj k from Qk.obj.hom)
  have : CompactSpace ↥(Limits.pullback P.obj.hom (a.app k)) := ‹CompactSpace Pk.obj.left›
  have : QuasiSeparatedSpace ↥(Limits.pullback P.obj.hom (a.app k)) :=
    ‹QuasiSeparatedSpace Pk.obj.left›
  have : CompactSpace ↥(Limits.pullback Q.obj.hom (b.app k)) := ‹CompactSpace Qk.obj.left›
  have : QuasiSeparatedSpace ↥(Limits.pullback Q.obj.hom (b.app k)) :=
    ‹QuasiSeparatedSpace Qk.obj.left›
  obtain ⟨j, f, hj⟩ := exists_iso_of_isPullback hd (HP k) (HQ k)
  let Pj := (FiniteEtale.pullback (a.app j)).obj P
  let Qj := (FiniteEtale.pullback (b.app j)).obj Q
  have haf : D.map f ≫ a.app k = a.app j :=
    (a.naturality f).trans (Category.comp_id _)
  have hbf : D.map f ≫ b.app k = b.app j :=
    (b.naturality f).trans (Category.comp_id _)
  let qP := comparisonMap P.obj.hom (a.app k) (a.app j) (D.map f) haf
  let qQ := comparisonMap Q.obj.hom (b.app k) (b.app j) (D.map f) hbf
  have hPP : hP j ≫ qP = hP k := by
    apply pullback.hom_ext
    · simp [hP, qP, comparisonMap, Category.assoc]
    · simp only [hP, qP, comparisonMap, Category.assoc, pullback.map,
        pullback.lift_snd, pullback.lift_snd_assoc]
      exact congrArg (pullback.snd P.obj.hom aL ≫ ·) (d.w f)
  have hQQ : (ei.hom ≫ hQ j) ≫ qQ = ei.hom ≫ hQ k := by
    rw [Category.assoc]
    apply congrArg (ei.hom ≫ ·)
    apply pullback.hom_ext
    · simp [hQ, qQ, comparisonMap, Category.assoc]
    · simp only [hQ, qQ, comparisonMap, Category.assoc, pullback.map,
        pullback.lift_snd, pullback.lift_snd_assoc]
      exact congrArg (pullback.snd Q.obj.hom bL ≫ ·) (d.w f)
  obtain ⟨t, ht, _⟩ := hj
    (comparisonMap_square P.obj.hom (a.app k) (a.app j) (D.map f) haf) hPP
    (by simp [hP, comparisonMap, PL])
    (comparisonMap_square Q.obj.hom (b.app k) (b.app j) (D.map f) hbf) hQQ
    (by
      change (ei.hom ≫ hQ j) ≫ pullback.snd Q.obj.hom (b.app j) =
        PL.obj.hom ≫ d.π.app j
      simp only [hQ, comparisonMap, Category.assoc, pullback.map, pullback.lift_snd]
      rw [← Category.assoc]
      exact congrArg (· ≫ d.π.app j) he)
  exact ⟨j, ⟨ObjectProperty.isoMk _ (MorphismProperty.Over.isoMk t ht)⟩⟩

private abbrev AffineNhds (S : Scheme.{u}) (s : S) :=
  {V : S.Opens // IsAffineOpen V ∧ s ∈ V}

private abbrev AffineNhdsWithin (S : Scheme.{u}) (s : S) (W : S.Opens) :=
  {V : AffineNhds S s // V.1 ≤ W}

private noncomputable def nhdsDiagram (S : Scheme.{u}) (s : S) : AffineNhds S s ⥤ Scheme.{u} :=
  (show Monotone (fun V : AffineNhds S s ↦ V.1) from fun _ _ h ↦ h).functor ⋙
    S.restrictFunctor ⋙ Over.forget S

private noncomputable def nhdsCone (S : Scheme.{u}) (s : S) : Cone (nhdsDiagram S s) where
  pt := Spec (S.presheaf.stalk s)
  π.app V := V.1.fromSpecStalkOfMem s V.2.2
  π.naturality V T f := by
    apply (cancel_mono T.1.ι).mp
    simp [nhdsDiagram]

private theorem nhdsCone_limit (S : Scheme.{u}) (s : S) :
    Nonempty (IsLimit (nhdsCone S s)) := by
  classical
  obtain ⟨_, _, _, _, _, _, _, _, _, h⟩ := S.fromSpecStalk_limit_affine_neighbourhoods s
  have hx (t : Cone (nhdsDiagram S s)) : ∃! g : t.pt ⟶ Spec (S.presheaf.stalk s),
      ∀ V : AffineNhds S s, g ≫ V.1.fromSpecStalkOfMem s V.2.2 = t.π.app V := by
    apply h t.pt (fun V ↦ t.π.app V)
    intro V T hTV
    exact t.w (homOfLE hTV)
  exact ⟨{
    lift := fun t ↦ (hx t).choose
    fac := fun t V ↦ (hx t).choose_spec.1 V
    uniq := fun t g hg ↦ (hx t).choose_spec.2 g hg }⟩

private def withinInclusion (S : Scheme.{u}) (s : S) (W : S.Opens) :
    AffineNhdsWithin S s W ⥤ AffineNhds S s :=
  (show Monotone (fun V : AffineNhdsWithin S s W ↦ V.1) from fun _ _ h ↦ h).functor

private theorem within_cofiltered (S : Scheme.{u}) (s : S) (W : S.Opens) (hsW : s ∈ W) :
    IsCofiltered (AffineNhdsWithin S s W) := by
  have : Nonempty (AffineNhdsWithin S s W) := by
    obtain ⟨V, hV, hsV, hVW⟩ := exists_isAffineOpen_mem_and_subset hsW
    exact ⟨⟨⟨V, hV, hsV⟩, hVW⟩⟩
  have : IsDirected (AffineNhdsWithin S s W) (· ≥ ·) := ⟨fun V T ↦ by
    obtain ⟨Z, hZ, hsZ, hZVT⟩ :=
      exists_isAffineOpen_mem_and_subset (show s ∈ V.1.1 ⊓ T.1.1 from ⟨V.1.2.2, T.1.2.2⟩)
    exact ⟨⟨⟨Z, hZ, hsZ⟩, (hZVT.trans inf_le_left).trans V.2⟩,
      hZVT.trans inf_le_left, hZVT.trans inf_le_right⟩⟩
  infer_instance

private theorem within_initial (S : Scheme.{u}) (s : S) (W : S.Opens) (hsW : s ∈ W) :
    (withinInclusion S s W).Initial := by
  have := within_cofiltered S s W hsW
  exact Functor.initial_of_exists_of_isCofiltered _
    (fun V ↦ by
      obtain ⟨T, hT, hsT, hTVW⟩ :=
        exists_isAffineOpen_mem_and_subset (show s ∈ V.1 ⊓ W from ⟨V.2.2, hsW⟩)
      exact ⟨⟨⟨T, hT, hsT⟩, hTVW.trans inf_le_right⟩,
        ⟨homOfLE (hTVW.trans inf_le_left)⟩⟩)
    (fun {V T} f g ↦ ⟨T, 𝟙 T, Subsingleton.elim _ _⟩)

private noncomputable def overlapDiagram {S C : Scheme.{u}} (c : C ⟶ S)
    (U W : S.Opens) (s : S) : AffineNhdsWithin S s W ⥤ Scheme.{u} :=
  (show Monotone (fun V : AffineNhdsWithin S s W ↦ (c ⁻¹ᵁ U) ⊓ (c ⁻¹ᵁ V.1.1)) from
    fun _ _ h ↦ inf_le_inf_left _ (c.preimage_mono h)).functor ⋙
    C.restrictFunctor ⋙ Over.forget C

private noncomputable def overlapLeft {S C : Scheme.{u}} (c : C ⟶ S)
    (U W : S.Opens) (s : S) :
    overlapDiagram c U W s ⟶ (Functor.const _).obj (c ⁻¹ᵁ U).toScheme where
  app _ := C.homOfLE inf_le_left
  naturality V T f := by simp [overlapDiagram]

private noncomputable def overlapRight {S C : Scheme.{u}} (c : C ⟶ S)
    (U W : S.Opens) (s : S) :
    overlapDiagram c U W s ⟶ (Functor.const _).obj (c ⁻¹ᵁ W).toScheme where
  app V := C.homOfLE inf_le_right ≫ C.homOfLE (c.preimage_mono V.2)
  naturality V T f := by simp [overlapDiagram]

private noncomputable def localToOpen {S C : Scheme.{u}} (c : C ⟶ S)
    (s : S) (V : S.Opens) (hsV : s ∈ V) :
    Limits.pullback c (S.fromSpecStalk s) ⟶ (c ⁻¹ᵁ V).toScheme :=
  (isPullback_morphismRestrict c V).flip.lift (pullback.fst c (S.fromSpecStalk s))
    (pullback.snd c (S.fromSpecStalk s) ≫ V.fromSpecStalkOfMem s hsV)
    (by simp [pullback.condition])

private theorem localToOpen_ι {S C : Scheme.{u}} (c : C ⟶ S)
    (s : S) (V : S.Opens) (hsV : s ∈ V) :
    localToOpen c s V hsV ≫ (c ⁻¹ᵁ V).ι = pullback.fst c (S.fromSpecStalk s) :=
  IsPullback.lift_fst ..

private noncomputable def overlapProjection {S C : Scheme.{u}} (c : C ⟶ S)
    (U : S.Opens) (s : S) (V : AffineNhds S s) :
    Limits.pullback (c ⁻¹ᵁ U).ι (pullback.fst c (S.fromSpecStalk s)) ⟶
      ((c ⁻¹ᵁ U) ⊓ (c ⁻¹ᵁ V.1)).toScheme :=
  (isPullback_opens_inf (c ⁻¹ᵁ U) (c ⁻¹ᵁ V.1)).lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ localToOpen c s V.1 V.2.2)
    (by rw [Category.assoc, localToOpen_ι]; exact pullback.condition)

private theorem overlapProjection_left {S C : Scheme.{u}} (c : C ⟶ S)
    (U : S.Opens) (s : S) (V : AffineNhds S s) :
    overlapProjection c U s V ≫ C.homOfLE inf_le_left =
      pullback.fst (c ⁻¹ᵁ U).ι (pullback.fst c (S.fromSpecStalk s)) :=
  IsPullback.lift_fst ..

private theorem overlapProjection_right {S C : Scheme.{u}} (c : C ⟶ S)
    (U : S.Opens) (s : S) (V : AffineNhds S s) :
    overlapProjection c U s V ≫ C.homOfLE inf_le_right =
      pullback.snd (c ⁻¹ᵁ U).ι (pullback.fst c (S.fromSpecStalk s)) ≫
        localToOpen c s V.1 V.2.2 :=
  IsPullback.lift_snd ..

private noncomputable def overlapCone {S C : Scheme.{u}} (c : C ⟶ S)
    (U W : S.Opens) (s : S) : Cone (overlapDiagram c U W s) where
  pt := Limits.pullback (c ⁻¹ᵁ U).ι (pullback.fst c (S.fromSpecStalk s))
  π.app V := overlapProjection c U s V.1
  π.naturality V T f := by
    apply (cancel_mono (C.homOfLE (inf_le_left :
      (c ⁻¹ᵁ U) ⊓ (c ⁻¹ᵁ T.1.1) ≤ c ⁻¹ᵁ U))).mp
    simp [overlapDiagram, overlapProjection_left]

private theorem overlapCone_left {S C : Scheme.{u}} (c : C ⟶ S)
    (U W : S.Opens) (s : S) (V : AffineNhdsWithin S s W) :
    (overlapCone c U W s).π.app V ≫ (overlapLeft c U W s).app V =
      pullback.fst (c ⁻¹ᵁ U).ι (pullback.fst c (S.fromSpecStalk s)) :=
  overlapProjection_left ..

private theorem overlapCone_right {S C : Scheme.{u}} (c : C ⟶ S)
    (U W : S.Opens) (s : S)
    (l : Limits.pullback c (S.fromSpecStalk s) ⟶ (c ⁻¹ᵁ W).toScheme)
    (hl : l ≫ (c ⁻¹ᵁ W).ι = pullback.fst c (S.fromSpecStalk s))
    (V : AffineNhdsWithin S s W) :
    (overlapCone c U W s).π.app V ≫ (overlapRight c U W s).app V =
      pullback.snd (c ⁻¹ᵁ U).ι (pullback.fst c (S.fromSpecStalk s)) ≫ l := by
  apply (cancel_mono (c ⁻¹ᵁ W).ι).mp
  simp only [overlapCone, overlapRight, Category.assoc, homOfLE_ι, hl]
  change overlapProjection c U s V.1 ≫ ((c ⁻¹ᵁ U) ⊓ (c ⁻¹ᵁ V.1.1)).ι = _
  rw [← homOfLE_ι C (inf_le_left : (c ⁻¹ᵁ U) ⊓ (c ⁻¹ᵁ V.1.1) ≤ c ⁻¹ᵁ U),
    ← Category.assoc, overlapProjection_left]
  exact pullback.condition

private noncomputable def overlapToNhds {S C : Scheme.{u}} (c : C ⟶ S)
    (U W : S.Opens) (s : S) :
    overlapDiagram c U W s ⟶ withinInclusion S s W ⋙ nhdsDiagram S s where
  app V := C.homOfLE inf_le_right ≫ c ∣_ V.1.1
  naturality V T f := by
    apply (cancel_mono T.1.1.ι).mp
    simp [overlapDiagram, withinInclusion, nhdsDiagram, Category.assoc]

private theorem overlap_stage_square {S C : Scheme.{u}} (c : C ⟶ S)
    (U W : S.Opens) (s : S) (V : AffineNhdsWithin S s W) :
    IsPullback ((overlapLeft c U W s).app V) ((overlapToNhds c U W s).app V)
      ((c ⁻¹ᵁ U).ι ≫ c) V.1.1.ι :=
  (isPullback_opens_inf (c ⁻¹ᵁ U) (c ⁻¹ᵁ V.1.1)).paste_vert
    (isPullback_morphismRestrict c V.1.1).flip

private theorem overlapProjection_toNhds {S C : Scheme.{u}} (c : C ⟶ S)
    (U W : S.Opens) (s : S) (V : AffineNhdsWithin S s W) :
    (overlapCone c U W s).π.app V ≫ (overlapToNhds c U W s).app V =
      (pullback.snd (c ⁻¹ᵁ U).ι (pullback.fst c (S.fromSpecStalk s)) ≫
        pullback.snd c (S.fromSpecStalk s)) ≫ V.1.1.fromSpecStalkOfMem s V.1.2.2 := by
  change overlapProjection c U s V.1 ≫ (C.homOfLE inf_le_right ≫ c ∣_ V.1.1) = _
  rw [← Category.assoc, overlapProjection_right, Category.assoc]
  simp only [localToOpen, IsPullback.lift_snd, Category.assoc]

private theorem overlapCone_limit {S C : Scheme.{u}} (c : C ⟶ S)
    (U W : S.Opens) (s : S) (hsW : s ∈ W) :
    Nonempty (IsLimit (overlapCone c U W s)) := by
  have := within_cofiltered S s W hsW
  have := within_initial S s W hsW
  have : CategoryTheory.IsConnected (AffineNhdsWithin S s W) := IsCofiltered.isConnected _
  obtain ⟨h⟩ := nhdsCone_limit S s
  let hG := (Functor.Initial.isLimitWhiskerEquiv (withinInclusion S s W) _).symm h
  let g := pullback.snd (c ⁻¹ᵁ U).ι (pullback.fst c (S.fromSpecStalk s)) ≫
    pullback.snd c (S.fromSpecStalk s)
  refine ⟨isLimitOfIsPullbackOfIsConnected (overlapToNhds c U W s)
    (overlapCone c U W s) ((nhdsCone S s).whisker (withinInclusion S s W))
    { hom := g, w := fun V ↦ (overlapProjection_toNhds c U W s V).symm } ?_ hG⟩
  intro V
  have H := (IsPullback.of_hasPullback (c ⁻¹ᵁ U).ι
    (pullback.fst c (S.fromSpecStalk s))).paste_vert
      (IsPullback.of_hasPullback c (S.fromSpecStalk s))
  change IsPullback _ g ((c ⁻¹ᵁ U).ι ≫ c) (S.fromSpecStalk s) at H
  rw [← overlapCone_left c U W s V] at H
  conv at H =>
    enter [4]
    rw [← V.1.1.fromSpecStalkOfMem_ι s V.1.2.2]
  exact H.of_right (overlapProjection_toNhds c U W s V) (overlap_stage_square c U W s V)

private theorem overlap_transition_affine {S C : Scheme.{u}} (c : C ⟶ S)
    (U W : S.Opens) (s : S) {V T : AffineNhdsWithin S s W} (f : V ⟶ T) :
    IsAffineHom ((overlapDiagram c U W s).map f) := by
  have : IsAffine V.1.1.toScheme := V.1.2.1
  have : IsAffine T.1.1.toScheme := T.1.2.1
  have H := overlap_stage_square c U W s V
  have hleft : (overlapDiagram c U W s).map f ≫ (overlapLeft c U W s).app T =
      (overlapLeft c U W s).app V := by simp [overlapDiagram, overlapLeft]
  rw [← hleft, ← homOfLE_ι S (leOfHom f)] at H
  have H' := H.of_right ((overlapToNhds c U W s).naturality f)
    (overlap_stage_square c U W s T)
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) H'.flip
    (@isAffineHom_of_isAffine _ _ _ V.1.2.1 T.1.2.1)

/-- Two existing models with a comparison on the local overlap become isomorphic
on an open overlap after shrinking the second neighbourhood. -/
theorem FiniteEtale.exists_neighbourhood_comparison_of_stalk {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S]
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [LocallyOfFinitePresentation c]
    (U W : S.Opens) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale) (s : S) (hsW : s ∈ W)
    (R : (c ⁻¹ᵁ W).toScheme.FiniteEtale)
    (l : Limits.pullback c (S.fromSpecStalk s) ⟶ (c ⁻¹ᵁ W).toScheme)
    (hl : l ≫ (c ⁻¹ᵁ W).ι = pullback.fst c (S.fromSpecStalk s))
    (e : Nonempty ((FiniteEtale.pullback
      (pullback.fst (c ⁻¹ᵁ U).ι (pullback.fst c (S.fromSpecStalk s)))).obj PA ≅
      (FiniteEtale.pullback
      (pullback.snd (c ⁻¹ᵁ U).ι (pullback.fst c (S.fromSpecStalk s)))).obj
        ((FiniteEtale.pullback l).obj R))) :
    ∃ (V : S.Opens) (hVW : V ≤ W), s ∈ V ∧
      Nonempty ((FiniteEtale.pullback
        (C.homOfLE (inf_le_left : (c ⁻¹ᵁ U) ⊓ (c ⁻¹ᵁ V) ≤ c ⁻¹ᵁ U))).obj PA ≅
        (FiniteEtale.pullback
        (C.homOfLE (inf_le_right : (c ⁻¹ᵁ U) ⊓ (c ⁻¹ᵁ V) ≤ c ⁻¹ᵁ V))).obj
          ((FiniteEtale.pullback (C.homOfLE (c.preimage_mono hVW))).obj R)) := by
  classical
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian c
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  have : IsNoetherian C := ⟨⟩
  have := within_cofiltered S s W hsW
  let D := overlapDiagram c U W s
  let d := overlapCone c U W s
  have : ∀ {i j : AffineNhdsWithin S s W} (f : i ⟶ j), IsAffineHom (D.map f) :=
    fun f ↦ overlap_transition_affine c U W s f
  have : ∀ V : AffineNhdsWithin S s W, CompactSpace (D.obj V) := by
    intro V
    change CompactSpace ((c ⁻¹ᵁ U) ⊓ (c ⁻¹ᵁ V.1.1)).toScheme
    exact (isCompact_iff_compactSpace).mp (TopologicalSpace.NoetherianSpace.isCompact _)
  have : ∀ V : AffineNhdsWithin S s W, QuasiSeparatedSpace (D.obj V) := by
    intro V
    change QuasiSeparatedSpace ((c ⁻¹ᵁ U) ⊓ (c ⁻¹ᵁ V.1.1)).toScheme
    infer_instance
  obtain ⟨hd⟩ := overlapCone_limit c U W s hsW
  obtain ⟨e⟩ := e
  let r := pullback.snd (c ⁻¹ᵁ U).ι (pullback.fst c (S.fromSpecStalk s))
  let E := e ≪≫ (finiteEtaleCompIso r l R).symm
  obtain ⟨V, ⟨t⟩⟩ := finiteEtale_stageIso D d hd (overlapLeft c U W s)
    (overlapRight c U W s) (pullback.fst _ _) (r ≫ l)
    (overlapCone_left c U W s) (overlapCone_right c U W s l hl) PA R E
  exact ⟨V.1.1, V.2, V.1.2.2,
    ⟨t ≪≫ finiteEtaleCompIso (C.homOfLE inf_le_right)
      (C.homOfLE (c.preimage_mono V.2)) R⟩⟩

end AlgebraicGeometry.Scheme
