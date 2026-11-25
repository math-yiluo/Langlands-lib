/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.DescendClosedImmersion
import Mathlib.CategoryTheory.Filtered.Final

/-!
# Descent of a fixed Chow diagram

Source: Stacks Project, Limits, Tag 081F, the base-changed Chow diagram and Tag 01ZP.
(blueprint: lem-weil-pbc-closed-chow-stage).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

private theorem over_natIso_property
    {S S' : Scheme.{u}} (F G : Over S ⥤ Over S') (e : F ≅ G)
    {X Y : Over S} (f : X ⟶ Y) (P : MorphismProperty Scheme.{u}) [P.RespectsIso] :
    P (F.map f).left ↔ P (G.map f).left := by
  let ex := (Over.forget S').mapIso (e.app X)
  let ey := (Over.forget S').mapIso (e.app Y)
  apply P.arrow_mk_iso_iff
  exact Arrow.isoMk ex ey (congrArg (fun k ↦ k.left) (e.hom.naturality f).symm)

/-- A given Chow immersion at a separated stage is closed at a later stage.
The source at that later stage is the base change of the given Chow modification,
not an arbitrary witness for properness of the original morphism.

Source: Stacks Project, Limits, Tag 081F, proof after choosing the Chow diagram;
Tag 01ZP for descent of the closed immersion.
(blueprint: lem-weil-pbc-closed-chow-stage).

Proof:
1. Restrict the directed system to indices above i₁. This subsystem has the same limit:
   every index has a common upper bound with i₁, so compatible cones extend uniquely.
   Affine transitions make its base at i₁ and the base-changed X₀ and Y₀ qcqs.
   Pasting pullback squares identifies the pullback of f₁ to the limit with that of f₀.
2. Base change the given π₁ and j₁ to the limit. The former remains proper and surjective,
   and the latter remains an immersion. The composite π ≫ f is proper by composition.
   Projective space is proper, hence separated, over the limit target. The commutative
   triangle therefore makes j proper (properness over a separated target), and a proper
   immersion is a closed immersion.
3. At i₁, T₁ is qcqs because it is proper over the qcqs source. Projective space is qcqs
   because it is proper over the qcqs target. The immersion j₁ is locally of finite type.
   Apply exists_isClosedImmersion_stage_of_locallyOfFiniteType to j₁ over Sᵢ₁ and the
   restricted system. It yields an index i above i₁ with jᵢ a closed immersion.
4. The pullback of T₁ over Sᵢ₁ is the source displayed below. Pasting squares and the
   projective-space base-change isomorphism give π and j with the displayed triangle.
   Surjectivity of π follows from base change and transport by the source comparison
   isomorphism. Separatedness of fᵢ follows from that of f₁ by the same comparison.
   The transition Sᵢ → Sᵢ₀ is Sᵢ → Sᵢ₁ → Sᵢ₀ by functoriality. -/
theorem exists_closed_chow_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    (X₀ Y₀ : Over (D.obj (op i₀)))
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    (f₀ : X₀ ⟶ Y₀) [LocallyOfFiniteType f₀.left]
    (hf : IsProper (((Over.pullback (c.π.app (op i₀))).map f₀).left))
    (i₁ : I) (h₁ : i₀ ≤ i₁)
    (hsep : IsSeparated (((Over.pullback (D.map (homOfLE h₁).op)).map f₀).left))
    (n : ℕ) (T₁ : Scheme.{u})
    (π₁ : T₁ ⟶ ((Over.pullback (D.map (homOfLE h₁).op)).obj X₀).left)
    (j₁ : T₁ ⟶ ProjectiveSpace (ULift.{u} (Fin (n + 1)))
      ((Over.pullback (D.map (homOfLE h₁).op)).obj Y₀).left)
    (hπ₁ : IsProper π₁) (hsurj₁ : Surjective π₁) (hj₁ : IsImmersion j₁)
    (hw₁ : j₁ ≫ ProjectiveSpace (ULift.{u} (Fin (n + 1)))
      ((Over.pullback (D.map (homOfLE h₁).op)).obj Y₀).left ↘
        ((Over.pullback (D.map (homOfLE h₁).op)).obj Y₀).left =
      π₁ ≫ ((Over.pullback (D.map (homOfLE h₁).op)).map f₀).left) :
    ∃ (i : I) (h₁i : i₁ ≤ i)
      (π : pullback (π₁ ≫ ((Over.pullback (D.map (homOfLE h₁).op)).obj X₀).hom)
          (D.map (homOfLE h₁i).op) ⟶
        ((Over.pullback (D.map (homOfLE (h₁.trans h₁i)).op)).obj X₀).left)
      (j : pullback (π₁ ≫ ((Over.pullback (D.map (homOfLE h₁).op)).obj X₀).hom)
          (D.map (homOfLE h₁i).op) ⟶
        ProjectiveSpace (ULift.{u} (Fin (n + 1)))
          ((Over.pullback (D.map (homOfLE (h₁.trans h₁i)).op)).obj Y₀).left),
      Surjective π ∧ IsClosedImmersion j ∧
        j ≫ ProjectiveSpace (ULift.{u} (Fin (n + 1)))
          ((Over.pullback (D.map (homOfLE (h₁.trans h₁i)).op)).obj Y₀).left ↘
            ((Over.pullback (D.map (homOfLE (h₁.trans h₁i)).op)).obj Y₀).left =
          π ≫ ((Over.pullback (D.map (homOfLE (h₁.trans h₁i)).op)).map f₀).left ∧
        IsSeparated (((Over.pullback (D.map (homOfLE (h₁.trans h₁i)).op)).map f₀).left) := by
  let B := Over.pullback (D.map (homOfLE h₁).op)
  let X₁ := B.obj X₀
  let Y₁ := B.obj Y₀
  let f₁ := B.map f₀
  let T : Over (D.obj (op i₁)) := Over.mk (π₁ ≫ X₁.hom)
  let Q : Over (D.obj (op i₁)) :=
    Over.mk (ProjectiveSpace (ULift.{u} (Fin (n + 1))) Y₁.left ↘ Y₁.left ≫ Y₁.hom)
  let p : T ⟶ X₁ := Over.homMk π₁
  let q : Q ⟶ Y₁ := Over.homMk
    (ProjectiveSpace (ULift.{u} (Fin (n + 1))) Y₁.left ↘ Y₁.left)
  let j : T ⟶ Q := Over.homMk j₁ (by
    change j₁ ≫ _ ≫ Y₁.hom = π₁ ≫ X₁.hom
    rw [← Category.assoc, hw₁, Category.assoc]
    exact congrArg (π₁ ≫ ·) f₁.w)
  have hjq : j ≫ q = p ≫ f₁ := by
    ext
    exact hw₁
  let L := Over.pullback (c.π.app (op i₁))
  have hcomp : c.π.app (op i₁) ≫ D.map (homOfLE h₁).op = c.π.app (op i₀) := by
    exact c.w (homOfLE h₁).op
  have hfL : IsProper (L.map f₁).left := by
    have hF : IsProper (((Over.pullback
        (c.π.app (op i₁) ≫ D.map (homOfLE h₁).op)).map f₀).left) := by
      rw [hcomp]
      exact hf
    exact (over_natIso_property _ _
      (Over.pullbackComp (c.π.app (op i₁)) (D.map (homOfLE h₁).op))
      f₀ (@IsProper)).mp hF
  have hpL : IsProper (L.map p).left :=
    MorphismProperty.overPullbackMap _ p hπ₁
  have hqL : IsSeparated (L.map q).left :=
    MorphismProperty.overPullbackMap _ q (inferInstanceAs (IsSeparated
      (ProjectiveSpace (ULift.{u} (Fin (n + 1))) Y₁.left ↘ Y₁.left)))
  have hjL : IsImmersion (L.map j).left :=
    MorphismProperty.overPullbackMap _ j hj₁
  have : IsProper ((L.map j).left ≫ (L.map q).left) := by
    have : IsProper ((L.map p).left ≫ (L.map f₁).left) := by
      let := hpL
      let := hfL
      infer_instance
    simpa only [← Over.comp_left, ← Functor.map_comp, hjq] using this
  have : IsProper (L.map j).left := by
    let := hqL
    exact IsProper.of_comp _ (L.map q).left
  have hjclosed : IsClosedImmersion (L.map j).left := by
    let := hjL
    exact IsClosedImmersion.of_isPreimmersion _
      (Scheme.Hom.isClosedMap (L.map j).left).isClosed_range
  have : CompactSpace (D.obj (op i₁)) :=
    QuasiCompact.compactSpace_of_compactSpace (D.map (homOfLE h₁).op)
  have : QuasiSeparatedSpace (D.obj (op i₁)) :=
    quasiSeparatedSpace_of_quasiSeparated (D.map (homOfLE h₁).op)
  have : CompactSpace X₁.left := by
    dsimp [X₁, B, Over.pullback]
    infer_instance
  have : QuasiSeparatedSpace X₁.left := by
    dsimp [X₁, B, Over.pullback]
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst _ _)
  have : CompactSpace Y₁.left := by
    dsimp [Y₁, B, Over.pullback]
    infer_instance
  have : QuasiSeparatedSpace Y₁.left := by
    dsimp [Y₁, B, Over.pullback]
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst _ _)
  have : CompactSpace T.left := by
    let := hπ₁
    exact QuasiCompact.compactSpace_of_compactSpace π₁
  have : QuasiSeparatedSpace T.left := by
    let := hπ₁
    exact quasiSeparatedSpace_of_quasiSeparated π₁
  have : CompactSpace Q.left :=
    QuasiCompact.compactSpace_of_compactSpace
      (ProjectiveSpace (ULift.{u} (Fin (n + 1))) Y₁.left ↘ Y₁.left)
  have : QuasiSeparatedSpace Q.left := by
    dsimp [Q]
    exact quasiSeparatedSpace_of_quasiSeparated
      (ProjectiveSpace (ULift.{u} (Fin (n + 1))) Y₁.left ↘ Y₁.left)
  have : LocallyOfFiniteType j.left := by
    let := hj₁
    exact inferInstanceAs (LocallyOfFiniteType j₁)
  let J := {i : I // i₁ ≤ i}
  have : IsDirected J (· ≤ ·) := ⟨by
    intro a b
    obtain ⟨k, ha, hb⟩ := exists_ge_ge a.val b.val
    exact ⟨⟨k, a.property.trans ha⟩, ha, hb⟩⟩
  let F : J ⥤ I := (Subtype.mono_coe _).functor
  have : F.Final := by
    apply (Subtype.mono_coe _).final_functor_iff.mpr
    intro i
    obtain ⟨k, hi, h₁k⟩ := exists_ge_ge i i₁
    exact ⟨⟨k, h₁k⟩, hi⟩
  let D' := F.op ⋙ D
  have : ∀ {i j : Jᵒᵖ} (t : i ⟶ j), IsAffineHom (D'.map t) :=
    fun t ↦ inferInstanceAs (IsAffineHom (D.map (F.op.map t)))
  let c' := c.whisker F.op
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv F.op c).symm hc
  let k₁ : J := ⟨i₁, le_rfl⟩
  have : CompactSpace (D'.obj (op k₁)) :=
    inferInstanceAs (CompactSpace (D.obj (op i₁)))
  have : QuasiSeparatedSpace (D'.obj (op k₁)) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj (op i₁)))
  have hlimit : IsClosedImmersion
      (((Over.pullback (c'.π.app (op k₁))).map j).left) := hjclosed
  obtain ⟨k, hk, hclosed⟩ :=
    exists_isClosedImmersion_stage_of_locallyOfFiniteType D' c' hc' k₁ T Q j hlimit
  have hclosed' : IsClosedImmersion
      (((Over.pullback (D.map (homOfLE k.property).op))).map j).left := hclosed
  let g := D.map (homOfLE k.property).op
  let C := Over.pullback g
  let Bi := Over.pullback (D.map (homOfLE (h₁.trans k.property)).op)
  have hg : g ≫ D.map (homOfLE h₁).op =
      D.map (homOfLE (h₁.trans k.property)).op := by
    rw [← D.map_comp]
    rfl
  let e : Bi ≅ B ⋙ C := by
    dsimp [Bi, B, C]
    rw [← hg]
    exact Over.pullbackComp g (D.map (homOfLE h₁).op)
  let ex : (Bi.obj X₀).left ≅ (C.obj X₁).left :=
    (Over.forget (D.obj (op k.val))).mapIso (e.app X₀)
  let ey : (Bi.obj Y₀).left ≅ (C.obj Y₁).left :=
    (Over.forget (D.obj (op k.val))).mapIso (e.app Y₀)
  let Yi := (Bi.obj Y₀).left
  let π := (C.map p).left ≫ ex.inv
  have hsurjC : Surjective (C.map p).left :=
    MorphismProperty.overPullbackMap _ p hsurj₁
  have hsurjπ : Surjective π := by
    let := hsurjC
    dsimp [π]
    infer_instance
  have hsepC : IsSeparated (C.map f₁).left :=
    MorphismProperty.overPullbackMap _ f₁ hsep
  have hsepi : IsSeparated (Bi.map f₀).left :=
    (over_natIso_property _ _ e f₀ (@IsSeparated)).mpr hsepC
  let v : Yi ⟶ Y₁.left := ey.hom ≫ pullback.fst Y₁.hom g
  let sYi : Yi ⟶ D.obj (op k.val) := ey.hom ≫ pullback.snd Y₁.hom g
  have hY : IsPullback v sYi Y₁.hom g := by
    exact (IsPullback.of_hasPullback Y₁.hom g).of_iso'
      ey (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [v]) (by simp [sYi]) (by simp) (by simp)
  have hQ := (ProjectiveSpace.isPullback_map (ULift.{u} (Fin (n + 1))) v).paste_vert hY
  let eQ := hQ.isoPullback
  have hq : eQ.hom ≫ (C.map q).left =
      (ProjectiveSpace (ULift.{u} (Fin (n + 1))) Yi ↘ Yi) ≫ ey.hom := by
    apply pullback.hom_ext
    · simp only [C, Over.pullback_map_left, Category.assoc, pullback.lift_fst]
      change hQ.isoPullback.hom ≫
        (pullback.fst
          ((ProjectiveSpace (ULift.{u} (Fin (n + 1))) Y₁.left ↘ Y₁.left) ≫ Y₁.hom) g) ≫
          (ProjectiveSpace (ULift.{u} (Fin (n + 1))) Y₁.left ↘ Y₁.left) =
        (ProjectiveSpace (ULift.{u} (Fin (n + 1))) Yi ↘ Yi) ≫ v
      rw [← Category.assoc, hQ.isoPullback_hom_fst]
      exact ProjectiveSpace.map_over (ULift.{u} (Fin (n + 1))) v
    · simp only [C, Over.pullback_map_left, Category.assoc, pullback.lift_snd]
      exact hQ.isoPullback_hom_snd
  let jᵢ := (C.map j).left ≫ eQ.inv
  have hjᵢ : IsClosedImmersion jᵢ := by
    have : IsClosedImmersion (C.map j).left := hclosed'
    dsimp [jᵢ]
    infer_instance
  have hqinv : eQ.inv ≫
      (ProjectiveSpace (ULift.{u} (Fin (n + 1))) Yi ↘ Yi) =
      (C.map q).left ≫ ey.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hq]
    simp
  have heinv : ex.inv ≫ (Bi.map f₀).left = (C.map f₁).left ≫ ey.inv := by
    exact (congrArg (fun z ↦ z.left) (e.inv.naturality f₀)).symm
  refine ⟨k.val, k.property, π, jᵢ, hsurjπ, hjᵢ, ?_, hsepi⟩
  change (C.map j).left ≫ eQ.inv ≫
    (ProjectiveSpace (ULift.{u} (Fin (n + 1))) Yi ↘ Yi) =
    ((C.map p).left ≫ ex.inv) ≫ (Bi.map f₀).left
  rw [hqinv, ← Category.assoc, ← Over.comp_left,
    ← Functor.map_comp, hjq, Functor.map_comp, Over.comp_left, Category.assoc, ← heinv]
  exact (Category.assoc _ _ _).symm

end AlgebraicGeometry
