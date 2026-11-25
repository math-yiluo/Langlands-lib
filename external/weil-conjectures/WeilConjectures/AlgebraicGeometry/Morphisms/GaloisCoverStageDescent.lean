/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
import Mathlib.CategoryTheory.Presentable.Directed
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.DescendFinite
import WeilConjectures.AlgebraicGeometry.DescendSurjective
import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Descent of an unpointed finite Galois torsor

## References

* Stacks Project, Tags 0BTV and 01ZM, used in the last paragraph of Tag 0EZJ
* Stacks Project, Tag 01ZM, parts (2) and (3), and Tag 0BTV, the equivalence of finite étale
  categories
* Stacks Project, Tag 0EZJ, final paragraph
* Tag 0EZJ, final paragraph
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

-- Assemble Tags 01ZM, 01ZO, and 07RP for a finite étale morphism.
-- The pullback bookkeeping follows the proved helper in FiniteEtaleAlgebraStage.
private theorem exists_finiteEtaleSurjective_limit_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    {X : Scheme.{u}} (g : X ⟶ c.pt) [IsFinite g] [Etale g] [Surjective g] :
    ∃ (i : I) (W : Scheme.{u}) (p : W ⟶ D.obj (Opposite.op i))
      (_ : IsFinite p) (_ : Etale p) (_ : Surjective p) (h : X ⟶ W),
      IsPullback h g p (c.π.app (Opposite.op i)) := by
  classical
  have prop_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
      {X S T : Scheme.{u}} (p : X ⟶ S) (q : T ⟶ S) :
      P (pullback.snd p q) ↔
        P (((Over.pullback q).map (Over.homMk p (by simp) :
          Over.mk p ⟶ Over.mk (𝟙 S))).left) := by
    have he : (((Over.pullback q).map (Over.homMk p (by simp) :
        Over.mk p ⟶ Over.mk (𝟙 S))).left) ≫ pullback.snd (𝟙 S) q =
        pullback.snd p q := by simp
    rw [← he, P.cancel_right_of_respectsIso]
  have prop_mono (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
      {X S T T' : Scheme.{u}} (p : X ⟶ S) (q : T ⟶ S) (q' : T' ⟶ S)
      (r : T' ⟶ T) (hr : r ≫ q = q') (hp : P (pullback.snd p q)) :
      P (pullback.snd p q') := by
    exact P.of_isPullback (isPullback_pullback_map p q' q r hr) hp
  obtain ⟨i, W, p, hp, hqc, hqs, h, H⟩ :=
    exists_isPullback_of_finitePresentation (D := D) (c := c) hc g
  have := hp
  have := hqc
  have := hqs
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace W := quasiSeparatedSpace_of_quasiSeparated p
  have : CompactSpace (Over.mk p).left := inferInstanceAs (CompactSpace W)
  have : QuasiSeparatedSpace (Over.mk p).left :=
    inferInstanceAs (QuasiSeparatedSpace W)
  have : CompactSpace (Over.mk (𝟙 (D.obj i))).left :=
    inferInstanceAs (CompactSpace (D.obj i))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  let φ : Over.mk p ⟶ Over.mk (𝟙 (D.obj i)) := Over.homMk p (by simp)
  have : LocallyOfFinitePresentation φ.left := hp
  have hf : IsFinite (pullback.snd p (c.π.app i)) := by
    rw [← H.isoPullback_inv_snd]
    infer_instance
  have he : Etale (pullback.snd p (c.π.app i)) := by
    rw [← H.isoPullback_inv_snd]
    infer_instance
  obtain ⟨j, hj, hfin⟩ := exists_isFinite_baseChange_stage D c hc i.unop
    (Over.mk p) (Over.mk (𝟙 (D.obj i))) φ
    ((prop_iff @IsFinite p (c.π.app i)).mp hf)
  obtain ⟨k, hk, het⟩ := Etale.exists_stage_of_inverseLimit D c hc i.unop
    (Over.mk p) (Over.mk (𝟙 (D.obj i))) φ
    ((prop_iff @Etale p (c.π.app i)).mp he)
  have hs : Surjective (pullback.snd p (c.π.app i)) := by
    rw [← H.isoPullback_inv_snd]
    infer_instance
  obtain ⟨l, hl, hsurj⟩ := exists_surjective_of_isLimit D c hc i.unop
    (Over.mk p) (Over.mk (𝟙 (D.obj i))) φ
    ((prop_iff @Surjective p (c.π.app i)).mp hs)
  obtain ⟨r₀, hjr₀, hkr₀⟩ := exists_ge_ge j k
  obtain ⟨r, hr₀r, hlr⟩ := exists_ge_ge r₀ l
  have hjr := hjr₀.trans hr₀r
  have hkr := hkr₀.trans hr₀r
  let a : Opposite.op r ⟶ i := (homOfLE (hj.trans hjr)).op
  let q := D.map a
  have hfin' : IsFinite (pullback.snd p q) := by
    apply prop_mono @IsFinite p (D.map (homOfLE hj).op) q
      (D.map (homOfLE hjr).op)
    · dsimp [q]
      rw [← D.map_comp]
      congr 1
    · exact (prop_iff @IsFinite p _).mpr hfin
  have het' : Etale (pullback.snd p q) := by
    apply prop_mono @Etale p (D.map (homOfLE hk).op) q
      (D.map (homOfLE hkr).op)
    · dsimp [q]
      rw [← D.map_comp]
      congr 1
    · exact (prop_iff @Etale p _).mpr het
  have hsurj' : Surjective (pullback.snd p q) := by
    apply prop_mono @Surjective p (D.map (homOfLE hl).op) q
      (D.map (homOfLE hlr).op)
    · dsimp [q]
      rw [← D.map_comp]
      congr 1
    · exact (prop_iff @Surjective p _).mpr hsurj
  let t : X ⟶ pullback p q := pullback.lift h (g ≫
    c.π.app (Opposite.op r))
    (by change h ≫ p = (g ≫ c.π.app (Opposite.op r)) ≫ D.map a
        rw [Category.assoc, c.w a]; exact H.w)
  have H' : IsPullback t g (pullback.snd p q) (c.π.app (Opposite.op r)) := by
    apply IsPullback.of_right (h₁₂ := pullback.fst p q) (h₂₂ := q)
    · convert H using 1
      · simp [t]
      · exact c.w a
    · simp [t]
    · exact IsPullback.of_hasPullback p q
  exact ⟨r, pullback p q, pullback.snd p q, hfin',
    het', hsurj', t, H'⟩


-- Descend all action maps before asking for the finite equations and comparison.
private theorem exists_action_maps_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (G : Type (u + 1)) [Group G] [Finite G] (Z : GaloisCover G c.pt)
    (i : I) {P : Scheme.{u}} (p : P ⟶ D.obj (Opposite.op i))
    [IsFinite p] [Etale p]
    (χ : Z.P ⟶ P) (H : IsPullback χ Z.π p (c.π.app (Opposite.op i))) :
    ∃ (j : I) (hij : i ≤ j),
      let q := D.map (homOfLE hij).op
      ∃ (s : G → (pullback p q ⟶ pullback p q)),
        (∀ g, s g ≫ pullback.snd p q = pullback.snd p q) ∧
        ∀ g, Z.smul g ≫ isPullbackLift D c (homOfLE hij).op H =
          isPullbackLift D c (homOfLE hij).op H ≫ s g := by
  classical
  let ψ (g : G) : pullback p (c.π.app (Opposite.op i)) ⟶ P :=
    H.isoPullback.inv ≫ Z.smul g ≫ χ
  have hψ (g : G) : ψ g ≫ p =
      pullback.fst p (c.π.app (Opposite.op i)) ≫ p := by
    dsimp [ψ]
    rw [Category.assoc, Category.assoc, H.w, ← Category.assoc (Z.smul g), Z.smul_π,
      H.isoPullback_inv_snd_assoc, pullback.condition]
  have hdesc (g : G) := exists_pullback_hom_of_isLimit hc p p (ψ g) (hψ g)
  choose k f t ht heq using hdesc
  obtain ⟨j₀, hj₀⟩ := (Set.finite_range (fun g ↦ (k g).unop)).bddAbove
  obtain ⟨j, hij, hj₀j⟩ := exists_ge_ge i j₀
  have hj (g : G) : (k g).unop ≤ j :=
    (hj₀ (Set.mem_range_self g)).trans hj₀j
  let a := (homOfLE hij).op
  let q := D.map a
  let r (g : G) : pullback p q ⟶ pullback p (D.map (f g)) :=
    pullback.map p q p (D.map (f g)) (𝟙 P) (D.map (homOfLE (hj g)).op)
      (𝟙 _) (by simp) (by
        simp only [Category.comp_id]
        rw [← D.map_comp]
        congr 1)
  have hr (g : G) : (r g ≫ t g) ≫ p = pullback.snd p q ≫ q := by
    rw [Category.assoc, ht g, ← Category.assoc]
    have hrf : r g ≫ pullback.fst p (D.map (f g)) = pullback.fst p q := by
      simp [r, pullback.map]
    rw [hrf, pullback.condition]
  let s (g : G) : pullback p q ⟶ pullback p q :=
    pullback.lift (r g ≫ t g) (pullback.snd p q) (hr g)
  refine ⟨j, hij, s, (fun g ↦ pullback.lift_snd ..), ?_⟩
  intro g
  let b := pullback.map p (c.π.app (Opposite.op i)) p (D.map (f g))
    (𝟙 P) (c.π.app (k g)) (𝟙 _) (by simp) (by simp)
  have hχr : isPullbackLift D c a H ≫ r g = H.isoPullback.hom ≫ b := by
    apply pullback.hom_ext
    · simp [r, b, q, a, pullback.map]
    · simp only [Category.assoc, r, b, pullback.map, pullback.lift_snd,
        H.isoPullback_hom_snd_assoc]
      have hsnd : isPullbackLift D c a H ≫ pullback.snd p q =
          Z.π ≫ c.π.app (Opposite.op j) := isPullbackLift_snd a H
      rw [← Category.assoc, hsnd, Category.assoc, c.w (homOfLE (hj g)).op]
  apply pullback.hom_ext
  · change (Z.smul g ≫ isPullbackLift D c a H) ≫ pullback.fst p q =
      (isPullbackLift D c a H ≫ s g) ≫ pullback.fst p q
    simp only [Category.assoc, s, pullback.lift_fst]
    rw [show isPullbackLift D c a H ≫ pullback.fst p q = χ from
      isPullbackLift_fst a H]
    rw [← Category.assoc (isPullbackLift D c a H), hχr, Category.assoc]
    rw [heq g]
    simp [ψ]
  · dsimp [s, q, a]
    simp only [Category.assoc, pullback.lift_snd, isPullbackLift_snd]
    rw [← Category.assoc, Z.smul_π]

private theorem exists_action_laws_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (G : Type (u + 1)) [Group G] [Finite G] (Z : GaloisCover G c.pt)
    (i : I) {P : Scheme.{u}} (p : P ⟶ D.obj (Opposite.op i))
    [IsFinite p] [Etale p]
    (χ : Z.P ⟶ P) (H : IsPullback χ Z.π p (c.π.app (Opposite.op i)))
    (s : G → (P ⟶ P)) (hs : ∀ g, s g ≫ p = p)
    (hequiv : ∀ g, Z.smul g ≫ χ = χ ≫ s g) :
    ∃ (j : I) (hij : i ≤ j),
      let q := D.map (homOfLE hij).op
      let sj (g : G) :=
        pullback.map p q p q (s g) (𝟙 _) (𝟙 _) (by simp [hs]) (by simp)
      sj 1 = 𝟙 _ ∧ ∀ g h, sj (g * h) = sj h ≫ sj g := by
  classical
  have h1 : pullback.fst p (c.π.app (Opposite.op i)) ≫ s 1 =
      pullback.fst p (c.π.app (Opposite.op i)) ≫ 𝟙 P := by
    rw [← H.isoPullback_inv_fst_assoc, ← hequiv 1, Z.one_smul]
    simp
  have hmul (g h : G) : pullback.fst p (c.π.app (Opposite.op i)) ≫ s (g * h) =
      pullback.fst p (c.π.app (Opposite.op i)) ≫ (s h ≫ s g) := by
    rw [← H.isoPullback_inv_fst_assoc, ← hequiv (g * h), Z.mul_smul]
    simp only [Category.assoc]
    rw [hequiv g, ← Category.assoc (Z.smul h), hequiv h]
    simp only [Category.assoc, H.isoPullback_inv_fst_assoc]
  obtain ⟨k₁, f₁, heq₁⟩ := exists_pullback_fst_comp_eq_of_isLimit hc p p
    (s 1) (𝟙 P) (hs 1) (by simp) h1
  have hdesc (gh : G × G) := exists_pullback_fst_comp_eq_of_isLimit hc p p
    (s (gh.1 * gh.2)) (s gh.2 ≫ s gh.1) (hs _) (by simp [hs]) (hmul gh.1 gh.2)
  choose k f heq using hdesc
  obtain ⟨j₀, hj₀⟩ := (Set.finite_range (fun gh ↦ (k gh).unop)).bddAbove
  obtain ⟨j₁, hj₀j₁, hk₁j₁⟩ := exists_ge_ge j₀ k₁.unop
  obtain ⟨j, hij, hj₁j⟩ := exists_ge_ge i j₁
  have hj (gh : G × G) : (k gh).unop ≤ j :=
    (hj₀ (Set.mem_range_self gh)).trans (hj₀j₁.trans hj₁j)
  let a := (homOfLE hij).op
  let q := D.map a
  have lift_eq {k' : Iᵒᵖ} (f' : k' ⟶ Opposite.op i) (hk' : k'.unop ≤ j)
      (x y : P ⟶ P)
      (he : pullback.fst p (D.map f') ≫ x = pullback.fst p (D.map f') ≫ y) :
      pullback.fst p q ≫ x = pullback.fst p q ≫ y := by
    let r := pullback.map p q p (D.map f') (𝟙 P) (D.map (homOfLE hk').op)
      (𝟙 _) (by simp) (by
        simp only [Category.comp_id]
        rw [← D.map_comp]
        congr 1)
    have hr : r ≫ pullback.fst p (D.map f') = pullback.fst p q := by
      simp [r, pullback.map]
    simpa only [← Category.assoc, hr] using congrArg (r ≫ ·) he
  have he1 := lift_eq f₁ (hk₁j₁.trans hj₁j) (s 1) (𝟙 P) heq₁
  have hem (g h : G) := lift_eq (f (g, h)) (hj (g, h))
    (s (g * h)) (s h ≫ s g) (heq (g, h))
  refine ⟨j, hij, ?_, ?_⟩
  · apply pullback.hom_ext
    · simpa [pullback.map, Category.assoc] using he1
    · simp [pullback.map]
  · intro g h
    apply pullback.hom_ext
    · simpa [pullback.map, Category.assoc] using hem g h
    · simp [pullback.map]

set_option backward.defeqAttrib.useBackward true in
/-- Compare the finite model with the identity model of its limiting isomorphism. -/
private theorem exists_iso_snd
    (_h : True) {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (t : i ⟶ j), IsAffineHom (D.map t)]
    (c : Cone D) (hc : IsLimit c) (k : I)
    [CompactSpace (D.obj k)] [QuasiSeparatedSpace (D.obj k)]
    {Z X : Scheme.{u}} [CompactSpace Z] [QuasiSeparatedSpace Z]
    (q : Z ⟶ D.obj k) [LocallyOfFinitePresentation q]
    (w : X ⟶ c.pt) [IsIso w] (h : X ⟶ Z)
    (H : IsPullback h w q (c.π.app k)) :
    ∃ (j : I) (f : j ⟶ k), IsIso (pullback.snd q (D.map f)) := by
  have H₁ : IsPullback (inv w ≫ h) (𝟙 c.pt) q (c.π.app k) := by
    exact H.of_iso (asIso w) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  have H₂ : IsPullback (c.π.app k) (𝟙 c.pt) (𝟙 (D.obj k)) (c.π.app k) :=
    IsPullback.of_vert_isIso (snd := 𝟙 _) (f := 𝟙 _) ⟨by simp⟩
  obtain ⟨j, f, hj⟩ := exists_iso_of_isPullback hc H₁ H₂
  have H₁' : IsPullback (pullback.fst q (D.map f)) (pullback.snd q (D.map f))
      q (D.map f) := IsPullback.of_hasPullback _ _
  have H₂' : IsPullback (D.map f) (𝟙 (D.obj j)) (𝟙 (D.obj k)) (D.map f) :=
    IsPullback.of_vert_isIso (snd := 𝟙 _) (f := 𝟙 _) ⟨by simp⟩
  obtain ⟨e, he, _⟩ := hj H₁' (isPullbackLift_fst f H₁)
    (isPullbackLift_snd f H₁) H₂' (c.w f) (by simp)
  refine ⟨j, f, ?_⟩
  simpa using (he ▸ (inferInstance : IsIso e.hom))

set_option backward.defeqAttrib.useBackward true in
/-- Translate isomorphism descent into the morphism presentation in `Over`. -/
private theorem exists_iso_overPullback
    (_h : True) {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (t : i ⟶ j), IsAffineHom (D.map t)]
    (c : Cone D) (hc : IsLimit c) (k : I)
    {Z Y : Over (D.obj k)}
    [CompactSpace Z.left] [QuasiSeparatedSpace Z.left]
    [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]
    (γ : Z ⟶ Y) [LocallyOfFinitePresentation γ.left]
    (hS : IsIso ((Over.pullback (c.π.app k)).map γ).left) :
    ∃ (j : I) (a : j ⟶ k), IsIso ((Over.pullback (D.map a)).map γ).left := by
  have hw : γ.left ≫ Y.hom = Z.hom ≫ D.map (𝟙 k) := by
    rw [Over.w γ, D.map_id, Category.comp_id]
  have he : (𝟙 Y.left) ≫ Y.hom = Y.hom ≫ D.map (𝟙 k) := by
    rw [Category.id_comp, D.map_id, Category.comp_id]
  have : IsIso (D.map (𝟙 k)) := by rw [D.map_id]; infer_instance
  have hfst : IsIso (pullback.fst Y.hom (D.map (𝟙 k))) := inferInstance
  have hfl : pullback.fst Y.hom (D.map (𝟙 k)) ≫ pullback.lift (𝟙 Y.left) Y.hom he = 𝟙 _ := by
    apply pullback.hom_ext
    · simp
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp, pullback.condition, D.map_id,
        Category.comp_id]
  have he₀ : IsIso (pullback.lift (𝟙 Y.left) Y.hom he) := by
    rw [show pullback.lift (𝟙 Y.left) Y.hom he = inv (pullback.fst Y.hom (D.map (𝟙 k))) from
      IsIso.eq_inv_of_hom_inv_id hfl]
    infer_instance
  have hq₀ : pullback.lift γ.left Z.hom hw = γ.left ≫ pullback.lift (𝟙 Y.left) Y.hom he := by
    apply pullback.hom_ext <;> simp
  have : LocallyOfFinitePresentation (pullback.lift γ.left Z.hom hw) := by
    rw [hq₀]; infer_instance
  -- The base change of `γ` to the limit is the base change of the identity-stage model.
  have hsq : IsPullback (pullback.fst Z.hom (c.π.app k))
      ((Over.pullback (c.π.app k)).map γ).left (pullback.lift γ.left Z.hom hw)
      ((baseChangeCone D c Y.hom).π.app (Over.mk (𝟙 k))) := by
    refine IsPullback.of_bot ?_ ?_ (isPullback_baseChangeCone_π D c Y.hom (Over.mk (𝟙 k)))
    · refine (IsPullback.of_hasPullback Z.hom (c.π.app k)).of_iso
        (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
        (by simp [Over.pullback])
        (by simp) (by simp)
    · apply pullback.hom_ext <;>
        simp [Over.pullback,
          pullback.condition]
  have hI1 : @LocallyOfFinitePresentation Z.left
      ((baseChangeDiagram D Y.hom).obj (Over.mk (𝟙 k))) (pullback.lift γ.left Z.hom hw) :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.lift γ.left Z.hom hw))
  have hI4 : @IsIso Scheme.{u} _ (pullback Z.hom (c.π.app k)) (baseChangeCone D c Y.hom).pt
      ((Over.pullback (c.π.app k)).map γ).left := hS
  obtain ⟨j, a, ha⟩ := exists_iso_snd trivial (baseChangeDiagram D Y.hom)
    (baseChangeCone D c Y.hom) (isLimitBaseChangeCone D c Y.hom hc)
    (Over.mk (𝟙 k)) (pullback.lift γ.left Z.hom hw)
    ((Over.pullback (c.π.app k)).map γ).left (pullback.fst Z.hom (c.π.app k)) hsq
  refine ⟨j.left, j.hom, ?_⟩
  have hργ : IsPullback (pullback.fst Z.hom (D.map j.hom))
      ((Over.pullback (D.map j.hom)).map γ).left γ.left
      (pullback.fst Y.hom (D.map j.hom)) := by
    refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback Y.hom (D.map j.hom))
    · refine (IsPullback.of_hasPullback Z.hom (D.map j.hom)).of_iso
        (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
        (by simp [Over.pullback]) (by simp) (by simp)
    · simp [Over.pullback]
  have hsq3 : IsPullback (𝟙 Z.left) (pullback.lift γ.left Z.hom hw) γ.left
      (pullback.fst Y.hom (D.map (𝟙 k))) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, pullback.lift_fst]⟩
  have hρq : IsPullback
      (pullback.fst (pullback.lift γ.left Z.hom hw) ((baseChangeDiagram D Y.hom).map a))
      (pullback.snd (pullback.lift γ.left Z.hom hw) ((baseChangeDiagram D Y.hom).map a))
      γ.left (pullback.fst Y.hom (D.map j.hom)) := by
    have h1 := (IsPullback.of_hasPullback (pullback.lift γ.left Z.hom hw)
        ((baseChangeDiagram D Y.hom).map a)).paste_horiz hsq3
    refine h1.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) ?_
    simp
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme.{u})
    (Arrow.isoMk (hρq.isoIsPullback _ _ hργ) (Iso.refl _) (by simp))).mp ha

private theorem comparison_pullback_data
    {X Y P Q : Scheme.{u}} (G : Type (u + 1)) [Group G] [Finite G]
    (p : P ⟶ X) (q : Q ⟶ Y) (j : Y ⟶ X) (ψ : Q ⟶ P)
    (hψ : IsPullback ψ q p j)
    (s : G → (P ⟶ P)) (hs : ∀ g, s g ≫ p = p)
    (a : G → (Q ⟶ Q)) (ha : ∀ g, a g ≫ q = q)
    (hcompat : ∀ g, a g ≫ ψ = ψ ≫ s g) :
    let t := Sigma.desc fun g : G ↦
      pullback.lift (f := p) (g := p) (s g) (𝟙 P) (by simp [hs])
    let tη := Sigma.desc fun g : G ↦
      pullback.lift (f := q) (g := q) (a g) (𝟙 Q) (by simp [ha])
    let σ := Sigma.desc fun _ : G ↦ p
    let ση := Sigma.desc fun _ : G ↦ q
    let Ψ := Sigma.desc fun g : G ↦ ψ ≫ Sigma.ι (fun _ : G ↦ P) g
    let ρ := pullback.snd p p ≫ p
    let ρη := pullback.snd q q ≫ q
    let R := pullback.map q q p p ψ ψ j hψ.w.symm hψ.w.symm
    IsPullback Ψ ση σ j ∧ IsPullback R ρη ρ j ∧ Ψ ≫ t = tη ≫ R := by
  let t : (∐ fun _ : G ↦ P) ⟶ pullback p p := Sigma.desc fun g : G ↦
    pullback.lift (f := p) (g := p) (s g) (𝟙 P) (by simp [hs])
  let tη : (∐ fun _ : G ↦ Q) ⟶ pullback q q := Sigma.desc fun g : G ↦
    pullback.lift (f := q) (g := q) (a g) (𝟙 Q) (by simp [ha])
  let σ : (∐ fun _ : G ↦ P) ⟶ X := Sigma.desc fun _ : G ↦ p
  let ση : (∐ fun _ : G ↦ Q) ⟶ Y := Sigma.desc fun _ : G ↦ q
  let Ψ : (∐ fun _ : G ↦ Q) ⟶ (∐ fun _ : G ↦ P) :=
    Sigma.desc fun g : G ↦ ψ ≫ Sigma.ι (fun _ : G ↦ P) g
  let ρ : pullback p p ⟶ X := pullback.snd p p ≫ p
  let ρη : pullback q q ⟶ Y := pullback.snd q q ≫ q
  let R : pullback q q ⟶ pullback p p :=
    pullback.map q q p p ψ ψ j hψ.w.symm hψ.w.symm
  have hSigma : IsPullback Ψ ση σ j := by
    have hu := FinitaryPreExtensive.isUniversal_finiteCoproducts
      (coproductIsCoproduct (fun _ : G ↦ P))
    have hs := hu.isPullback_of_isColimit_left (fun _ : G ↦ p) σ j
      (fun _ : G ↦ q) (fun _ : G ↦ ψ) (fun _ : G ↦ hψ.flip)
      (coproductIsCoproduct (fun _ : G ↦ Q))
    simpa [Cofan.IsColimit.desc, coproductIsCoproduct, Ψ, ση, σ] using hs.flip
  have hR : IsPullback R ρη ρ j := by
    apply IsPullback.mk'
    · simp [R, ρη, ρ, Category.assoc, hψ.w]
    · intro T φ φ' h₁ h₂
      apply pullback.hom_ext
      · apply hψ.hom_ext
        · simpa [R] using congrArg (fun k ↦ k ≫ pullback.fst p p) h₁
        · simpa [ρη, ← pullback.condition] using h₂
      · apply hψ.hom_ext
        · simpa [R] using congrArg (fun k ↦ k ≫ pullback.snd p p) h₁
        · exact h₂
    · intro T f b hf
      have hf₂ : (f ≫ pullback.snd p p) ≫ p = b ≫ j := by
        simpa [ρ] using hf
      have hf₁ : (f ≫ pullback.fst p p) ≫ p = b ≫ j := by
        simpa [Category.assoc, pullback.condition] using hf₂
      let z₁ := hψ.lift (f ≫ pullback.fst p p) b hf₁
      let z₂ := hψ.lift (f ≫ pullback.snd p p) b hf₂
      have hz : z₁ ≫ q = z₂ ≫ q := by simp [z₁, z₂]
      refine ⟨pullback.lift z₁ z₂ hz, ?_, ?_⟩
      · apply pullback.hom_ext <;> simp [R, z₁, z₂]
      · simp [ρη, z₂]
  have hc : Ψ ≫ t = tη ≫ R := by
    apply Sigma.hom_ext
    intro g
    apply pullback.hom_ext
    · simp only [colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Cofan.mk_pt,
        Cofan.mk_ι_app, Category.assoc, colimit.ι_desc, limit.lift_π,
        PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_left, hcompat, Ψ, t, tη, R]
    · simp only [colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Cofan.mk_pt,
        Cofan.mk_ι_app, Category.assoc, colimit.ι_desc, limit.lift_π,
        PullbackCone.mk_π_app, Category.comp_id, limit.lift_π_assoc,
        cospan_right, Ψ, t, tη, R]
      change ψ = 𝟙 Q ≫ ψ
      simp
  exact ⟨hSigma, hR, hc⟩

private theorem comparison_isIso_iff
    {X Y P Q : Scheme.{u}} (G : Type (u + 1)) [Group G] [Finite G]
    (p : P ⟶ X) (q : Q ⟶ Y) (b : Y ⟶ X) (ψ : Q ⟶ P)
    (H : IsPullback ψ q p b)
    (s : G → (P ⟶ P)) (hs : ∀ g, s g ≫ p = p)
    (a : G → (Q ⟶ Q)) (ha : ∀ g, a g ≫ q = q)
    (hequiv : ∀ g, a g ≫ ψ = ψ ≫ s g) :
    let t := Sigma.desc fun g : G ↦
      pullback.lift (f := p) (g := p) (s g) (𝟙 P) (by simp [hs])
    let tη := Sigma.desc fun g : G ↦
      pullback.lift (f := q) (g := q) (a g) (𝟙 Q) (by simp [ha])
    let σ := Sigma.desc fun _ : G ↦ p
    let ρ := pullback.snd p p ≫ p
    let ht : t ≫ ρ = σ := by
      ext g
      simp only [colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Cofan.mk_pt,
        Cofan.mk_ι_app, limit.lift_π_assoc, cospan_right, PullbackCone.mk_π_app,
        colimit.ι_desc, t, ρ, σ]
      change 𝟙 P ≫ p = p
      simp
    let γ : Over.mk σ ⟶ Over.mk ρ := Over.homMk t ht
    IsIso ((Over.pullback b).map γ).left ↔ IsIso tη := by
  let t := Sigma.desc fun g : G ↦
    pullback.lift (f := p) (g := p) (s g) (𝟙 P) (by simp [hs])
  let tη := Sigma.desc fun g : G ↦
    pullback.lift (f := q) (g := q) (a g) (𝟙 Q) (by simp [ha])
  let σ := Sigma.desc fun _ : G ↦ p
  let ση := Sigma.desc fun _ : G ↦ q
  let ρ := pullback.snd p p ≫ p
  let ρη := pullback.snd q q ≫ q
  let Ψ := Sigma.desc fun g : G ↦ ψ ≫ Sigma.ι (fun _ : G ↦ P) g
  let R := pullback.map q q p p ψ ψ b H.w.symm H.w.symm
  have ht : t ≫ ρ = σ := by
      ext g
      simp only [colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Cofan.mk_pt,
        Cofan.mk_ι_app, limit.lift_π_assoc, cospan_right, PullbackCone.mk_π_app,
        colimit.ι_desc, t, ρ, σ]
      change 𝟙 P ≫ p = p
      simp
  let γ : Over.mk σ ⟶ Over.mk ρ := Over.homMk t ht
  obtain ⟨hSigma, hR, hc⟩ := comparison_pullback_data G p q b ψ H s hs a ha hequiv
  have hSf : hSigma.isoPullback.hom ≫ pullback.fst σ b = Ψ :=
    hSigma.isoPullback_hom_fst
  have hSs : hSigma.isoPullback.hom ≫ pullback.snd σ b = ση :=
    hSigma.isoPullback_hom_snd
  have hRf : hR.isoPullback.hom ≫ pullback.fst ρ b = R := hR.isoPullback_hom_fst
  have hRs : hR.isoPullback.hom ≫ pullback.snd ρ b = ρη := hR.isoPullback_hom_snd
  have hcomm : hSigma.isoPullback.hom ≫ ((Over.pullback b).map γ).left =
      tη ≫ hR.isoPullback.hom := by
    apply pullback.hom_ext
    · simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst]
      change hSigma.isoPullback.hom ≫ pullback.fst σ b ≫ t =
        tη ≫ hR.isoPullback.hom ≫ pullback.fst ρ b
      rw [← Category.assoc, hSf, hRf]
      exact hc
    · simp only [Category.assoc, Over.pullback_map_left, pullback.lift_snd]
      change hSigma.isoPullback.hom ≫ pullback.snd σ b =
        tη ≫ hR.isoPullback.hom ≫ pullback.snd ρ b
      rw [hSs, hRs]
      ext g
      simp only [colimit.ι_desc, colimit.ι_desc_assoc, Discrete.functor_obj_eq_as,
        Cofan.mk_pt, Cofan.mk_ι_app, limit.lift_π_assoc, cospan_right,
        PullbackCone.mk_π_app, tη, ρη, ση]
      change q = 𝟙 Q ≫ q
      simp
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme.{u})
    (Arrow.isoMk hSigma.isoPullback hR.isoPullback hcomm)).symm

/-- The comparison of a finite étale model with a genuine group action is invertible
at a later stage if its pullback is equivariantly a torsor. -/
private theorem GaloisCover.exists_comparison_stage_on_action_model
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (G : Type (u + 1)) [Group G] [Finite G] (Z : GaloisCover G c.pt)
    (i : I) {P : Scheme.{u}} (p : P ⟶ D.obj (Opposite.op i)) [IsFinite p] [Etale p]
    (χ : Z.P ⟶ P) (H : IsPullback χ Z.π p (c.π.app (Opposite.op i)))
    (s : G → (P ⟶ P)) (hs : ∀ g, s g ≫ p = p)
    (hequiv : ∀ g, Z.smul g ≫ χ = χ ≫ s g) :
    ∃ (j : I) (hij : i ≤ j),
      let q := D.map (homOfLE hij).op
      let Pj := pullback p q
      let pj := pullback.snd p q
      let sj (g : G) : Pj ⟶ Pj :=
        pullback.map p q p q (s g) (𝟙 _) (𝟙 _) (by simp [hs]) (by simp)
      IsIso (Sigma.desc fun g : G ↦
        pullback.lift (f := pj) (g := pj) (sj g) (𝟙 Pj)
          (by simp [sj, pj, pullback.map])) := by
  classical
  let t := Sigma.desc fun g : G ↦
    pullback.lift (f := p) (g := p) (s g) (𝟙 P) (by simp [hs])
  let σ := Sigma.desc fun _ : G ↦ p
  let ρ := pullback.snd p p ≫ p
  have ht : t ≫ ρ = σ := by
      ext g
      simp only [colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Cofan.mk_pt,
        Cofan.mk_ι_app, limit.lift_π_assoc, cospan_right, PullbackCone.mk_π_app,
        colimit.ι_desc, t, ρ, σ]
      change 𝟙 P ≫ p = p
      simp
  let γ : Over.mk σ ⟶ Over.mk ρ := Over.homMk t ht
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace P := quasiSeparatedSpace_of_quasiSeparated p
  obtain ⟨hqc, hqs, _⟩ := finite_coproduct_lfp_qcqs (fun _ : G ↦ P)
    (D.obj (Opposite.op i)) (fun _ ↦ p)
  have : CompactSpace (Over.mk σ).left := hqc (fun _ ↦ inferInstance)
  have : QuasiSeparatedSpace (Over.mk σ).left := hqs (fun _ ↦ inferInstance)
  have : CompactSpace (Over.mk ρ).left := inferInstanceAs (CompactSpace ↥(pullback p p))
  have : IsFinite ρ := by dsimp [ρ]; infer_instance
  have : QuasiSeparatedSpace (Over.mk ρ).left :=
    quasiSeparatedSpace_of_quasiSeparated ρ
  have hσ : Etale σ := IsZariskiLocalAtSource.sigmaDesc (P := @Etale)
    (fun _ ↦ inferInstance)
  have : Etale ρ := by dsimp [ρ]; infer_instance
  have : Etale (t ≫ ρ) := ht.symm ▸ hσ
  have : Etale t := Etale.of_comp t ρ
  have : LocallyOfFinitePresentation γ.left := inferInstanceAs (LocallyOfFinitePresentation t)
  have hlim : IsIso ((Over.pullback (c.π.app (Opposite.op i))).map γ).left :=
    (comparison_isIso_iff G p Z.π (c.π.app (Opposite.op i)) χ H s hs Z.smul
      Z.smul_π hequiv).mpr Z.isIso_sigmaDesc
  obtain ⟨j, f, hiso⟩ :=
    exists_iso_overPullback trivial D c hc (Opposite.op i) γ hlim
  have hij : i ≤ j.unop := leOfHom f.unop
  have hf : f = (homOfLE hij).op := Subsingleton.elim _ _
  rw [hf] at hiso
  let q := D.map (homOfLE hij).op
  let pj := pullback.snd p q
  let sj (g : G) := pullback.map p q p q (s g) (𝟙 _) (𝟙 _)
    (by simp [hs]) (by simp)
  have hsj (g : G) : sj g ≫ pj = pj := by simp [sj, pj, pullback.map]
  have hcompat (g : G) : sj g ≫ pullback.fst p q = pullback.fst p q ≫ s g := by
    simp [sj, pullback.map]
  refine ⟨j.unop, hij, ?_⟩
  exact (comparison_isIso_iff G p pj q (pullback.fst p q)
    (IsPullback.of_hasPullback p q) s hs sj hsj hcompat).mp hiso


/-- An unpointed finite torsor descends along affine inverse limits. -/
theorem GaloisCover.exists_stage_of_affine_limits
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    (hDqc : ∀ i, CompactSpace (D.obj i)) (hDqs : ∀ i, QuasiSeparatedSpace (D.obj i))
    (hDa : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f))
    {X : Scheme.{u}} (κ : (Functor.const I).obj X ⟶ D)
    (hκ : IsLimit (Cone.mk X κ))
    (G : Type (u + 1)) [Group G] [Finite G] (Z : GaloisCover G X) :
    ∃ (i : I) (Z₀ : GaloisCover G (D.obj i)) (χ : Z.P ⟶ Z₀.P),
      IsPullback χ Z.π Z₀.π (κ.app i) := by
  classical
  obtain ⟨A, hA, hdir, hne, F, hF⟩ := IsFiltered.exists_directed Iᵒᵖ
  let E := F.leftOp ⋙ D
  let c := (Cone.mk X κ).whisker F.leftOp
  have hc : IsLimit c :=
    (Functor.Initial.isLimitWhiskerEquiv F.leftOp (Cone.mk X κ)).symm hκ
  have (a : Aᵒᵖ) : CompactSpace (E.obj a) := hDqc _
  have (a : Aᵒᵖ) : QuasiSeparatedSpace (E.obj a) := hDqs _
  have {a b : Aᵒᵖ} (f : a ⟶ b) : IsAffineHom (E.map f) := hDa _
  have : IsFinite Z.π := Z.isFinite
  have : Etale Z.π := Z.etale
  have : Surjective Z.π := Z.surjective
  obtain ⟨i, P, p, hfin, het, hsurj, χ, H⟩ :=
    exists_finiteEtaleSurjective_limit_stage E c hc Z.π
  have := hfin
  have := het
  have := hsurj
  obtain ⟨j, hij, s, hs, hequiv⟩ :=
    exists_action_maps_stage E c hc G Z i p χ H
  let f := (homOfLE hij).op
  let pj := pullback.snd p (E.map f)
  let χj := isPullbackLift E c f H
  have Hj : IsPullback χj Z.π pj (c.π.app (Opposite.op j)) :=
    isPullback_isPullbackLift f H
  obtain ⟨k, hjk, h1, hmul⟩ :=
    exists_action_laws_stage E c hc G Z j pj χj Hj s hs hequiv
  let a := (homOfLE hjk).op
  let q := E.map a
  let sk (g : G) := pullback.map pj q pj q (s g) (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using (hs g).symm) (by simp)
  let pk := pullback.snd pj q
  let χk := isPullbackLift E c a Hj
  have Hk : IsPullback χk Z.π pk (c.π.app (Opposite.op k)) :=
    isPullback_isPullbackLift a Hj
  have hsk (g : G) : sk g ≫ pk = pk := by simp [sk, pk, pullback.map]
  have hek (g : G) : Z.smul g ≫ χk = χk ≫ sk g := by
    apply pullback.hom_ext
    · dsimp [χk, sk, q, a]
      simp only [Category.assoc, pullback.map, pullback.lift_fst,
        isPullbackLift_fst, isPullbackLift_fst_assoc]
      exact hequiv g
    · dsimp [χk, sk, pk, q, a]
      simp only [Category.assoc, pullback.map, pullback.lift_snd,
        Category.comp_id, isPullbackLift_snd]
      rw [← Category.assoc, Z.smul_π]
  have h1' : sk 1 = 𝟙 _ := h1
  have hmul' (g h : G) : sk (g * h) = sk h ≫ sk g := hmul g h
  obtain ⟨l, hkl, hiso⟩ := GaloisCover.exists_comparison_stage_on_action_model
    E c hc G Z k pk χk Hk sk hsk hek
  let b := (homOfLE hkl).op
  let r := E.map b
  let sl (g : G) := pullback.map pk r pk r (sk g) (𝟙 _) (𝟙 _)
    (by simp [hsk]) (by simp)
  let Z₀ : GaloisCover G (E.obj (Opposite.op l)) :=
    { P := pullback pk r
      π := pullback.snd pk r
      isFinite := inferInstance
      etale := inferInstance
      surjective := inferInstance
      smul := sl
      smul_π := fun g ↦ by simp [sl, pullback.map]
      one_smul := by
        apply pullback.hom_ext <;> simp [sl, pullback.map, h1']
      mul_smul := fun g h ↦ by
        apply pullback.hom_ext <;> simp [sl, pullback.map, hmul', Category.assoc]
      isIso_sigmaDesc := hiso }
  refine ⟨F.leftOp.obj (Opposite.op l), Z₀, isPullbackLift E c b Hk, ?_⟩
  exact isPullback_isPullbackLift b Hk

end AlgebraicGeometry.Scheme
