import Langlands.AlgebraicGeometry.SchemeLimitAffineStatement

/-! # Proof of relative affineness descent -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AffineLimit

open EtaleEquivalenceRelation.Action.TargetLimit

section Pullbacks

variable {S X Y T : Scheme.{u}}
  (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (w : f ≫ b = a)
  (p : T ⟶ S)

lemma baseChangeMap_isPullback :
    IsPullback (baseChangeMap a b f w p) (pullback.snd p a)
      (pullback.snd p b) f := by
  apply IsPullback.of_right
    (h₁₂ := pullback.fst p b) (h₂₂ := b) (v₁₃ := p)
  · simpa only [baseChangeMap_fst, w] using IsPullback.of_hasPullback p a
  · exact baseChangeMap_snd a b f w p
  · exact IsPullback.of_hasPullback p b

lemma baseChangeMap_square_isPullback {Z U : Scheme.{u}}
    (z : Z ⟶ S) (u : U ⟶ S)
    (g : Z ⟶ X) (h : Z ⟶ U) (q : U ⟶ Y)
    (wg : g ≫ a = z) (wh : h ≫ u = z) (wq : q ≫ b = u)
    (H : IsPullback g h f q) :
    IsPullback (baseChangeMap z a g wg p) (baseChangeMap z u h wh p)
      (baseChangeMap a b f w p) (baseChangeMap u b q wq p) := by
  apply IsPullback.of_right
    (h₁₂ := pullback.snd p a) (h₂₂ := pullback.snd p b) (v₁₃ := f)
  · simpa only [baseChangeMap_snd] using
      ((baseChangeMap_isPullback z u h wh p).flip.paste_horiz H)
  · apply pullback.hom_ext
    · simp
    · simp only [Category.assoc, baseChangeMap_snd, baseChangeMap_snd_assoc]
      exact congrArg (pullback.snd p z ≫ ·) H.w
  · exact (baseChangeMap_isPullback a b f w p).flip

noncomputable def baseChangeCover (𝒰 : Y.OpenCover) :
    (pullback p b).OpenCover :=
  Scheme.Cover.copy (𝒰.pullback₁ (pullback.snd p b)) 𝒰.I₀
    (fun i ↦ pullback p (𝒰.f i ≫ b))
    (fun i ↦ baseChangeMap (𝒰.f i ≫ b) b (𝒰.f i) rfl p)
    (Equiv.refl _)
    (fun i ↦ (baseChangeMap_isPullback (𝒰.f i ≫ b) b (𝒰.f i) rfl p).isoPullback)
    (fun i ↦
      (baseChangeMap_isPullback (𝒰.f i ≫ b) b (𝒰.f i) rfl p).isoPullback_hom_fst.symm)

include w in
lemma chart_structure (q : T ⟶ Y) :
    pullback.fst f q ≫ a = pullback.snd f q ≫ (q ≫ b) := by
  rw [← w, ← Category.assoc, pullback.condition, Category.assoc]

lemma chart_isPullback {U : Scheme.{u}} (q : U ⟶ Y) :
    IsPullback
      (baseChangeMap (pullback.snd f q ≫ (q ≫ b)) a (pullback.fst f q)
        (chart_structure a b f w q) p)
      (baseChangeMap (pullback.snd f q ≫ (q ≫ b)) (q ≫ b)
        (pullback.snd f q) rfl p)
      (baseChangeMap a b f w p)
      (baseChangeMap (q ≫ b) b q rfl p) :=
  baseChangeMap_square_isPullback a b f w p _ _
    (pullback.fst f q) (pullback.snd f q) q
    (chart_structure a b f w q) rfl rfl (IsPullback.of_hasPullback f q)

lemma isAffine_chart [IsAffine S] [IsAffine T] {U : Scheme.{u}} [IsAffine U]
    (q : U ⟶ Y) [IsAffineHom (baseChangeMap a b f w p)] :
    IsAffine (pullback p (pullback.snd f q ≫ (q ≫ b))) := by
  have : IsAffineHom
      (baseChangeMap (pullback.snd f q ≫ (q ≫ b)) (q ≫ b)
        (pullback.snd f q) rfl p) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (chart_isPullback a b f w p q) inferInstance
  exact isAffine_of_isAffineHom
    (baseChangeMap (pullback.snd f q ≫ (q ≫ b)) (q ≫ b)
      (pullback.snd f q) rfl p)

lemma isAffineHom_of_affine_charts [IsAffine S] [IsAffine T]
    (𝒰 : Y.OpenCover) [∀ i, IsAffine (𝒰.X i)]
    (H : ∀ i, IsAffine (pullback p (pullback.snd f (𝒰.f i) ≫ (𝒰.f i ≫ b)))) :
    IsAffineHom (baseChangeMap a b f w p) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsAffineHom)
    (baseChangeCover b p 𝒰)
  intro i
  have : IsAffine (pullback p (pullback.snd f (𝒰.f i) ≫ (𝒰.f i ≫ b))) := H i
  have : IsAffine (pullback (baseChangeMap a b f w p)
      (baseChangeMap (𝒰.f i ≫ b) b (𝒰.f i) rfl p)) :=
    .of_isIso (chart_isPullback a b f w p (𝒰.f i)).isoPullback.inv
  change IsAffineHom (pullback.snd (baseChangeMap a b f w p)
    (baseChangeMap (𝒰.f i ≫ b) b (𝒰.f i) rfl p))
  infer_instance

variable {I : Type u} [Category.{u} I]
  (D : I ⥤ Scheme.{u})
  (t : D ⟶ (Functor.const I).obj S)

lemma diagram_map_isPullback {i j : I} (r : i ⟶ j) :
    IsPullback ((diagram D t a).map r) (pullback.fst (t.app i) a)
      (pullback.fst (t.app j) a) (D.map r) := by
  apply IsPullback.of_right
    (h₁₂ := pullback.snd (t.app j) a) (h₂₂ := t.app j) (v₁₃ := a)
  · have e : D.map r ≫ t.app j = t.app i := by simp
    simpa only [diagram_map_snd, e] using
      (IsPullback.of_hasPullback (t.app i) a).flip
  · exact diagram_map_fst D t a r
  · exact (IsPullback.of_hasPullback (t.app j) a).flip

lemma cone_π_isPullback (c : Cone D) (q : c.pt ⟶ S)
    (hq : ∀ i, c.π.app i ≫ t.app i = q) (i : I) :
    IsPullback ((cone D t a c q hq).π.app i) (pullback.fst q a)
      (pullback.fst (t.app i) a) (c.π.app i) := by
  apply IsPullback.of_right
    (h₁₂ := pullback.snd (t.app i) a) (h₂₂ := t.app i) (v₁₃ := a)
  · simpa only [cone_π_snd, hq] using (IsPullback.of_hasPullback q a).flip
  · exact cone_π_fst D t a c q hq i
  · exact (IsPullback.of_hasPullback (t.app i) a).flip

lemma cone_baseChangeMap_isPullback (c : Cone D) (q : c.pt ⟶ S)
    (hq : ∀ i, c.π.app i ≫ t.app i = q) (i : I) :
    IsPullback (baseChangeMap a b f w q)
      ((cone D t a c q hq).π.app i)
      ((cone D t b c q hq).π.app i)
      (baseChangeMap a b f w (t.app i)) := by
  apply IsPullback.of_right
    (h₁₂ := pullback.fst q b) (h₂₂ := pullback.fst (t.app i) b)
    (v₁₃ := c.π.app i)
  · simpa only [baseChangeMap_fst] using (cone_π_isPullback a D t c q hq i).flip
  · exact (cone_baseChangeMap D t a b f w c q hq i).symm
  · exact (cone_π_isPullback b D t c q hq i).flip

end Pullbacks

section Structural

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) {S Z : Scheme.{u}}
  [IsAffine S] [∀ i, IsAffine (D.obj i)]
  (t : D ⟶ (Functor.const I).obj S) (a : Z ⟶ S)
  (c : Cone D) (hc : IsLimit c) (p : c.pt ⟶ S)
  (hp : ∀ i, c.π.app i ≫ t.app i = p)

include hc hp in
omit [IsAffine S] in
lemma exists_isAffine_level [QuasiCompact a] [QuasiSeparated a]
    [IsAffine (pullback p a)] :
    ∃ i, IsAffine (pullback (t.app i) a) := by
  have : ∀ {i j : I} (r : i ⟶ j), IsAffineHom ((diagram D t a).map r) := by
    intro i j r
    exact MorphismProperty.of_isPullback (P := @IsAffineHom)
      (diagram_map_isPullback a D t r).flip inferInstance
  have (i : I) : CompactSpace ((diagram D t a).obj i) := by
    change CompactSpace (pullback (t.app i) a : Scheme.{u})
    infer_instance
  have (i : I) : QuasiSeparatedSpace ((diagram D t a).obj i) := by
    change QuasiSeparatedSpace (pullback (t.app i) a : Scheme.{u})
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst (t.app i) a)
  have : IsAffine (cone D t a c p hp).pt :=
    (inferInstance : IsAffine (pullback p a))
  exact Scheme.exists_isAffine_of_isLimit (diagram D t a)
    (cone D t a c p hp) (isLimitCone D t a c p hp hc)

end Structural

/-- Affineness of a relative morphism descends chartwise to one common level. -/
theorem relativeAffinenessDescent : RelativeAffinenessDescent.{u} := by
  intro I _ _ D S X Y _ _ t a b f w _ _ _ c hc p hp
  classical
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace b
  let 𝒰 := Y.affineCover.finiteSubcover
  constructor
  · intro H
    let := H
    have hchart (k : 𝒰.I₀) :
        ∃ i, IsAffine (pullback (t.app i)
          (pullback.snd f (𝒰.f k) ≫ (𝒰.f k ≫ b))) := by
      let z := pullback.snd f (𝒰.f k) ≫ (𝒰.f k ≫ b)
      have : QuasiCompact z := by dsimp [z]; infer_instance
      have : QuasiSeparated z := by dsimp [z]; infer_instance
      have : IsAffine (pullback p z) := isAffine_chart a b f w p (𝒰.f k)
      exact exists_isAffine_level D t z c hc p hp
    choose j hj using hchart
    obtain ⟨i, hi⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image j)
    let r (k : 𝒰.I₀) : i ⟶ j k := (hi (by simp)).some
    refine ⟨i, isAffineHom_of_affine_charts a b f w (t.app i) 𝒰 ?_⟩
    intro k
    let z := pullback.snd f (𝒰.f k) ≫ (𝒰.f k ≫ b)
    have : IsAffine ((diagram D t z).obj (j k)) := hj k
    have : IsAffineHom ((diagram D t z).map (r k)) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom)
        (diagram_map_isPullback z D t (r k)).flip inferInstance
    exact isAffine_of_isAffineHom ((diagram D t z).map (r k))
  · rintro ⟨i, H⟩
    exact MorphismProperty.of_isPullback (P := @IsAffineHom)
      (cone_baseChangeMap_isPullback a b f w D t c p hp i).flip H

end Langlands.AlgebraicGeometry.AffineLimit
