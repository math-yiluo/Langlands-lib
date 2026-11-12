import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationLimitModelStatement
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationLimitModelLevels
import Langlands.AlgebraicGeometry.AlgebraicSpace.LimitSchemeRepresentation

/-! # Proof of finite-stage descent of étale scheme equivalence relations

Over the limit of a cofiltered affine diagram, models of the object and relation schemes
exist at a stage, the two structure maps descend to a later stage, and the laws of an étale
equivalence relation for the descended pair then hold at a further stage
(`LimitModel.levelLaws_descend`). The relation at that stage is assembled from the
base-changed models.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

namespace LimitModel

open AffineLimit SchemeLimitModel EtaleEquivalenceRelation.Action.TargetLimit

/-- Precomposing a pullback square with an isomorphism gives a pullback square. -/
lemma isPullback_iso_comp {C : Type*} [Category C] {P P' X Y Z : C} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (e : P' ≅ P)
    {snd' : P' ⟶ Y} (hs : e.hom ≫ snd = snd') : IsPullback (e.hom ≫ fst) snd' f g := by
  subst hs
  exact h.of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
    (by simp) (by simp)

/-- Precomposing the two left corners of a pullback square with isomorphisms gives a pullback
square. -/
lemma isPullback_iso_comp₂ {C : Type*} [Category C] {P P' X Y Y' Z : C} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (e : P' ≅ P)
    (e' : Y' ≅ Y) {snd' : P' ⟶ Y'} (hs : e.hom ≫ snd = snd' ≫ e'.hom) :
    IsPullback (e.hom ≫ fst) snd' f (e'.hom ≫ g) := by
  refine h.of_iso e.symm (Iso.refl _) e'.symm (Iso.refl _) (by simp) ?_ (by simp) (by simp)
  rw [Iso.symm_hom, Iso.symm_hom, eq_comm, Iso.inv_comp_eq, reassoc_of% hs]
  simp

section Over

variable {I : Type u} [SmallCategory I] (D : I ⥤ Scheme.{u}) (j : I)

/-- The stages over `j` lie over the stage `j`. -/
@[simps]
def overNat : Over.forget j ⋙ D ⟶ (Functor.const (Over j)).obj (D.obj j) where
  app k := D.map k.hom
  naturality k l r := by
    dsimp
    rw [← D.map_comp, Over.w, Category.comp_id]

variable {D} in
/-- The limit cone restricted to the stages over `j` is a limit cone. -/
noncomputable def overIsLimit [IsCofiltered I] {c : Cone D} (hc : IsLimit c) :
    IsLimit (c.whisker (Over.forget j)) :=
  (Functor.Initial.isLimitWhiskerEquiv (Over.forget j) c).symm hc

lemma over_hp (c : Cone D) (k : Over j) :
    (c.whisker (Over.forget j)).π.app k ≫ (overNat D j).app k = c.π.app j :=
  c.w k.hom

instance [∀ i, IsAffine (D.obj i)] (k : Over j) : IsAffine ((Over.forget j ⋙ D).obj k) :=
  inferInstanceAs (IsAffine (D.obj k.left))

end Over

/-- A finitely presented model at a stage gives one at every later stage. -/
lemma exists_model_rebase {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    {Z X : Scheme.{u}} (bZ : Z ⟶ c.pt) {j : I} (a : X ⟶ D.obj j)
    [LocallyOfFinitePresentation a] [QuasiCompact a] [QuasiSeparated a] (π : Z ⟶ X)
    (h : IsPullback π bZ a (c.π.app j)) {k : I} (r : k ⟶ j) :
    ∃ (X' : Scheme.{u}) (a' : X' ⟶ D.obj k) (π' : Z ⟶ X'),
      LocallyOfFinitePresentation a' ∧ QuasiCompact a' ∧ QuasiSeparated a' ∧
        IsPullback π' bZ a' (c.π.app k) := by
  refine ⟨pullback (D.map r) a, pullback.fst _ _,
    pullback.lift (bZ ≫ c.π.app k) π (by rw [Category.assoc, c.w r]; exact h.w.symm),
    MorphismProperty.pullback_fst _ _ inferInstance,
    MorphismProperty.pullback_fst _ _ inferInstance,
    MorphismProperty.pullback_fst _ _ inferInstance, ?_⟩
  apply IsPullback.of_right (h₁₂ := pullback.snd (D.map r) a) (h₂₂ := D.map r) (v₁₃ := a)
  · simpa using h
  · simp
  · exact (IsPullback.of_hasPullback (D.map r) a).flip

/-- Affineness of a base changed model persists at later stages. -/
lemma isAffine_level {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
    [∀ i, IsAffine (D.obj i)] {S X : Scheme.{u}} (t : D ⟶ (Functor.const I).obj S)
    (a : X ⟶ S) {i j : I} (r : i ⟶ j) (H : IsAffine (pullback (t.app j) a)) :
    IsAffine (pullback (t.app i) a) := by
  rw [← level_comp D t r]
  have : IsAffineHom (pullMap (t.app j) (D.map r) a) :=
    MorphismProperty.of_isPullback (pullMap_isPullback (t.app j) (D.map r) a).flip
      inferInstance
  exact isAffine_of_isAffineHom (pullMap (t.app j) (D.map r) a)

/-- The relation over the limit descends to a stage once both structure maps are base
changes of maps `ft fs` between finitely presented models over a common affine base. -/
lemma exists_stage {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ i, IsAffine (D.obj i)] {S X Y : Scheme.{u}} [IsAffine S]
    (t : D ⟶ (Functor.const I).obj S) (c : Cone D) (hc : IsLimit c) (p : c.pt ⟶ S)
    (hp : ∀ i, c.π.app i ≫ t.app i = p) (a : X ⟶ S) (b : Y ⟶ S) (ft fs : Y ⟶ X)
    (wt : ft ≫ a = b) (ws : fs ≫ a = b)
    [LocallyOfFinitePresentation a] [QuasiCompact a] [QuasiSeparated a]
    [LocallyOfFinitePresentation b] [QuasiCompact b] [QuasiSeparated b]
    (E : EtaleEquivalenceRelation.{u}) [IsAffine E.U] (bE : E.U ⟶ c.pt)
    (hb : E.t ≫ bE = E.s ≫ bE) (πU : E.U ⟶ X) (πR : E.R ⟶ Y)
    (hU : IsPullback πU bE a p) (hR : IsPullback πR (E.t ≫ bE) b p)
    (ht : πR ≫ ft = E.t ≫ πU) (hs : πR ≫ fs = E.s ≫ πU) :
    ∃ (i : I) (Ei : EtaleEquivalenceRelation.{u})
      (bi : Ei.U ⟶ D.obj i) (fU : E.U ⟶ Ei.U) (fR : E.R ⟶ Ei.R),
      IsAffine Ei.U ∧ LocallyOfFinitePresentation bi ∧
      QuasiCompact (Ei.t ≫ bi) ∧ Ei.t ≫ bi = Ei.s ≫ bi ∧
      IsPullback fU bE bi (c.π.app i) ∧ E.IsCartesianHom Ei fU fR := by
  let eU := hU.flip.isoPullback
  let eR := hR.flip.isoPullback
  have ht' : eR.hom ≫ baseChangeMap b a ft wt p = E.t ≫ eU.hom := by
    apply pullback.hom_ext
    · simp [eU, eR]
    · simp [eU, eR, ht]
  have hs' : eR.hom ≫ baseChangeMap b a fs ws p = E.s ≫ eU.hom := by
    apply pullback.hom_ext
    · simp [eU, eR, hb]
    · simp [eU, eR, hs]
  have H₀ : LevelLaws a b ft fs wt ws p :=
    (levelLaws_iff a b ft fs wt ws p).mpr (Laws.of_iso eR eU ht' hs' (laws_of E))
  obtain ⟨i₁, h₁⟩ := levelLaws_descend a b ft fs wt ws D t c hc p hp H₀
  have : IsAffine (pullback p a) := IsAffine.of_isIso eU.inv
  obtain ⟨i₂, h₂⟩ := exists_isAffine_level D t a c hc p hp
  obtain ⟨k, ⟨r₁⟩, ⟨r₂⟩⟩ : ∃ k : I, Nonempty (k ⟶ i₁) ∧ Nonempty (k ⟶ i₂) :=
    ⟨_, ⟨IsCofiltered.minToLeft i₁ i₂⟩, ⟨IsCofiltered.minToRight i₁ i₂⟩⟩
  have hk := h₁.level r₁
  have hka : IsAffine (pullback (t.app k) a) := isAffine_level D t a r₂ h₂
  let Ei := ((levelLaws_iff a b ft fs wt ws (t.app k)).mp hk).relation
  have hEt : Ei.t = baseChangeMap b a ft wt (t.app k) := rfl
  have hEs : Ei.s = baseChangeMap b a fs ws (t.app k) := rfl
  refine ⟨k, Ei, pullback.fst (t.app k) a, eU.hom ≫ (cone D t a c p hp).π.app k,
    eR.hom ≫ (cone D t b c p hp).π.app k, hka,
    MorphismProperty.pullback_fst _ _ inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hEt, baseChangeMap_fst]
    exact MorphismProperty.pullback_fst _ _ inferInstance
  · rw [hEt, hEs, baseChangeMap_fst, baseChangeMap_fst]
  · exact isPullback_iso_comp (cone_π_isPullback a D t c p hp k) eU (by simp [eU])
  · rw [hEt, Category.assoc, ← (cone_baseChangeMap_isPullback b a ft wt D t c p hp k).w,
      reassoc_of% ht']
  · rw [hEs]
    exact isPullback_iso_comp₂ (cone_baseChangeMap_isPullback b a fs ws D t c p hp k).flip
      eR eU hs'

end LimitModel

open LimitModel AffineLimit SchemeLimitModel EtaleEquivalenceRelation.Action.TargetLimit

/-- Finite-stage descent of finitely presented étale scheme equivalence relations. -/
theorem limitModelExistence : LimitModelExistence.{u} := by
  intro I _ _ D _ c hc E _ b hb _ _
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have : Etale E.t := E.etale_t
  let ι : E.R ⟶ pullback b b := pullback.lift E.t E.s hb
  have : Mono ι := ⟨fun g h e => (laws_of E).1 _ g h
    (by simpa [ι] using e =≫ pullback.fst b b) (by simpa [ι] using e =≫ pullback.snd b b)⟩
  have : QuasiSeparated (pullback.fst b b) := MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiSeparated (E.t ≫ b) := by
    have e : E.t ≫ b = ι ≫ pullback.fst b b ≫ b := by simp [ι]
    rw [e]
    infer_instance
  have : LocallyOfFinitePresentation (Over.mk b).hom :=
    inferInstanceAs (LocallyOfFinitePresentation b)
  have : QuasiCompact (Over.mk b).hom := inferInstanceAs (QuasiCompact b)
  have : QuasiSeparated (Over.mk b).hom := inferInstanceAs (QuasiSeparated b)
  have : LocallyOfFinitePresentation (Over.mk (E.t ≫ b)).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (E.t ≫ b))
  have : QuasiCompact (Over.mk (E.t ≫ b)).hom := inferInstanceAs (QuasiCompact (E.t ≫ b))
  have : QuasiSeparated (Over.mk (E.t ≫ b)).hom := inferInstanceAs (QuasiSeparated (E.t ≫ b))
  obtain ⟨j₁, U₁, π₁, hU₁, hU₂, hU₃, pb₁⟩ :=
    AlgebraicSpace.exists_schemeModel_of_affineLimit D c hc (Over.mk b)
  obtain ⟨j₂, R₂, π₂, hR₁, hR₂, hR₃, pb₂⟩ :=
    AlgebraicSpace.exists_schemeModel_of_affineLimit D c hc (Over.mk (E.t ≫ b))
  obtain ⟨j₀, ⟨r₁⟩, ⟨r₂⟩⟩ : ∃ j₀ : I, Nonempty (j₀ ⟶ j₁) ∧ Nonempty (j₀ ⟶ j₂) :=
    ⟨_, ⟨IsCofiltered.minToLeft j₁ j₂⟩, ⟨IsCofiltered.minToRight j₁ j₂⟩⟩
  obtain ⟨X, a, πU, _, _, _, hU⟩ := exists_model_rebase D c b U₁.hom π₁ pb₁ r₁
  obtain ⟨Y, bR, πR, _, _, _, hR⟩ := exists_model_rebase D c (E.t ≫ b) R₂.hom π₂ pb₂ r₂
  -- Descend both structure maps to a stage over `j₀`.
  let c₀ := c.whisker (Over.forget j₀)
  have hc₀ : IsLimit c₀ := overIsLimit j₀ hc
  let t₀ := overNat D j₀
  have hp₀ := over_hp D j₀ c
  let eU := hU.flip.isoPullback
  let eR := hR.flip.isoPullback
  let τ₀ : LimitHom bR a (c.π.app j₀) := ⟨eR.inv ≫ E.t ≫ eU.hom, by simp [eU, eR]⟩
  let σ₀ : LimitHom bR a (c.π.app j₀) := ⟨eR.inv ≫ E.s ≫ eU.hom, by simp [eU, eR, ← hb]⟩
  obtain ⟨k₁, τ₁, hτ₁⟩ := exists_level_morphism (Over.forget j₀ ⋙ D) t₀ bR a c₀ hc₀
    (c.π.app j₀) hp₀ τ₀
  obtain ⟨k₂, σ₁, hσ₁⟩ := exists_level_morphism (Over.forget j₀ ⋙ D) t₀ bR a c₀ hc₀
    (c.π.app j₀) hp₀ σ₀
  obtain ⟨k, ⟨s₁⟩, ⟨s₂⟩⟩ : ∃ k : Over j₀, Nonempty (k ⟶ k₁) ∧ Nonempty (k ⟶ k₂) :=
    ⟨_, ⟨IsCofiltered.minToLeft k₁ k₂⟩, ⟨IsCofiltered.minToRight k₁ k₂⟩⟩
  let τ := restrict (Over.forget j₀ ⋙ D) t₀ bR a s₁ τ₁
  let σ := restrict (Over.forget j₀ ⋙ D) t₀ bR a s₂ σ₁
  have hτ : toLimit (Over.forget j₀ ⋙ D) t₀ bR a c₀ (c.π.app j₀) hp₀ k τ = τ₀ := by
    simp [τ, hτ₁]
  have hσ : toLimit (Over.forget j₀ ⋙ D) t₀ bR a c₀ (c.π.app j₀) hp₀ k σ = σ₀ := by
    simp [σ, hσ₁]
  -- The descended pair over the stage `k.left`.
  have : LocallyOfFinitePresentation (pullback.fst (t₀.app k) a) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiCompact (pullback.fst (t₀.app k) a) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiSeparated (pullback.fst (t₀.app k) a) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : LocallyOfFinitePresentation (pullback.fst (t₀.app k) bR) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiCompact (pullback.fst (t₀.app k) bR) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiSeparated (pullback.fst (t₀.app k) bR) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  let πU' := eU.hom ≫ (cone (Over.forget j₀ ⋙ D) t₀ a c₀ (c.π.app j₀) hp₀).π.app k
  let πR' := eR.hom ≫ (cone (Over.forget j₀ ⋙ D) t₀ bR c₀ (c.π.app j₀) hp₀).π.app k
  have hU' : IsPullback πU' b (pullback.fst (t₀.app k) a) (c.π.app k.left) :=
    isPullback_iso_comp (cone_π_isPullback a (Over.forget j₀ ⋙ D) t₀ c₀ (c.π.app j₀) hp₀ k)
      eU (by simp [eU])
  have hR' : IsPullback πR' (E.t ≫ b) (pullback.fst (t₀.app k) bR) (c.π.app k.left) :=
    isPullback_iso_comp (cone_π_isPullback bR (Over.forget j₀ ⋙ D) t₀ c₀ (c.π.app j₀) hp₀ k)
      eR (by simp [eR])
  have hτ' : πR' ≫ τ.val = E.t ≫ πU' := by
    simp only [πR', πU', Category.assoc]
    rw [toLimit_square, hτ]
    simp [τ₀]
  have hσ' : πR' ≫ σ.val = E.s ≫ πU' := by
    simp only [πR', πU', Category.assoc]
    rw [toLimit_square, hσ]
    simp [σ₀]
  obtain ⟨i, Ei, bi, fU, fR, h⟩ := exists_stage (Over.forget k.left ⋙ D)
    (overNat D k.left) (c.whisker (Over.forget k.left)) (overIsLimit k.left hc)
    (c.π.app k.left) (over_hp D k.left c) (pullback.fst (t₀.app k) a)
    (pullback.fst (t₀.app k) bR) τ.val σ.val τ.property σ.property E b hb πU' πR' hU' hR'
    hτ' hσ'
  exact ⟨i.left, Ei, bi, fU, fR, h⟩

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
