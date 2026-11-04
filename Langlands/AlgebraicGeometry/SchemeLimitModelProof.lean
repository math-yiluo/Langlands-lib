import Langlands.AlgebraicGeometry.SchemeLimitModelStatement

/-! # Nonaffine scheme-model morphism descent -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

open EtaleEquivalenceRelation.Action.TargetLimit AffineLimit

variable {I : Type u} [Category.{u} I]
  (D : I ⥤ Scheme.{u}) {S X Y : Scheme.{u}}
  (t : D ⟶ (Functor.const I).obj S) (a : X ⟶ S) (b : Y ⟶ S)

private lemma transition_isPullback {i j : I} (r : i ⟶ j) :
    IsPullback ((diagram D t a).map r) (pullback.fst (t.app i) a)
      (pullback.fst (t.app j) a) (D.map r) := by
  have ht : D.map r ≫ t.app j = t.app i := by
    simp
  exact IsPullback.of_right
    (h₁₂ := pullback.snd (t.app j) a) (h₂₂ := t.app j)
    (by simpa only [diagram_map_snd, ht] using
      (IsPullback.of_hasPullback (t.app i) a).flip)
    (diagram_map_fst D t a r) (IsPullback.of_hasPullback (t.app j) a).flip

private instance [∀ i, IsAffine (D.obj i)] {i j : I} (r : i ⟶ j) :
    IsAffineHom ((diagram D t a).map r) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom)
    (transition_isPullback D t a r).flip inferInstance

private instance [∀ i, IsAffine (D.obj i)] [QuasiCompact a] (i : I) :
    CompactSpace ((diagram D t a).obj i) := by
  change CompactSpace ↑(pullback (t.app i) a : Scheme.{u})
  infer_instance

private instance [∀ i, IsAffine (D.obj i)] [QuasiSeparated a] (i : I) :
    QuasiSeparatedSpace ((diagram D t a).obj i) :=
  quasiSeparatedSpace_of_quasiSeparated (pullback.fst (t.app i) a)

private noncomputable def levelId (i : I) : LevelHom D t a a i :=
  ⟨𝟙 _, by simp⟩

private noncomputable def levelComp {Z : Scheme.{u}} (d : Z ⟶ S) {i : I}
    (f : LevelHom D t a b i) (g : LevelHom D t b d i) : LevelHom D t a d i :=
  ⟨f.val ≫ g.val, by rw [Category.assoc, g.property, f.property]⟩

private lemma restrict_levelId {i j : I} (r : i ⟶ j) :
    restrict D t a a r (levelId D t a j) = levelId D t a i := by
  apply Subtype.ext
  apply pullback.hom_ext
  · simp [levelId]
  · change (restrict D t a a r (levelId D t a j)).val ≫ pullback.snd (t.app i) a =
      (𝟙 _) ≫ pullback.snd (t.app i) a
    simp [levelId]

private lemma restrict_levelComp {Z : Scheme.{u}} (d : Z ⟶ S) {i j : I} (r : i ⟶ j)
    (f : LevelHom D t a b j) (g : LevelHom D t b d j) :
    restrict D t a d r (levelComp D t a b d f g) =
      levelComp D t a b d (restrict D t a b r f) (restrict D t b d r g) := by
  apply Subtype.ext
  apply pullback.hom_ext
  · simp [levelComp]
  · change (restrict D t a d r (levelComp D t a b d f g)).val ≫
        pullback.snd (t.app i) d =
      ((restrict D t a b r f).val ≫ (restrict D t b d r g).val) ≫
        pullback.snd (t.app i) d
    simp only [restrict_snd, levelComp, Category.assoc]
    rw [← Category.assoc (restrict D t a b r f).val ((diagram D t b).map r),
      ← restrict_square]
    simp only [Category.assoc]

private noncomputable def limitId {T : Scheme.{u}} (p : T ⟶ S) : LimitHom a a p :=
  ⟨𝟙 _, by simp⟩

private noncomputable def limitComp {Z T : Scheme.{u}} (d : Z ⟶ S) (p : T ⟶ S)
    (f : LimitHom a b p) (g : LimitHom b d p) : LimitHom a d p :=
  ⟨f.val ≫ g.val, by rw [Category.assoc, g.property, f.property]⟩

private lemma toLimit_levelId (c : Cone D) (p : c.pt ⟶ S)
    (hp : ∀ i, c.π.app i ≫ t.app i = p) (i : I) :
    toLimit D t a a c p hp i (levelId D t a i) = limitId a p := by
  apply Subtype.ext
  apply pullback.hom_ext
  · simp [limitId]
  · simp [levelId, limitId]

private lemma toLimit_levelComp {Z : Scheme.{u}} (d : Z ⟶ S) (c : Cone D) (p : c.pt ⟶ S)
    (hp : ∀ i, c.π.app i ≫ t.app i = p) (i : I)
    (f : LevelHom D t a b i) (g : LevelHom D t b d i) :
    toLimit D t a d c p hp i (levelComp D t a b d f g) =
      limitComp a b d p (toLimit D t a b c p hp i f) (toLimit D t b d c p hp i g) := by
  apply Subtype.ext
  apply pullback.hom_ext
  · simp [limitComp]
  · simp only [toLimit_snd, levelComp, limitComp, Subtype.coe_mk, Category.assoc]
    rw [← Category.assoc (toLimit D t a b c p hp i f).val
        ((cone D t b c p hp).π.app i), ← toLimit_square]
    simp only [Category.assoc]

variable [IsCofiltered I] [∀ i, IsAffine (D.obj i)]
  (c : Cone D) (hc : IsLimit c) (p : c.pt ⟶ S)
  (hp : ∀ i, c.π.app i ≫ t.app i = p)

include hc in
/-- Factor an actual morphism between the limit base changes of nonaffine models. -/
lemma exists_level_morphism [QuasiCompact a] [QuasiSeparated a]
    [LocallyOfFinitePresentation b] (f : LimitHom a b p) :
    ∃ (i : I) (fi : LevelHom D t a b i), toLimit D t a b c p hp i fi = f := by
  have hbase : (f.val ≫ pullback.snd p b) ≫ b = pullback.snd p a ≫ a := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, f.property,
      pullback.condition]
  obtain ⟨i, g, hg, hgb⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (diagram D t a) (comparison D t a ≫ (Functor.const I).map a)
      b (cone D t a c p hp) (isLimitCone D t a c p hp hc)
      (f.val ≫ pullback.snd p b) (by
        ext i
        simp only [NatTrans.comp_app, Functor.const_map_app, comparison,
          cone_π_snd_assoc]
        exact hbase.symm)
  change g ≫ b = pullback.snd (t.app i) a ≫ a at hgb
  let fi : LevelHom D t a b i :=
    ⟨pullback.lift (pullback.fst (t.app i) a) g (by
      change pullback.fst (t.app i) a ≫ t.app i = g ≫ b
      rw [hgb, pullback.condition]),
      pullback.lift_fst _ _ _⟩
  refine ⟨i, fi, ?_⟩
  apply Subtype.ext
  apply pullback.hom_ext
  · simp [f.property]
  · simpa [fi] using hg

include hc in
/-- Equality of two actual level morphisms is detected at a common level. -/
lemma eventually_equal [QuasiCompact a] [LocallyOfFiniteType b]
    (i j : I) (fi : LevelHom D t a b i) (fj : LevelHom D t a b j)
    (h : toLimit D t a b c p hp i fi = toLimit D t a b c p hp j fj) :
    ∃ (k : I) (r : k ⟶ i) (s : k ⟶ j),
      restrict D t a b r fi = restrict D t a b s fj := by
  have heq : (cone D t a c p hp).π.app i ≫ fi.val ≫ pullback.snd (t.app i) b =
      (cone D t a c p hp).π.app j ≫ fj.val ≫ pullback.snd (t.app j) b := by
    simpa only [toLimit_snd] using
      congrArg (fun f : LimitHom a b p => f.val ≫ pullback.snd p b) h
  obtain ⟨k, r, s, hrs⟩ := Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType
    (diagram D t a) (comparison D t a ≫ (Functor.const I).map a)
    b (cone D t a c p hp) (isLimitCone D t a c p hp hc)
    (fi.val ≫ pullback.snd (t.app i) b)
    (by
      change pullback.snd (t.app i) a ≫ a = (fi.val ≫ pullback.snd (t.app i) b) ≫ b
      rw [Category.assoc, ← pullback.condition (f := t.app i) (g := b), ← Category.assoc, fi.property,
        pullback.condition])
    (fj.val ≫ pullback.snd (t.app j) b)
    (by
      change pullback.snd (t.app j) a ≫ a = (fj.val ≫ pullback.snd (t.app j) b) ≫ b
      rw [Category.assoc, ← pullback.condition (f := t.app j) (g := b), ← Category.assoc, fj.property,
        pullback.condition]) heq
  refine ⟨k, r, s, ?_⟩
  apply Subtype.ext
  apply pullback.hom_ext
  · simp
  · change (restrict D t a b r fi).val ≫ pullback.snd (t.app k) b =
      (restrict D t a b s fj).val ≫ pullback.snd (t.app k) b
    simpa only [restrict_snd] using hrs

include hc in
/-- Descend a prescribed isomorphism, retaining its actual limit restriction. -/
lemma exists_level_isomorphism
    [QuasiCompact a] [QuasiSeparated a] [LocallyOfFinitePresentation a]
    [QuasiCompact b] [QuasiSeparated b] [LocallyOfFinitePresentation b]
    (e : pullback p a ≅ pullback p b)
    (he : e.hom ≫ pullback.fst p b = pullback.fst p a) :
    ∃ (i : I) (ei : (diagram D t a).obj i ≅ (diagram D t b).obj i)
      (hei : ei.hom ≫ pullback.fst (t.app i) b = pullback.fst (t.app i) a),
      toLimit D t a b c p hp i ⟨ei.hom, hei⟩ = ⟨e.hom, he⟩ := by
  have hein : e.inv ≫ pullback.fst p a = pullback.fst p b := by
    rw [← he, e.inv_hom_id_assoc]
  obtain ⟨i, f, hf⟩ := exists_level_morphism D t a b c hc p hp ⟨e.hom, he⟩
  obtain ⟨j, g, hg⟩ := exists_level_morphism D t b a c hc p hp ⟨e.inv, hein⟩
  let k := IsCofiltered.min i j
  let fk : LevelHom D t a b k := restrict D t a b (IsCofiltered.minToLeft i j) f
  let gk : LevelHom D t b a k := restrict D t b a (IsCofiltered.minToRight i j) g
  have hfk : toLimit D t a b c p hp k fk = ⟨e.hom, he⟩ := by
    simpa only [fk, toLimit_restrict] using hf
  have hgk : toLimit D t b a c p hp k gk = ⟨e.inv, hein⟩ := by
    simpa only [gk, toLimit_restrict] using hg
  have hfg : toLimit D t a a c p hp k (levelComp D t a b a fk gk) =
      toLimit D t a a c p hp k (levelId D t a k) := by
    rw [toLimit_levelComp, hfk, hgk, toLimit_levelId]
    apply Subtype.ext
    exact e.hom_inv_id
  have hgf : toLimit D t b b c p hp k (levelComp D t b a b gk fk) =
      toLimit D t b b c p hp k (levelId D t b k) := by
    rw [toLimit_levelComp, hgk, hfk, toLimit_levelId]
    apply Subtype.ext
    exact e.inv_hom_id
  obtain ⟨j₁, r₁, s₁, h₁⟩ := eventually_equal D t a a c hc p hp k k
    (levelComp D t a b a fk gk) (levelId D t a k) hfg
  obtain ⟨j₂, r₂, s₂, h₂⟩ := eventually_equal D t b b c hc p hp k k
    (levelComp D t b a b gk fk) (levelId D t b k) hgf
  obtain ⟨l, u, v, huv⟩ := IsCofiltered.cospan r₁ r₂
  let z : l ⟶ k := u ≫ r₁
  let fl : LevelHom D t a b l := restrict D t a b z fk
  let gl : LevelHom D t b a l := restrict D t b a z gk
  have hl : levelComp D t a b a fl gl = levelId D t a l := by
    have h := congrArg (restrict D t a a u) h₁
    simpa only [restrict_comp, restrict_levelComp, restrict_levelId, fl, gl, z] using h
  have hr : levelComp D t b a b gl fl = levelId D t b l := by
    have h := congrArg (restrict D t b b v) h₂
    simpa only [restrict_comp, restrict_levelComp, restrict_levelId, fl, gl, z, huv] using h
  let el : (diagram D t a).obj l ≅ (diagram D t b).obj l :=
    ⟨fl.val, gl.val, congrArg Subtype.val hl, congrArg Subtype.val hr⟩
  refine ⟨l, el, fl.property, ?_⟩
  change toLimit D t a b c p hp l fl = ⟨e.hom, he⟩
  simpa only [fl, toLimit_restrict] using hfk

/-- The complete nonaffine model-morphism descent target. -/
theorem modelMorphismDescent : ModelMorphismDescent.{u} := by
  intro I _ _ D _ S X Y t a b c hc p hp
  refine ⟨?_, ?_, ?_⟩
  · intro hqc hqs hfp
    let := hqc
    let := hqs
    let := hfp
    exact exists_level_morphism D t a b c hc p hp
  · intro hqc hft
    let := hqc
    let := hft
    exact eventually_equal D t a b c hc p hp
  · intro hqca hqsa hfpa hqcb hqsb hfpb
    let := hqca
    let := hqsa
    let := hfpa
    let := hqcb
    let := hqsb
    let := hfpb
    exact exists_level_isomorphism D t a b c hc p hp

end Langlands.AlgebraicGeometry.SchemeLimitModel
