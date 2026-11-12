import Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
import Langlands.AbelianScheme.TorsionFiniteEtale
import Langlands.AlgebraicGeometry.SchemeLimitModelProof
import Langlands.AlgebraicGeometry.SchemeLimitAffineProof
import Langlands.AlgebraicGeometry.SchemeLimitRelativePropertyProof
import Langlands.AlgebraicGeometry.SchemeLimitOpenImmersionProof

/-! # Equivalence-relation laws at the stages of an affine limit

For two models `a : X ⟶ S` and `b : Y ⟶ S` and two maps `ft fs : Y ⟶ X` over `S`, the
base changes of `ft` and `fs` along `q : T ⟶ S` form a pair of maps
`pullback q b ⟶ pullback q a`. This file states the laws of an étale equivalence relation
for this pair as factorization properties of base changed models (`LevelLaws`), shows that
they agree with the pointwise laws (`Laws`), are stable under further base change, and
descend from the limit of a cofiltered affine diagram to one of its stages.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.LimitModel

open AffineLimit SchemeLimitModel EtaleEquivalenceRelation.Action.TargetLimit

section Laws

/-- The laws of an étale equivalence relation for a pair `t s : R ⟶ U`, stated on points:
`(t, s)` is injective on points, reflexive, symmetric and transitive, and both maps are
étale. -/
def Laws {R U : Scheme.{u}} (t s : R ⟶ U) : Prop :=
  (∀ (T : Scheme.{u}) (g h : T ⟶ R), g ≫ t = h ≫ t → g ≫ s = h ≫ s → g = h) ∧
  (∀ (T : Scheme.{u}) (x : T ⟶ U), ∃ r : T ⟶ R, r ≫ t = x ∧ r ≫ s = x) ∧
  (∀ (T : Scheme.{u}) (r : T ⟶ R), ∃ r' : T ⟶ R, r' ≫ t = r ≫ s ∧ r' ≫ s = r ≫ t) ∧
  (∀ (T : Scheme.{u}) (r r' : T ⟶ R), r ≫ s = r' ≫ t →
    ∃ r'' : T ⟶ R, r'' ≫ t = r ≫ t ∧ r'' ≫ s = r' ≫ s) ∧
  Etale t ∧ Etale s

/-- An étale equivalence relation satisfies the pointwise laws. -/
lemma laws_of (E : EtaleEquivalenceRelation.{u}) : Laws E.t E.s := by
  refine ⟨fun T g h ht hs => ?_, E.refl, E.symm, E.trans, E.etale_t, E.etale_s⟩
  have := E.mono_lift
  rw [← cancel_mono (prod.lift E.t E.s)]
  apply prod.hom_ext <;> simpa

/-- The pointwise laws give an étale equivalence relation. -/
def Laws.relation {R U : Scheme.{u}} {t s : R ⟶ U} (H : Laws t s) :
    EtaleEquivalenceRelation.{u} where
  U := U
  R := R
  t := t
  s := s
  mono_lift := ⟨fun g h e => H.1 _ g h (by simpa using e =≫ prod.fst)
    (by simpa using e =≫ prod.snd)⟩
  refl := H.2.1
  symm := H.2.2.1
  trans := H.2.2.2.1
  etale_t := H.2.2.2.2.1
  etale_s := H.2.2.2.2.2

/-- The pointwise laws transfer along isomorphisms of both schemes. -/
lemma Laws.of_iso {R U R' U' : Scheme.{u}} {t s : R ⟶ U} {t' s' : R' ⟶ U'}
    (eR : R ≅ R') (eU : U ≅ U') (ht : eR.hom ≫ t' = t ≫ eU.hom)
    (hs : eR.hom ≫ s' = s ≫ eU.hom) (H : Laws t s) : Laws t' s' := by
  have ht' : t' = eR.inv ≫ t ≫ eU.hom := by rw [← ht, Iso.inv_hom_id_assoc]
  have hs' : s' = eR.inv ≫ s ≫ eU.hom := by rw [← hs, Iso.inv_hom_id_assoc]
  obtain ⟨hi, hr, hy, hx, het, hes⟩ := H
  subst ht' hs'
  refine ⟨fun T g h e₁ e₂ => ?_, fun T x => ?_, fun T r => ?_, fun T r r' e => ?_, ?_, ?_⟩
  · have := hi T (g ≫ eR.inv) (h ≫ eR.inv) (by simpa using e₁ =≫ eU.inv)
      (by simpa using e₂ =≫ eU.inv)
    simpa using this =≫ eR.hom
  · obtain ⟨r, h₁, h₂⟩ := hr T (x ≫ eU.inv)
    exact ⟨r ≫ eR.hom, by simp [reassoc_of% h₁], by simp [reassoc_of% h₂]⟩
  · obtain ⟨r', h₁, h₂⟩ := hy T (r ≫ eR.inv)
    exact ⟨r' ≫ eR.hom, by simp [reassoc_of% h₁], by simp [reassoc_of% h₂]⟩
  · obtain ⟨r'', h₁, h₂⟩ := hx T (r ≫ eR.inv) (r' ≫ eR.inv) (by simpa using e =≫ eU.inv)
    exact ⟨r'' ≫ eR.hom, by simp [reassoc_of% h₁], by simp [reassoc_of% h₂]⟩
  · infer_instance
  · infer_instance

end Laws

section BaseChange

variable {S T : Scheme.{u}} (q : T ⟶ S)

lemma baseChangeMap_comp {X Y Z : Scheme.{u}} (x : X ⟶ S) (y : Y ⟶ S) (z : Z ⟶ S)
    (f : X ⟶ Y) (g : Y ⟶ Z) (wf : f ≫ y = x) (wg : g ≫ z = y) :
    baseChangeMap x y f wf q ≫ baseChangeMap y z g wg q =
      baseChangeMap x z (f ≫ g) (by rw [Category.assoc, wg, wf]) q := by
  apply pullback.hom_ext <;> simp

variable {T' X : Scheme.{u}} (r : T' ⟶ T) (α : X ⟶ S)

/-- The comparison map from the base change along `r ≫ q` to the base change along `q`. -/
noncomputable def pullMap : pullback (r ≫ q) α ⟶ pullback q α :=
  pullback.lift (pullback.fst _ _ ≫ r) (pullback.snd _ _) (by
    rw [Category.assoc, pullback.condition])

@[reassoc (attr := simp)]
lemma pullMap_fst : pullMap q r α ≫ pullback.fst q α = pullback.fst (r ≫ q) α ≫ r :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pullMap_snd : pullMap q r α ≫ pullback.snd q α = pullback.snd (r ≫ q) α :=
  pullback.lift_snd _ _ _

lemma pullMap_isPullback :
    IsPullback (pullMap q r α) (pullback.fst (r ≫ q) α) (pullback.fst q α) r := by
  apply IsPullback.of_right (h₁₂ := pullback.snd q α) (h₂₂ := q) (v₁₃ := α)
  · simpa only [pullMap_snd] using (IsPullback.of_hasPullback (r ≫ q) α).flip
  · exact pullMap_fst q r α
  · exact (IsPullback.of_hasPullback q α).flip

variable {Y : Scheme.{u}} (β : Y ⟶ S) (f : X ⟶ Y) (w : f ≫ β = α)

/-- Base change along `r ≫ q` of a map over `S` is the base change along `pullMap` of its
base change along `q`. -/
lemma pullMap_baseChangeMap_isPullback :
    IsPullback (pullMap q r α) (baseChangeMap α β f w (r ≫ q))
      (baseChangeMap α β f w q) (pullMap q r β) := by
  apply IsPullback.of_bot (v₂₁ := pullback.fst (r ≫ q) β) (v₂₂ := pullback.fst q β)
    (h₃₁ := r)
  · simpa only [baseChangeMap_fst] using pullMap_isPullback q r α
  · apply pullback.hom_ext <;> simp
  · exact pullMap_isPullback q r β

/-- A property stable under base change passes from the base change along `q` to the base
change along `r ≫ q`. -/
lemma baseChangeMap_comp_left {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    (H : P (baseChangeMap α β f w q)) : P (baseChangeMap α β f w (r ≫ q)) :=
  P.of_isPullback (pullMap_baseChangeMap_isPullback q r α β f w) H

end BaseChange

section Fact

variable {S Z W V : Scheme.{u}} (α : Z ⟶ S) (β : W ⟶ S) (g : W ⟶ V) (h : Z ⟶ V)

/-- After base change along `q`, the map `h` factors through `g` by a map of base changed
models over the new base. -/
def Fact {T : Scheme.{u}} (q : T ⟶ S) : Prop :=
  ∃ φ : pullback q α ⟶ pullback q β, φ ≫ pullback.fst q β = pullback.fst q α ∧
    φ ≫ pullback.snd q β ≫ g = pullback.snd q α ≫ h

variable {α β g h} in
/-- A factorization persists after further base change. -/
lemma Fact.comp {T T' : Scheme.{u}} {q : T ⟶ S} (r : T' ⟶ T) (H : Fact α β g h q) :
    Fact α β g h (r ≫ q) := by
  obtain ⟨φ, h₁, h₂⟩ := H
  refine ⟨pullback.lift (pullback.fst (r ≫ q) α) (pullMap q r α ≫ φ ≫ pullback.snd q β) ?_,
    pullback.lift_fst _ _ _, ?_⟩
  · simp only [Category.assoc]
    rw [← pullback.condition, reassoc_of% h₁, pullMap_fst_assoc]
  · simp [h₂]

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
  (t : D ⟶ (Functor.const I).obj S)

lemma level_comp {i j : I} (r : i ⟶ j) : D.map r ≫ t.app j = t.app i := by
  simp

variable {α β g h D t} in
/-- A factorization at a stage persists at every later stage. -/
lemma Fact.level {i j : I} (r : i ⟶ j) (H : Fact α β g h (t.app j)) :
    Fact α β g h (t.app i) := by
  rw [← level_comp D t r]
  exact H.comp (D.map r)

variable [IsCofiltered I] [∀ i, IsAffine (D.obj i)]
  (c : Cone D) (hc : IsLimit c) (p : c.pt ⟶ S)
  (hp : ∀ i, c.π.app i ≫ t.app i = p)

include hc hp in
/-- A factorization over the limit already exists at a stage. -/
lemma Fact.descend {γ : V ⟶ S} (wg : g ≫ γ = β) (wh : h ≫ γ = α)
    [QuasiCompact α] [QuasiSeparated α] [LocallyOfFinitePresentation β]
    [LocallyOfFiniteType γ] (H : Fact α β g h p) : ∃ i, Fact α β g h (t.app i) := by
  obtain ⟨φ, h₁, h₂⟩ := H
  obtain ⟨i, fi, hfi⟩ := exists_level_morphism D t α β c hc p hp ⟨φ, h₁⟩
  obtain ⟨k, r, s, hrs⟩ := eventually_equal D t α γ c hc p hp i i
    ⟨fi.val ≫ baseChangeMap β γ g wg (t.app i), by simp [fi.property]⟩
    ⟨baseChangeMap α γ h wh (t.app i), by simp⟩ (by
      apply Subtype.ext
      apply pullback.hom_ext
      · simp
      · simp only [toLimit_snd, Category.assoc, baseChangeMap_snd, cone_π_snd_assoc]
        rw [← Category.assoc ((cone D t α c p hp).π.app i) fi.val,
          toLimit_square D t α β c p hp i fi, hfi]
        simp [h₂])
  refine ⟨k, (restrict D t α β r fi).val, (restrict D t α β r fi).property, ?_⟩
  have := congrArg (fun f : LevelHom D t α γ k => f.val ≫ pullback.snd (t.app k) γ) hrs
  simpa using this

end Fact

/-- Two properties that persist at later stages hold together at one stage. -/
lemma exists_and_of_mono {I : Type u} [Category.{u} I] [IsCofiltered I] {P Q : I → Prop}
    (hP : ∀ {i j : I}, (i ⟶ j) → P j → P i) (hQ : ∀ {i j : I}, (i ⟶ j) → Q j → Q i)
    (h₁ : ∃ i, P i) (h₂ : ∃ i, Q i) : ∃ i, P i ∧ Q i := by
  obtain ⟨i, hi⟩ := h₁
  obtain ⟨j, hj⟩ := h₂
  exact ⟨IsCofiltered.min i j, hP (IsCofiltered.minToLeft i j) hi,
    hQ (IsCofiltered.minToRight i j) hj⟩

section Level

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) {S X Y : Scheme.{u}}
  (t : D ⟶ (Functor.const I).obj S) (α : X ⟶ S) (β : Y ⟶ S) (f : X ⟶ Y) (w : f ≫ β = α)

/-- A property stable under base change passes from a stage to every later stage. -/
lemma baseChangeMap_level {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    {i j : I} (r : i ⟶ j) (H : P (baseChangeMap α β f w (t.app j))) :
    P (baseChangeMap α β f w (t.app i)) := by
  rw [← level_comp D t r]
  exact baseChangeMap_comp_left _ _ _ _ _ _ H

end Level

section Etale

variable {S X Y T : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) (f : Y ⟶ X) (w : f ≫ a = b)

lemma diagonal_model : pullback.diagonal f ≫ pullback.fst f f ≫ b = b := by simp

/-- The base change of the diagonal of `f` is the diagonal of the base change of `f`, up to
an isomorphism of its target. -/
lemma isOpenImmersion_baseChangeMap_diagonal_iff (q : T ⟶ S) :
    IsOpenImmersion (baseChangeMap b (pullback.fst f f ≫ b) (pullback.diagonal f)
        (diagonal_model b f) q) ↔
      IsOpenImmersion (pullback.diagonal (baseChangeMap b a f w q)) := by
  have wh : pullback.snd f f ≫ b = pullback.fst f f ≫ b := by
    have h := (pullback.condition (f := f) (g := f)) =≫ a
    simp only [Category.assoc, w] at h
    exact h.symm
  have H := baseChangeMap_square_isPullback b a f w q (pullback.fst f f ≫ b) b
    (pullback.fst f f) (pullback.snd f f) f rfl wh w (IsPullback.of_hasPullback f f)
  have he : baseChangeMap b (pullback.fst f f ≫ b) (pullback.diagonal f)
      (diagonal_model b f) q ≫ H.isoPullback.hom =
        pullback.diagonal (baseChangeMap b a f w q) := by
    apply pullback.hom_ext <;> apply pullback.hom_ext <;> simp
  rw [← he]
  exact (MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _ _).symm

/-- Étaleness of a base change of a finitely presented map is flatness together with the
diagonal being an open immersion. -/
lemma etale_baseChangeMap_iff [LocallyOfFinitePresentation f] (q : T ⟶ S) :
    Etale (baseChangeMap b a f w q) ↔ Flat (baseChangeMap b a f w q) ∧
      IsOpenImmersion (baseChangeMap b (pullback.fst f f ≫ b) (pullback.diagonal f)
        (diagonal_model b f) q) := by
  have : LocallyOfFinitePresentation (baseChangeMap b a f w q) :=
    MorphismProperty.of_isPullback (baseChangeMap_isPullback b a f w q).flip inferInstance
  rw [isOpenImmersion_baseChangeMap_diagonal_iff a b f w q]
  constructor
  · intro H
    exact ⟨(Etale.iff_flat_and_formallyUnramified.mp H).1, inferInstance⟩
  · rintro ⟨H₁, H₂⟩
    exact Etale.iff_flat_and_formallyUnramified.mpr ⟨H₁, inferInstance, this⟩

/-- Étaleness of the base change of a finitely presented map to the limit holds at a stage. -/
lemma etale_descend {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ i, IsAffine (D.obj i)] (t : D ⟶ (Functor.const I).obj S)
    (c : Cone D) (hc : IsLimit c) (p : c.pt ⟶ S) (hp : ∀ i, c.π.app i ≫ t.app i = p)
    [IsAffine S] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [QuasiSeparated f] [QuasiCompact a] [LocallyOfFinitePresentation b] [QuasiCompact b]
    [QuasiSeparated b] (H : Etale (baseChangeMap b a f w p)) :
    ∃ i, Etale (baseChangeMap b a f w (t.app i)) := by
  have : LocallyOfFinitePresentation (pullback.fst f f) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiCompact (pullback.fst f f) := MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiSeparated (pullback.fst f f) := MorphismProperty.pullback_fst _ _ inferInstance
  rw [etale_baseChangeMap_iff a b f w p] at H
  obtain ⟨H₁, H₂⟩ := H
  obtain ⟨i, hi⟩ := (relativeFlatDescent D t b a f w c hc p hp).mp H₁
  obtain ⟨j, hj⟩ := (relativeOpenImmersionDescent D t b (pullback.fst f f ≫ b)
    (pullback.diagonal f) (diagonal_model b f) c hc p hp).mp H₂
  obtain ⟨k, hk₁, hk₂⟩ := exists_and_of_mono
    (P := fun i => Flat (baseChangeMap b a f w (t.app i)))
    (Q := fun i => IsOpenImmersion (baseChangeMap b (pullback.fst f f ≫ b)
      (pullback.diagonal f) (diagonal_model b f) (t.app i)))
    (fun r H => baseChangeMap_level D t _ _ _ _ r H)
    (fun r H => baseChangeMap_level D t _ _ _ _ r H) ⟨i, hi⟩ ⟨j, hj⟩
  exact ⟨k, (etale_baseChangeMap_iff a b f w (t.app k)).mpr ⟨hk₁, hk₂⟩⟩

end Etale

section Models

variable {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) (ft fs : Y ⟶ X)
  (wt : ft ≫ a = b) (ws : fs ≫ a = b)

/-- The pair `(ft, fs)` as a map into the fibre square of `a`. -/
noncomputable def graph : Y ⟶ pullback a a :=
  pullback.lift ft fs (by rw [wt, ws])

local notation "Γ" => graph a b ft fs wt ws

@[reassoc (attr := simp)]
lemma graph_fst : Γ ≫ pullback.fst a a = ft := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma graph_snd : Γ ≫ pullback.snd a a = fs := pullback.lift_snd _ _ _

lemma graph_model : Γ ≫ pullback.fst a a ≫ a = b := by simp [wt]

lemma kernel_cond : pullback.fst Γ Γ ≫ b = pullback.snd Γ Γ ≫ b := by
  simpa [wt] using pullback.condition (f := Γ) (g := Γ) =≫ (pullback.fst a a ≫ a)

lemma kernel_ft : pullback.fst Γ Γ ≫ ft = pullback.snd Γ Γ ≫ ft := by
  simpa using pullback.condition (f := Γ) (g := Γ) =≫ pullback.fst a a

lemma kernel_fs : pullback.fst Γ Γ ≫ fs = pullback.snd Γ Γ ≫ fs := by
  simpa using pullback.condition (f := Γ) (g := Γ) =≫ pullback.snd a a

include wt ws in
lemma pair_cond : pullback.fst fs ft ≫ b = pullback.snd fs ft ≫ b := by
  simpa [ws, wt] using pullback.condition (f := fs) (g := ft) =≫ a

/-- The laws of an étale equivalence relation for the base changes of `ft` and `fs` along
`q`, stated as factorizations of base changed models (reflexivity, symmetry, transitivity,
and injectivity through the kernel pair of the graph) together with étaleness. -/
def LevelLaws {T : Scheme.{u}} (q : T ⟶ S) : Prop :=
  Fact a b Γ (pullback.diagonal a) q ∧
  Fact b b Γ (pullback.lift fs ft (by rw [ws, wt])) q ∧
  Fact (pullback.fst fs ft ≫ b) b Γ
    (pullback.lift (pullback.fst fs ft ≫ ft) (pullback.snd fs ft ≫ fs)
      (by rw [Category.assoc, Category.assoc, wt, ws, pair_cond a b ft fs wt ws])) q ∧
  Fact (pullback.fst Γ Γ ≫ b) b (pullback.diagonal b)
    (pullback.lift (pullback.fst Γ Γ) (pullback.snd Γ Γ) (kernel_cond a b ft fs wt ws)) q ∧
  Etale (baseChangeMap b a ft wt q) ∧ Etale (baseChangeMap b a fs ws q)

/-- The factorization form of the laws agrees with the pointwise laws of the base changed
pair. -/
lemma levelLaws_iff {T : Scheme.{u}} (q : T ⟶ S) :
    LevelLaws a b ft fs wt ws q ↔
      Laws (baseChangeMap b a ft wt q) (baseChangeMap b a fs ws q) := by
  constructor
  · rintro ⟨⟨φ₁, e₁, e₁'⟩, ⟨φ₂, e₂, e₂'⟩, ⟨φ₃, e₃, e₃'⟩, ⟨φ₄, -, e₄'⟩, het, hes⟩
    have e₁t : φ₁ ≫ pullback.snd q b ≫ ft = pullback.snd q a := by
      simpa using e₁' =≫ pullback.fst a a
    have e₁s : φ₁ ≫ pullback.snd q b ≫ fs = pullback.snd q a := by
      simpa using e₁' =≫ pullback.snd a a
    have e₂t : φ₂ ≫ pullback.snd q b ≫ ft = pullback.snd q b ≫ fs := by
      simpa using e₂' =≫ pullback.fst a a
    have e₂s : φ₂ ≫ pullback.snd q b ≫ fs = pullback.snd q b ≫ ft := by
      simpa using e₂' =≫ pullback.snd a a
    have e₃t : φ₃ ≫ pullback.snd q b ≫ ft =
        pullback.snd q (pullback.fst fs ft ≫ b) ≫ pullback.fst fs ft ≫ ft := by
      simpa using e₃' =≫ pullback.fst a a
    have e₃s : φ₃ ≫ pullback.snd q b ≫ fs =
        pullback.snd q (pullback.fst fs ft ≫ b) ≫ pullback.snd fs ft ≫ fs := by
      simpa using e₃' =≫ pullback.snd a a
    have k₄ : pullback.snd q (pullback.fst Γ Γ ≫ b) ≫ pullback.fst Γ Γ =
        pullback.snd q (pullback.fst Γ Γ ≫ b) ≫ pullback.snd Γ Γ := by
      have h₁ := e₄' =≫ pullback.fst b b
      have h₂ := e₄' =≫ pullback.snd b b
      simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd,
        Category.comp_id, pullback.lift_fst, pullback.lift_snd] at h₁ h₂
      rw [← h₁, ← h₂]
    refine ⟨fun T' g h hgt hgs => ?_, fun T' x => ?_, fun T' r => ?_,
      fun T' r r' e => ?_, het, hes⟩
    · have hf : g ≫ pullback.fst q b = h ≫ pullback.fst q b := by
        simpa using hgt =≫ pullback.fst q a
      have ht : (g ≫ pullback.snd q b) ≫ ft = (h ≫ pullback.snd q b) ≫ ft := by
        simpa using hgt =≫ pullback.snd q a
      have hs : (g ≫ pullback.snd q b) ≫ fs = (h ≫ pullback.snd q b) ≫ fs := by
        simpa using hgs =≫ pullback.snd q a
      let z : T' ⟶ pullback Γ Γ := pullback.lift (g ≫ pullback.snd q b)
        (h ≫ pullback.snd q b) (by apply pullback.hom_ext <;> simpa)
      let y : T' ⟶ pullback q (pullback.fst Γ Γ ≫ b) :=
        pullback.lift (g ≫ pullback.fst q b) z (by simp [z, pullback.condition])
      have := y ≫= k₄
      simp only [y, z, pullback.lift_snd_assoc, pullback.lift_fst, pullback.lift_snd] at this
      exact pullback.hom_ext hf this
    · exact ⟨x ≫ φ₁, by apply pullback.hom_ext <;> simp [e₁, e₁t],
        by apply pullback.hom_ext <;> simp [e₁, e₁s]⟩
    · exact ⟨r ≫ φ₂, by apply pullback.hom_ext <;> simp [e₂, e₂t],
        by apply pullback.hom_ext <;> simp [e₂, e₂s]⟩
    · have hf : r ≫ pullback.fst q b = r' ≫ pullback.fst q b := by
        simpa using e =≫ pullback.fst q a
      have hs : (r ≫ pullback.snd q b) ≫ fs = (r' ≫ pullback.snd q b) ≫ ft := by
        simpa using e =≫ pullback.snd q a
      let z : T' ⟶ pullback fs ft := pullback.lift _ _ hs
      let y : T' ⟶ pullback q (pullback.fst fs ft ≫ b) :=
        pullback.lift (r ≫ pullback.fst q b) z (by simp [z, pullback.condition])
      refine ⟨y ≫ φ₃, ?_, ?_⟩
      · apply pullback.hom_ext
        · simp [e₃, y]
        · simp [e₃t, y, z]
      · apply pullback.hom_ext
        · simp [e₃, y, hf]
        · simp [e₃s, y, z]
  · rintro ⟨hi, hr, hy, hx, het, hes⟩
    refine ⟨?_, ?_, ?_, ?_, het, hes⟩
    · obtain ⟨r, h₁, h₂⟩ := hr _ (𝟙 _)
      refine ⟨r, by simpa using h₁ =≫ pullback.fst q a, ?_⟩
      apply pullback.hom_ext
      · simpa using h₁ =≫ pullback.snd q a
      · simpa using h₂ =≫ pullback.snd q a
    · obtain ⟨r, h₁, h₂⟩ := hy _ (𝟙 _)
      refine ⟨r, by simpa using h₁ =≫ pullback.fst q a, ?_⟩
      apply pullback.hom_ext
      · simpa using h₁ =≫ pullback.snd q a
      · simpa using h₂ =≫ pullback.snd q a
    · have c₁ : pullback.fst q (pullback.fst fs ft ≫ b) ≫ q =
          (pullback.snd q (pullback.fst fs ft ≫ b) ≫ pullback.fst fs ft) ≫ b := by
        rw [pullback.condition, Category.assoc]
      have c₂ : pullback.fst q (pullback.fst fs ft ≫ b) ≫ q =
          (pullback.snd q (pullback.fst fs ft ≫ b) ≫ pullback.snd fs ft) ≫ b := by
        rw [pullback.condition, Category.assoc, pair_cond a b ft fs wt ws]
      let r := pullback.lift (f := q) (g := b) _ _ c₁
      let r' := pullback.lift (f := q) (g := b) _ _ c₂
      obtain ⟨r'', h₁, h₂⟩ := hx _ r r' (by
        apply pullback.hom_ext
        · simp [r, r']
        · simp [r, r', pullback.condition])
      refine ⟨r'', by simpa [r] using h₁ =≫ pullback.fst q a, ?_⟩
      apply pullback.hom_ext
      · simpa [r] using h₁ =≫ pullback.snd q a
      · simpa [r'] using h₂ =≫ pullback.snd q a
    · have c₁ : pullback.fst q (pullback.fst Γ Γ ≫ b) ≫ q =
          (pullback.snd q (pullback.fst Γ Γ ≫ b) ≫ pullback.fst Γ Γ) ≫ b := by
        rw [pullback.condition, Category.assoc]
      have c₂ : pullback.fst q (pullback.fst Γ Γ ≫ b) ≫ q =
          (pullback.snd q (pullback.fst Γ Γ ≫ b) ≫ pullback.snd Γ Γ) ≫ b := by
        rw [pullback.condition, Category.assoc, kernel_cond a b ft fs wt ws]
      let u₁ := pullback.lift (f := q) (g := b) _ _ c₁
      let u₂ := pullback.lift (f := q) (g := b) _ _ c₂
      have hu : u₁ = u₂ := hi _ u₁ u₂
        (by apply pullback.hom_ext <;> simp [u₁, u₂, kernel_ft a b ft fs wt ws])
        (by apply pullback.hom_ext <;> simp [u₁, u₂, kernel_fs a b ft fs wt ws])
      refine ⟨u₁, by simp [u₁], ?_⟩
      apply pullback.hom_ext
      · simp [u₁]
      · conv_lhs => rw [hu]
        simp [u₂]

variable {a b ft fs wt ws} in
/-- The laws persist after further base change. -/
lemma LevelLaws.comp {T T' : Scheme.{u}} {q : T ⟶ S} (r : T' ⟶ T)
    (H : LevelLaws a b ft fs wt ws q) : LevelLaws a b ft fs wt ws (r ≫ q) :=
  ⟨H.1.comp r, H.2.1.comp r, H.2.2.1.comp r, H.2.2.2.1.comp r,
    baseChangeMap_comp_left _ _ _ _ _ _ H.2.2.2.2.1,
    baseChangeMap_comp_left _ _ _ _ _ _ H.2.2.2.2.2⟩

variable {a b ft fs wt ws} in
/-- The laws at a stage persist at every later stage. -/
lemma LevelLaws.level {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}}
    {t : D ⟶ (Functor.const I).obj S} {i j : I} (r : i ⟶ j)
    (H : LevelLaws a b ft fs wt ws (t.app j)) : LevelLaws a b ft fs wt ws (t.app i) := by
  rw [← level_comp D t r]
  exact H.comp _

/-- The laws over the limit of a cofiltered affine diagram already hold at a stage. -/
lemma levelLaws_descend {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ i, IsAffine (D.obj i)] (t : D ⟶ (Functor.const I).obj S)
    (c : Cone D) (hc : IsLimit c) (p : c.pt ⟶ S) (hp : ∀ i, c.π.app i ≫ t.app i = p)
    [IsAffine S] [LocallyOfFinitePresentation a] [QuasiCompact a] [QuasiSeparated a]
    [LocallyOfFinitePresentation b] [QuasiCompact b] [QuasiSeparated b]
    (H : LevelLaws a b ft fs wt ws p) : ∃ i, LevelLaws a b ft fs wt ws (t.app i) := by
  have : LocallyOfFinitePresentation (ft ≫ a) := by rw [wt]; infer_instance
  have : LocallyOfFinitePresentation (fs ≫ a) := by rw [ws]; infer_instance
  have : QuasiCompact (ft ≫ a) := by rw [wt]; infer_instance
  have : QuasiCompact (fs ≫ a) := by rw [ws]; infer_instance
  have : QuasiSeparated (ft ≫ a) := by rw [wt]; infer_instance
  have : QuasiSeparated (fs ≫ a) := by rw [ws]; infer_instance
  have : LocallyOfFinitePresentation ft := Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp ft a
  have : LocallyOfFinitePresentation fs := Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp fs a
  have : QuasiCompact ft := QuasiCompact.of_comp ft a
  have : QuasiCompact fs := QuasiCompact.of_comp fs a
  have : QuasiSeparated ft := QuasiSeparated.of_comp ft a
  have : QuasiSeparated fs := QuasiSeparated.of_comp fs a
  have : LocallyOfFinitePresentation (pullback.fst a a) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : LocallyOfFinitePresentation (pullback.fst b b) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiSeparated (pullback.fst a a) := MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiCompact (pullback.fst fs ft) := MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiSeparated (pullback.fst fs ft) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiCompact (Γ ≫ pullback.fst a a) := by rw [graph_fst]; infer_instance
  have : QuasiSeparated (Γ ≫ pullback.fst a a) := by rw [graph_fst]; infer_instance
  have : QuasiCompact Γ := QuasiCompact.of_comp Γ (pullback.fst a a)
  have : QuasiSeparated Γ := QuasiSeparated.of_comp Γ (pullback.fst a a)
  have : QuasiCompact (pullback.fst Γ Γ) := MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiSeparated (pullback.fst Γ Γ) := MorphismProperty.pullback_fst _ _ inferInstance
  obtain ⟨H₁, H₂, H₃, H₄, H₅, H₆⟩ := H
  obtain ⟨i₁, h₁⟩ := Fact.descend _ _ _ _ D t c hc p hp (graph_model a b ft fs wt ws)
    (by simp) H₁
  obtain ⟨i₂, h₂⟩ := Fact.descend _ _ _ _ D t c hc p hp (graph_model a b ft fs wt ws)
    (by simp [ws]) H₂
  obtain ⟨i₃, h₃⟩ := Fact.descend _ _ _ _ D t c hc p hp (graph_model a b ft fs wt ws)
    (by simp [wt]) H₃
  obtain ⟨i₄, h₄⟩ := Fact.descend _ _ _ _ D t c hc p hp
    (γ := pullback.fst b b ≫ b) (by simp) (by simp) H₄
  obtain ⟨i₅, h₅⟩ := etale_descend a b ft wt D t c hc p hp H₅
  obtain ⟨i₆, h₆⟩ := etale_descend a b fs ws D t c hc p hp H₆
  let k₁ := IsCofiltered.min i₁ i₂
  let k₂ := IsCofiltered.min i₃ i₄
  let k₃ := IsCofiltered.min i₅ i₆
  let k₄ := IsCofiltered.min k₂ k₃
  let k := IsCofiltered.min k₁ k₄
  have r₁ : k ⟶ k₁ := IsCofiltered.minToLeft _ _
  have r₄ : k ⟶ k₄ := IsCofiltered.minToRight _ _
  have r₂ : k ⟶ k₂ := r₄ ≫ IsCofiltered.minToLeft _ _
  have r₃ : k ⟶ k₃ := r₄ ≫ IsCofiltered.minToRight _ _
  exact ⟨k, h₁.level (r₁ ≫ IsCofiltered.minToLeft _ _),
    h₂.level (r₁ ≫ IsCofiltered.minToRight _ _),
    h₃.level (r₂ ≫ IsCofiltered.minToLeft _ _), h₄.level (r₂ ≫ IsCofiltered.minToRight _ _),
    baseChangeMap_level D t _ _ _ _ (r₃ ≫ IsCofiltered.minToLeft _ _) h₅,
    baseChangeMap_level D t _ _ _ _ (r₃ ≫ IsCofiltered.minToRight _ _) h₆⟩

end Models

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.LimitModel
