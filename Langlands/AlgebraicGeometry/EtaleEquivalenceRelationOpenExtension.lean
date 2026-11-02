import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleDistinct
import Langlands.AlgebraicGeometry.Morphisms.OpenCoverLift

/-! # Extending an étale equivalence relation from an open by the identity -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

namespace OpenExtension

variable (E : EtaleEquivalenceRelation.{u}) {V : Scheme.{u}}
    (ι : E.U ⟶ V) [IsOpenImmersion ι]

instance span_isOpenImmersion {i j : WalkingSpan}
    (a : i ⟶ j) : IsOpenImmersion ((span ι E.unit).map a) := by
  cases a <;> dsimp <;> infer_instance

/-- Glue the original arrow scheme to the larger diagonal along the unit. -/
noncomputable abbrev arrows : Scheme.{u} := pushout ι E.unit

/-- The new diagonal inclusion. -/
noncomputable abbrev unit : V ⟶ arrows E ι := pushout.inl ι E.unit

/-- The original relation is an open part of the extension. -/
noncomputable abbrev inclusion : E.R ⟶ arrows E ι := pushout.inr ι E.unit

instance : IsOpenImmersion (unit E ι) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span ι E.unit) WalkingSpan.left))

instance : IsOpenImmersion (inclusion E ι) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span ι E.unit) WalkingSpan.right))

@[reassoc]
lemma unit_inclusion : E.unit ≫ inclusion E ι = ι ≫ unit E ι :=
  (pushout.condition (f := ι) (g := E.unit)).symm

/-- The two charts of the arrow pushout. -/
noncomputable def cover : (arrows E ι).OpenCover where
  I₀ := WalkingPair
  X i := i.casesOn V E.R
  f i := i.casesOn (unit E ι) (inclusion E ι)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, ?_⟩
    · intro x
      obtain ⟨i, y, hy⟩ :=
        Scheme.IsLocallyDirected.ι_jointly_surjective (span ι E.unit) x
      cases i with
      | none =>
          refine ⟨WalkingPair.left, ι y, ?_⟩
          change unit E ι (ι y) = x
          rw [← Scheme.Hom.comp_apply]
          exact (congrArg (fun f => f y)
            (colimit.w (span ι E.unit) WalkingSpan.Hom.fst)).trans hy
      | some i =>
          cases i
          · exact ⟨WalkingPair.left, y, hy⟩
          · exact ⟨WalkingPair.right, y, hy⟩
    · intro i
      cases i <;> dsimp <;> infer_instance

/-- Target endpoint of the extended arrows. -/
noncomputable def t : arrows E ι ⟶ V :=
  pushout.desc (𝟙 V) (E.t ≫ ι) (by simp)

/-- Source endpoint of the extended arrows. -/
noncomputable def s : arrows E ι ⟶ V :=
  pushout.desc (𝟙 V) (E.s ≫ ι) (by simp)

@[reassoc (attr := simp)]
lemma unit_t : unit E ι ≫ t E ι = 𝟙 V := pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma unit_s : unit E ι ≫ s E ι = 𝟙 V := pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma inclusion_t : inclusion E ι ≫ t E ι = E.t ≫ ι := pushout.inr_desc _ _ _

@[reassoc (attr := simp)]
lemma inclusion_s : inclusion E ι ≫ s E ι = E.s ≫ ι := pushout.inr_desc _ _ _

/-- Endpoint uniqueness for maps lying in any two charts of the pushout. -/
lemma chart_hom_ext {T : Scheme.{u}} (i j : (cover E ι).I₀)
    (a : T ⟶ (cover E ι).X i) (b : T ⟶ (cover E ι).X j)
    (ht : (a ≫ (cover E ι).f i) ≫ t E ι = (b ≫ (cover E ι).f j) ≫ t E ι)
    (hs : (a ≫ (cover E ι).f i) ≫ s E ι = (b ≫ (cover E ι).f j) ≫ s E ι) :
    a ≫ (cover E ι).f i = b ≫ (cover E ι).f j := by
  cases i <;> cases j
  · simp only [cover, Category.assoc, unit_t, Category.comp_id] at ht
    exact congrArg (· ≫ unit E ι) ht
  · simp only [cover, Category.assoc, unit_t, unit_s, inclusion_t, inclusion_s,
      Category.comp_id] at ht hs ⊢
    have hb : b ≫ E.t = b ≫ E.s := (cancel_mono ι).mp (ht.symm.trans hs)
    have hu : b = (b ≫ E.t) ≫ E.unit := by
      apply E.hom_ext <;> simp [hb]
    rw [hu, Category.assoc, unit_inclusion]
    simpa only [Category.assoc] using congrArg (fun z => z ≫ unit E ι) ht
  · simp only [cover, Category.assoc, unit_t, unit_s, inclusion_t, inclusion_s,
      Category.comp_id] at ht hs ⊢
    have ha : a ≫ E.t = a ≫ E.s := (cancel_mono ι).mp (ht.trans hs.symm)
    have hu : a = (a ≫ E.t) ≫ E.unit := by
      apply E.hom_ext <;> simp [ha]
    rw [hu, Category.assoc, unit_inclusion]
    simpa only [Category.assoc] using congrArg (fun z => z ≫ unit E ι) ht
  · have hab : a = b := by
      apply E.hom_ext
      · apply (cancel_mono ι).mp
        simpa [cover] using ht
      · apply (cancel_mono ι).mp
        simpa [cover] using hs
    exact congrArg (· ≫ inclusion E ι) hab

/-- The extended arrow scheme is still a monic relation. -/
lemma hom_ext {T : Scheme.{u}} {a b : T ⟶ arrows E ι}
    (ht : a ≫ t E ι = b ≫ t E ι) (hs : a ≫ s E ι = b ≫ s E ι) : a = b := by
  let C := cover E ι
  apply Scheme.Cover.hom_ext (C.pullback₁ a) _ _
  intro i
  apply Scheme.Cover.hom_ext (C.pullback₁ (pullback.fst a (C.f i) ≫ b)) _ _
  intro j
  let w := pullback.fst (pullback.fst a (C.f i) ≫ b) (C.f j)
  have ha : (w ≫ pullback.fst a (C.f i)) ≫ a =
      (w ≫ pullback.snd a (C.f i)) ≫ C.f i := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
  have hb : (w ≫ pullback.fst a (C.f i)) ≫ b =
      pullback.snd (pullback.fst a (C.f i) ≫ b) (C.f j) ≫ C.f j := by
    rw [Category.assoc]
    exact pullback.condition
  change w ≫ (pullback.fst a (C.f i) ≫ a) =
    w ≫ (pullback.fst a (C.f i) ≫ b)
  simp only [← Category.assoc, ha, hb]
  apply chart_hom_ext E ι i j
  · rw [← ha, ← hb]
    simp only [Category.assoc, ht]
  · rw [← ha, ← hb]
    simp only [Category.assoc, hs]

instance mono_pair : Mono (prod.lift (t E ι) (s E ι)) where
  right_cancellation := by
    intro T a b h
    apply hom_ext E ι
    · simpa using congrArg (· ≫ prod.fst) h
    · simpa using congrArg (· ≫ prod.snd) h

/-- Reverse the original arrows and fix the new diagonal. -/
noncomputable def inverse : arrows E ι ⟶ arrows E ι :=
  pushout.desc (unit E ι) (E.inverse ≫ inclusion E ι) (by
    have h : E.unit ≫ E.inverse = E.unit := by
      apply E.hom_ext <;> simp
    rw [← Category.assoc, h, unit_inclusion])

@[reassoc (attr := simp)]
lemma unit_inverse : unit E ι ≫ inverse E ι = unit E ι := pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma inclusion_inverse :
    inclusion E ι ≫ inverse E ι = E.inverse ≫ inclusion E ι := pushout.inr_desc _ _ _

@[reassoc (attr := simp)]
lemma inverse_t : inverse E ι ≫ t E ι = s E ι := by
  apply pushout.hom_ext <;> simp

@[reassoc (attr := simp)]
lemma inverse_s : inverse E ι ≫ s E ι = t E ι := by
  apply pushout.hom_ext <;> simp

/-- A pair of endpoints lifts globally if it lifts on an open cover. -/
lemma exists_endpoints_of_openCover {T : Scheme.{u}} (C : T.OpenCover)
    (x y : T ⟶ V)
    (h : ∀ i, ∃ r : C.X i ⟶ arrows E ι,
      r ≫ t E ι = C.f i ≫ x ∧ r ≫ s E ι = C.f i ≫ y) :
    ∃ r : T ⟶ arrows E ι, r ≫ t E ι = x ∧ r ≫ s E ι = y := by
  obtain ⟨r, hr⟩ := Langlands.AlgebraicGeometry.exists_lift_of_openCover
    (prod.lift (t E ι) (s E ι)) (prod.lift x y) C (fun i => by
      obtain ⟨r, ht, hs⟩ := h i
      exact ⟨r, by apply prod.hom_ext <;> simp [ht, hs]⟩)
  exact ⟨r, by simpa using congrArg (· ≫ prod.fst) hr,
    by simpa using congrArg (· ≫ prod.snd) hr⟩

/-- Transitivity for arrows in any two charts of the pushout. -/
lemma chart_trans {T : Scheme.{u}} (i j : (cover E ι).I₀)
    (a : T ⟶ (cover E ι).X i) (b : T ⟶ (cover E ι).X j)
    (h : (a ≫ (cover E ι).f i) ≫ s E ι =
      (b ≫ (cover E ι).f j) ≫ t E ι) :
    ∃ r : T ⟶ arrows E ι,
      r ≫ t E ι = (a ≫ (cover E ι).f i) ≫ t E ι ∧
      r ≫ s E ι = (b ≫ (cover E ι).f j) ≫ s E ι := by
  cases i <;> cases j
  · exact ⟨a ≫ unit E ι, rfl, by simpa [cover] using h⟩
  · refine ⟨b ≫ inclusion E ι, ?_, rfl⟩
    simpa [cover] using h.symm
  · refine ⟨a ≫ inclusion E ι, rfl, ?_⟩
    simpa [cover] using h
  · have hab : a ≫ E.s = b ≫ E.t := by
      apply (cancel_mono ι).mp
      simpa [cover] using h
    exact ⟨E.compose a b hab ≫ inclusion E ι, by simp [cover], by simp [cover]⟩

/-- Transitivity is local twice, once for each input arrow. -/
lemma trans {T : Scheme.{u}} (a b : T ⟶ arrows E ι)
    (h : a ≫ s E ι = b ≫ t E ι) :
    ∃ r : T ⟶ arrows E ι, r ≫ t E ι = a ≫ t E ι ∧
      r ≫ s E ι = b ≫ s E ι := by
  let C := cover E ι
  apply exists_endpoints_of_openCover E ι (C.pullback₁ a)
  intro i
  let p := pullback.fst a (C.f i)
  apply exists_endpoints_of_openCover E ι (C.pullback₁ (p ≫ b))
  intro j
  let w := pullback.fst (p ≫ b) (C.f j)
  let a' := w ≫ pullback.snd a (C.f i)
  let b' := pullback.snd (p ≫ b) (C.f j)
  have ha : a' ≫ C.f i = (w ≫ p) ≫ a := by
    dsimp [a', p]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
  have hb : b' ≫ C.f j = (w ≫ p) ≫ b := by
    dsimp [b', w]
    simpa only [Category.assoc] using
      (pullback.condition (f := p ≫ b) (g := C.f j)).symm
  have hab : (a' ≫ C.f i) ≫ s E ι = (b' ≫ C.f j) ≫ t E ι := by
    rw [ha, hb]
    simp only [Category.assoc, h]
  obtain ⟨r, ht, hs⟩ := chart_trans E ι i j a' b' hab
  refine ⟨r, ?_, ?_⟩
  · change r ≫ t E ι = w ≫ p ≫ a ≫ t E ι
    exact ht.trans (by rw [ha]; simp only [Category.assoc])
  · change r ≫ s E ι = w ≫ p ≫ b ≫ s E ι
    exact hs.trans (by rw [hb]; simp only [Category.assoc])

instance etale_t : Etale (t E ι) := by
  have : IsZariskiLocalAtSource @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  apply IsZariskiLocalAtSource.of_openCover (P := @Etale.{u}) (cover E ι)
  intro i
  cases i <;> dsimp only [cover]
  · rw [unit_t]
    infer_instance
  · rw [inclusion_t]
    let := E.etale_t
    infer_instance

instance etale_s : Etale (s E ι) := by
  have : IsZariskiLocalAtSource @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  apply IsZariskiLocalAtSource.of_openCover (P := @Etale.{u}) (cover E ι)
  intro i
  cases i <;> dsimp only [cover]
  · rw [unit_s]
    infer_instance
  · rw [inclusion_s]
    let := E.etale_s
    infer_instance

/-- Extend the relation by the diagonal outside the original open scheme. -/
noncomputable def relation : EtaleEquivalenceRelation.{u} where
  U := V
  R := arrows E ι
  t := t E ι
  s := s E ι
  mono_lift := inferInstance
  refl T a := ⟨a ≫ unit E ι, by simp, by simp⟩
  symm T a := ⟨a ≫ inverse E ι, by simp, by simp⟩
  trans T a b h := trans E ι a b h
  etale_t := inferInstance
  etale_s := inferInstance

/-- An extended arrow whose source is in the old open lies in the old relation. -/
lemma exists_lift_of_source {T : Scheme.{u}}
    (a : T ⟶ arrows E ι) (b : T ⟶ E.U) (h : a ≫ s E ι = b ≫ ι) :
    ∃ r : T ⟶ E.R, r ≫ inclusion E ι = a ∧ r ≫ E.s = b := by
  let C := cover E ι
  obtain ⟨r, hr⟩ := Langlands.AlgebraicGeometry.exists_lift_of_openCover
    (inclusion E ι) a (C.pullback₁ a) (by
    intro i
    have hc : (pullback.snd a (C.f i) ≫ C.f i) ≫ s E ι =
        pullback.fst a (C.f i) ≫ b ≫ ι := by
      rw [← pullback.condition]
      simp only [Category.assoc, h]
    cases i
    · simp only [C, cover, Category.assoc, unit_s, Category.comp_id] at hc
      refine ⟨pullback.fst a (unit E ι) ≫ b ≫ E.unit, ?_⟩
      change (pullback.fst a (unit E ι) ≫ b ≫ E.unit) ≫ inclusion E ι =
        pullback.fst a (unit E ι) ≫ a
      simpa only [Category.assoc, unit_inclusion, hc] using
        (pullback.condition (f := a) (g := unit E ι)).symm
    · exact ⟨pullback.snd a (inclusion E ι), pullback.condition.symm⟩)
  refine ⟨r, hr, ?_⟩
  apply (cancel_mono ι).mp
  rw [Category.assoc, ← inclusion_s, ← Category.assoc, hr, h]

/-- Restriction of the extension along the original open recovers the relation. -/
lemma isPullback_source : IsPullback (inclusion E ι) E.s (s E ι) ι := by
  refine IsPullback.of_isLimit' ⟨inclusion_s E ι⟩ ?_
  apply PullbackCone.IsLimit.mk _
    (fun c => (exists_lift_of_source E ι c.fst c.snd c.condition).choose)
  · intro c
    exact (exists_lift_of_source E ι c.fst c.snd c.condition).choose_spec.1
  · intro c
    exact (exists_lift_of_source E ι c.fst c.snd c.condition).choose_spec.2
  · intro c m hm _
    apply (cancel_mono (inclusion E ι)).mp
    exact hm.trans (exists_lift_of_source E ι c.fst c.snd c.condition).choose_spec.1.symm

/-- The old relation maps cartesianly into its extension. -/
lemma isCartesianHom : IsCartesianHom E (relation E ι) ι (inclusion E ι) :=
  ⟨inclusion_t E ι, isPullback_source E ι⟩

end OpenExtension

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
