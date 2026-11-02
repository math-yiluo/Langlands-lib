import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationOpenExtension

/-! # Cartesian comparison of open extensions -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.OpenExtension.Comparison

variable {E F : EtaleEquivalenceRelation.{u}}
    {f : E.U ⟶ F.U} {g : E.R ⟶ F.R}
    {V W : Scheme.{u}} (ι : E.U ⟶ V) (κ : F.U ⟶ W)
    [IsOpenImmersion ι] [IsOpenImmersion κ] (v : V ⟶ W)
    (ht : g ≫ F.t = E.t ≫ f) (hs : g ≫ F.s = E.s ≫ f)
    (w : ι ≫ v = f ≫ κ)

include ht hs in
/-- An endpoint-preserving map of relations preserves the unit. -/
lemma unit_naturality : E.unit ≫ g = f ≫ F.unit := by
  apply F.hom_ext <;> simp [ht, hs]

/-- The induced map on the actual pushouts of arrow schemes. -/
noncomputable def map : arrows E ι ⟶ arrows F κ :=
  pushout.desc (v ≫ unit F κ) (g ≫ inclusion F κ) (by
    calc
      ι ≫ v ≫ unit F κ = f ≫ κ ≫ unit F κ := by rw [← Category.assoc, w]; simp
      _ = f ≫ F.unit ≫ inclusion F κ := by rw [unit_inclusion]
      _ = E.unit ≫ g ≫ inclusion F κ := by
        rw [← Category.assoc, ← unit_naturality ht hs, Category.assoc])

@[reassoc (attr := simp)]
lemma unit_map : unit E ι ≫ map ι κ v ht hs w = v ≫ unit F κ :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma inclusion_map : inclusion E ι ≫ map ι κ v ht hs w = g ≫ inclusion F κ :=
  pushout.inr_desc _ _ _

@[reassoc (attr := simp)]
lemma map_t : map ι κ v ht hs w ≫ t F κ = t E ι ≫ v := by
  apply pushout.hom_ext
  · simp
  · simp only [inclusion_map_assoc, inclusion_t, inclusion_t_assoc]
    rw [← Category.assoc, ht, Category.assoc, ← w]

@[reassoc (attr := simp)]
lemma map_s : map ι κ v ht hs w ≫ s F κ = s E ι ≫ v := by
  apply pushout.hom_ext
  · simp
  · simp only [inclusion_map_assoc, inclusion_s, inclusion_s_assoc]
    rw [← Category.assoc, hs, Category.assoc, ← w]

variable {ι κ v}

/-- A diagonal arrow and an old arrow with equal images and sources agree. -/
lemma diagonal_old_hom_ext (h : IsCartesianHom E F f g) {T : Scheme.{u}}
    (a : T ⟶ V) (b : T ⟶ E.R)
    (hm : (a ≫ unit E ι) ≫ map ι κ v h.1 h.2.w w =
      (b ≫ inclusion E ι) ≫ map ι κ v h.1 h.2.w w)
    (hs : (a ≫ unit E ι) ≫ s E ι = (b ≫ inclusion E ι) ≫ s E ι) :
    a ≫ unit E ι = b ≫ inclusion E ι := by
  have hab : a = b ≫ E.s ≫ ι := by simpa using hs
  have hbg : b ≫ g = (b ≫ E.s) ≫ f ≫ F.unit := by
    apply (cancel_mono (inclusion F κ)).mp
    calc
      (b ≫ g) ≫ inclusion F κ = (a ≫ v) ≫ unit F κ := by
        simpa using hm.symm
      _ = ((b ≫ E.s) ≫ f ≫ F.unit) ≫ inclusion F κ := by
        simp only [hab, Category.assoc, w, unit_inclusion]
  have hb : b = (b ≫ E.s) ≫ E.unit := by
    apply h.2.hom_ext
    · simpa only [Category.assoc, unit_naturality h.1 h.2.w] using hbg
    · simp
  calc
    a ≫ unit E ι = ((b ≫ E.s) ≫ E.unit) ≫ inclusion E ι := by
      simp only [hab, Category.assoc, unit_inclusion]
    _ = b ≫ inclusion E ι := by rw [← hb]

/-- Uniqueness in the source square, checked in each pair of pushout charts. -/
lemma chart_hom_ext (h : IsCartesianHom E F f g) {T : Scheme.{u}}
    (i j : (cover E ι).I₀)
    (a : T ⟶ (cover E ι).X i) (b : T ⟶ (cover E ι).X j)
    (hm : (a ≫ (cover E ι).f i) ≫ map ι κ v h.1 h.2.w w =
      (b ≫ (cover E ι).f j) ≫ map ι κ v h.1 h.2.w w)
    (hs : (a ≫ (cover E ι).f i) ≫ s E ι =
      (b ≫ (cover E ι).f j) ≫ s E ι) :
    a ≫ (cover E ι).f i = b ≫ (cover E ι).f j := by
  cases i <;> cases j
  · have hab : a = b := by simpa [cover] using hs
    exact congrArg (· ≫ unit E ι) hab
  · exact diagonal_old_hom_ext w h a b hm hs
  · exact (diagonal_old_hom_ext w h b a hm.symm hs.symm).symm
  · have hab : a = b := by
      apply h.2.hom_ext
      · apply (cancel_mono (inclusion F κ)).mp
        simpa [cover] using hm
      · apply (cancel_mono ι).mp
        simpa [cover] using hs
    exact congrArg (· ≫ inclusion E ι) hab

/-- The comparison map and the source determine a map to the extension. -/
lemma hom_ext (h : IsCartesianHom E F f g) {T : Scheme.{u}}
    {a b : T ⟶ arrows E ι}
    (hm : a ≫ map ι κ v h.1 h.2.w w = b ≫ map ι κ v h.1 h.2.w w)
    (hs : a ≫ s E ι = b ≫ s E ι) : a = b := by
  let C := cover E ι
  apply Scheme.Cover.hom_ext (C.pullback₁ a) _ _
  intro i
  apply Scheme.Cover.hom_ext (C.pullback₁ (pullback.fst a (C.f i) ≫ b)) _ _
  intro j
  let z := pullback.fst (pullback.fst a (C.f i) ≫ b) (C.f j)
  have ha : (z ≫ pullback.fst a (C.f i)) ≫ a =
      (z ≫ pullback.snd a (C.f i)) ≫ C.f i := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
  have hb : (z ≫ pullback.fst a (C.f i)) ≫ b =
      pullback.snd (pullback.fst a (C.f i) ≫ b) (C.f j) ≫ C.f j := by
    rw [Category.assoc]
    exact pullback.condition
  change z ≫ (pullback.fst a (C.f i) ≫ a) =
    z ≫ (pullback.fst a (C.f i) ≫ b)
  simp only [← Category.assoc, ha, hb]
  apply chart_hom_ext w h i j
  · rw [← ha, ← hb]
    simp only [Category.assoc, hm]
  · rw [← ha, ← hb]
    simp only [Category.assoc, hs]

/-- The comparison-source pair is monic before any cartesianness assumption
on the square of open immersions. -/
lemma mono_pair (h : IsCartesianHom E F f g) :
    Mono (prod.lift (map ι κ v h.1 h.2.w w) (s E ι)) where
  right_cancellation := by
    intro T a b hab
    apply hom_ext w h
    · simpa using congrArg (· ≫ prod.fst) hab
    · simpa using congrArg (· ≫ prod.snd) hab

/-- A compatible arrow and source lift on either chart of the lower extension. -/
lemma chart_exists_lift (h : IsCartesianHom E F f g)
    (hv : IsPullback f ι κ v) {T : Scheme.{u}}
    (i : (cover F κ).I₀) (a : T ⟶ (cover F κ).X i) (b : T ⟶ V)
    (hw : (a ≫ (cover F κ).f i) ≫ s F κ = b ≫ v) :
    ∃ r : T ⟶ arrows E ι, r ≫ map ι κ v h.1 h.2.w w =
      a ≫ (cover F κ).f i ∧ r ≫ s E ι = b := by
  cases i
  · have hab : a = b ≫ v := by simpa [cover] using hw
    exact ⟨b ≫ unit E ι, by simp [cover, hab], by simp⟩
  · have hu : (a ≫ F.s) ≫ κ = b ≫ v := by simpa [cover] using hw
    let x := hv.lift (a ≫ F.s) b hu
    have hxf : x ≫ f = a ≫ F.s := hv.lift_fst _ _ _
    have hxι : x ≫ ι = b := hv.lift_snd _ _ _
    let r := h.2.lift a x hxf.symm
    have hrg : r ≫ g = a := h.2.lift_fst _ _ _
    have hrs : r ≫ E.s = x := h.2.lift_snd _ _ _
    refine ⟨r ≫ inclusion E ι, ?_, ?_⟩
    · simpa only [cover, Category.assoc, inclusion_map] using
        congrArg (· ≫ inclusion F κ) hrg
    · rw [Category.assoc, inclusion_s, ← Category.assoc, hrs, hxι]

/-- Local lifts glue to a global lift in the source comparison square. -/
lemma exists_lift (h : IsCartesianHom E F f g) (hv : IsPullback f ι κ v)
    {T : Scheme.{u}} (a : T ⟶ arrows F κ) (b : T ⟶ V)
    (hw : a ≫ s F κ = b ≫ v) :
    ∃ r : T ⟶ arrows E ι,
      r ≫ map ι κ v h.1 h.2.w w = a ∧ r ≫ s E ι = b := by
  let C := cover F κ
  let := mono_pair w h
  obtain ⟨r, hr⟩ := Langlands.AlgebraicGeometry.exists_lift_of_openCover
    (prod.lift (map ι κ v h.1 h.2.w w) (s E ι)) (prod.lift a b) (C.pullback₁ a) (by
      intro i
      have hl : (pullback.snd a (C.f i) ≫ C.f i) ≫ s F κ =
          (pullback.fst a (C.f i) ≫ b) ≫ v := by
        rw [← pullback.condition]
        simp only [Category.assoc, hw]
      obtain ⟨r, hm, hs⟩ := chart_exists_lift w h hv i
        (pullback.snd a (C.f i)) (pullback.fst a (C.f i) ≫ b) hl
      refine ⟨r, ?_⟩
      change r ≫ prod.lift (map ι κ v h.1 h.2.w w) (s E ι) =
        pullback.fst a (C.f i) ≫ prod.lift a b
      apply prod.hom_ext
      · simpa only [Category.assoc, prod.lift_fst, Category.comp_id] using
          hm.trans pullback.condition.symm
      · simpa only [Category.assoc, prod.lift_snd, Category.comp_id] using hs)
  exact ⟨r, by simpa using congrArg (· ≫ prod.fst) hr,
    by simpa using congrArg (· ≫ prod.snd) hr⟩

/-- Cartesian morphisms extend cartesianly over a pullback square of opens. -/
lemma isPullback_source (h : IsCartesianHom E F f g)
    (hv : IsPullback f ι κ v) :
    IsPullback (map ι κ v h.1 h.2.w w) (s E ι) (s F κ) v := by
  refine IsPullback.mk' (map_s _ _ _ _ _ _) ?_ ?_
  · intro T a b hm hs
    exact hom_ext w h hm hs
  · intro T a b hw
    exact exists_lift w h hv a b hw

/-- The induced relation morphism between open extensions is cartesian. -/
lemma isCartesianHom (h : IsCartesianHom E F f g)
    (hv : IsPullback f ι κ v) :
    IsCartesianHom (relation E ι) (relation F κ) v
      (map ι κ v h.1 h.2.w w) :=
  ⟨map_t _ _ _ _ _ _, isPullback_source w h hv⟩

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.OpenExtension.Comparison
