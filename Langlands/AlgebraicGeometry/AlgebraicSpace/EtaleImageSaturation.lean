import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorImages
import Langlands.AlgebraicGeometry.EtaleOffDiagonal
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Diagonal and off-diagonal saturation of an etale chart image -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleImageSaturation

variable {S : Scheme.{u}}

private theorem localClosure_mono {F : Presheaf S} {A B : Subfunctor F}
    (h : A ≤ B) :
    A.sheafify (fppfTopology S) ≤ B.sheafify (fppfTopology S) := by
  intro T x hx
  exact (fppfTopology S).superset_covering (fun U f hf => h _ hf) hx

set_option backward.isDefEq.respectTransparency false in
/-- Computing a local image can be done on two open pieces covering its source. -/
theorem sheafify_range_eq_sup {F : Presheaf S}
    (hF : CategoryTheory.Presheaf.IsSheaf (fppfTopology S) F)
    {P V W : Over S} (b : (schemeYoneda S).obj P ⟶ F)
    (d : V ⟶ P) (j : W ⟶ P)
    [_root_.AlgebraicGeometry.IsOpenImmersion d.left]
    [_root_.AlgebraicGeometry.IsOpenImmersion j.left]
    (hcover : ∀ z : P.left, z ∈ Set.range d.left ∨ z ∈ Set.range j.left) :
    (Subfunctor.range b).sheafify (fppfTopology S) =
      (Subfunctor.range ((schemeYoneda S).map d ≫ b) ⊔
        Subfunctor.range ((schemeYoneda S).map j ≫ b)).sheafify (fppfTopology S) := by
  let U : Bool → Over S | false => V | true => W
  let q : ∀ i, U i ⟶ P | false => d | true => j
  let : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion (q i).left := by
    intro i
    cases i <;> assumption
  let 𝒰 := Scheme.Cover.mkOfCovers
    (P := @_root_.AlgebraicGeometry.IsOpenImmersion.{u}) Bool
    (fun i => (U i).left) (fun i => (q i).left) (by
      intro z
      rcases hcover z with ⟨v, hv⟩ | ⟨w, hw⟩
      · exact ⟨false, v, hv⟩
      · exact ⟨true, w, hw⟩)
  have hq : Sieve.ofArrows U q ∈ fppfTopology S P := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact (Precoverage.toGrothendieck_mono
      Scheme.zariskiPrecoverage_le_fppfPrecoverage) _ 𝒰.mem_grothendieckTopology
  let A := Subfunctor.range ((schemeYoneda S).map d ≫ b) ⊔
    Subfunctor.range ((schemeYoneda S).map j ≫ b)
  have hsection : b.app (op P) (ULift.up (𝟙 P)) ∈
      (A.sheafify (fppfTopology S)).obj (op P) := by
    apply (fppfTopology S).superset_covering ?_ hq
    rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    change F.map (q i).op (b.app (op P) (ULift.up (𝟙 P))) ∈ A.obj (op (U i))
    rw [← b.naturality_apply (q i).op]
    cases i
    · refine Or.inl ⟨ULift.up (𝟙 V), ?_⟩
      change b.app (op V) (ULift.up (𝟙 V ≫ d)) = b.app (op V) (ULift.up d)
      rw [Category.id_comp]
    · refine Or.inr ⟨ULift.up (𝟙 W), ?_⟩
      change b.app (op W) (ULift.up (𝟙 W ≫ j)) = b.app (op W) (ULift.up j)
      rw [Category.id_comp]
  have hle : Subfunctor.range b ≤ A.sheafify (fppfTopology S) := by
    rintro T x ⟨⟨r⟩, rfl⟩
    have hr := (A.sheafify (fppfTopology S)).map r.op hsection
    change F.map r.op (b.app (op P) (ULift.up (𝟙 P))) ∈
      (A.sheafify (fppfTopology S)).obj T at hr
    rw [← b.naturality_apply r.op] at hr
    simpa using hr
  apply le_antisymm
  · exact Subfunctor.sheafify_le (Subfunctor.range b)
      (A.sheafify (fppfTopology S)) hle
      ((CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).mp hF)
      (A.sheafify_isSheaf ((CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).mp hF))
  · apply localClosure_mono
    apply sup_le
    · rintro T x ⟨y, rfl⟩
      exact ⟨((schemeYoneda S).map d).app T y, rfl⟩
    · rintro T x ⟨y, rfl⟩
      exact ⟨((schemeYoneda S).map j).app T y, rfl⟩

variable {B T : Over S} (e : B ⟶ T)

/-- The actual self-relation of the etale base change, over the fixed base. -/
def relation : Over S :=
  Over.mk (pullback.fst e.left e.left ≫ B.hom)

def left : relation e ⟶ B :=
  Over.homMk (pullback.fst e.left e.left)

def right : relation e ⟶ B :=
  Over.homMk (pullback.snd e.left e.left) (by
    dsimp [relation]
    rw [← Over.w e, ← Category.assoc, ← pullback.condition, Category.assoc])

theorem relation_isPullback : IsPullback (left e) (right e) e e := by
  apply IsPullback.of_map_of_faithful (Over.forget S)
  exact IsPullback.of_hasPullback e.left e.left

def diagonal : B ⟶ relation e :=
  Over.homMk (pullback.diagonal e.left) (by simp [relation])

@[reassoc (attr := simp)]
theorem diagonal_left : diagonal e ≫ left e = 𝟙 B := by
  ext
  exact pullback.diagonal_fst _

@[reassoc (attr := simp)]
theorem diagonal_right : diagonal e ≫ right e = 𝟙 B := by
  ext
  exact pullback.diagonal_snd _

instance [Etale e.left] :
    _root_.AlgebraicGeometry.IsOpenImmersion (diagonal e).left :=
  inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion (pullback.diagonal e.left))

/-- The off-diagonal scheme with its original structure morphism. -/
def off [IsSeparated e.left] : Over S :=
  Over.mk (EtaleOffDiagonal.projection e.left ≫ B.hom)

def offι [IsSeparated e.left] : off e ⟶ relation e :=
  Over.homMk (EtaleOffDiagonal.openComplement e.left).ι

instance [IsSeparated e.left] :
    _root_.AlgebraicGeometry.IsOpenImmersion (offι e).left :=
  inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion
    (EtaleOffDiagonal.openComplement e.left).ι)

variable {V : Over S} (w : V ⟶ B)

/-- The scheme of all translates of the chart source. -/
abbrev chartRelation : Over S := Limits.pullback (right e) w

def diagonalChart : V ⟶ chartRelation e w :=
  pullback.lift (w ≫ diagonal e) (𝟙 V) (by simp)

@[reassoc (attr := simp)]
theorem diagonalChart_fst :
    diagonalChart e w ≫ pullback.fst (right e) w = w ≫ diagonal e :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem diagonalChart_snd :
    diagonalChart e w ≫ pullback.snd (right e) w = 𝟙 V :=
  pullback.lift_snd _ _ _

theorem diagonalChart_isPullback :
    IsPullback w (diagonalChart e w) (diagonal e) (pullback.fst (right e) w) := by
  have houter : IsPullback w
      (diagonalChart e w ≫ pullback.snd (right e) w)
      (diagonal e ≫ right e) w := by
    simp only [diagonalChart_snd, diagonal_right]
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  exact houter.of_bot (diagonalChart_fst e w).symm
    (IsPullback.of_hasPullback (right e) w)

instance [Etale e.left] :
    _root_.AlgebraicGeometry.IsOpenImmersion (diagonalChart e w).left :=
  MorphismProperty.of_isPullback
    (P := @_root_.AlgebraicGeometry.IsOpenImmersion.{u})
    ((diagonalChart_isPullback e w).map (Over.forget S))
    (inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion (diagonal e).left))

/-- The actual base change of the chart source to the off-diagonal. -/
abbrev offChart [IsSeparated e.left] : Over S := Limits.pullback (offι e ≫ right e) w

def offChartι [IsSeparated e.left] : offChart e w ⟶ chartRelation e w :=
  pullback.lift (pullback.fst (offι e ≫ right e) w ≫ offι e)
    (pullback.snd (offι e ≫ right e) w) (by
      simpa only [Category.assoc] using
        pullback.condition (f := offι e ≫ right e) (g := w))

@[reassoc (attr := simp)]
theorem offChartι_fst [IsSeparated e.left] :
    offChartι e w ≫ pullback.fst (right e) w =
      pullback.fst (offι e ≫ right e) w ≫ offι e :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem offChartι_snd [IsSeparated e.left] :
    offChartι e w ≫ pullback.snd (right e) w =
      pullback.snd (offι e ≫ right e) w :=
  pullback.lift_snd _ _ _

theorem offChartι_isPullback [IsSeparated e.left] :
    IsPullback (pullback.fst (offι e ≫ right e) w) (offChartι e w)
      (offι e) (pullback.fst (right e) w) := by
  have houter : IsPullback (pullback.fst (offι e ≫ right e) w)
      (offChartι e w ≫ pullback.snd (right e) w) (offι e ≫ right e) w := by
    rw [offChartι_snd]
    exact IsPullback.of_hasPullback _ _
  exact houter.of_bot (offChartι_fst e w).symm
    (IsPullback.of_hasPullback (right e) w)

instance [Etale e.left] [IsSeparated e.left] :
    _root_.AlgebraicGeometry.IsOpenImmersion (offChartι e w).left :=
  MorphismProperty.of_isPullback
    (P := @_root_.AlgebraicGeometry.IsOpenImmersion.{u})
    ((offChartι_isPullback e w).map (Over.forget S))
    (inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion (offι e).left))

/-- The original chart and the off-diagonal part cover the translate source. -/
theorem diagonal_off_cover [Etale e.left] [IsSeparated e.left]
    (z : (chartRelation e w).left) :
    z ∈ Set.range (diagonalChart e w).left ∨
      z ∈ Set.range (offChartι e w).left := by
  classical
  by_cases hz : (pullback.fst (right e) w).left z ∈
      Set.range (diagonal e).left
  · obtain ⟨b, hb⟩ := hz
    obtain ⟨v, _, hv⟩ := Scheme.exists_preimage_of_isPullback
      ((diagonalChart_isPullback e w).map (Over.forget S)) b z hb
    exact Or.inl ⟨v, hv⟩
  · have hz' : (pullback.fst (right e) w).left z ∈ Set.range (offι e).left := by
      change _ ∈ Set.range (EtaleOffDiagonal.openComplement e.left).ι
      rw [Scheme.Opens.range_ι]
      exact hz
    obtain ⟨b, hb⟩ := hz'
    obtain ⟨v, _, hv⟩ := Scheme.exists_preimage_of_isPullback
      ((offChartι_isPullback e w).map (Over.forget S)) b z hb
    exact Or.inr ⟨v, hv⟩

/-- The base point of a translate is the first coordinate of the relation. -/
abbrev newBase : chartRelation e w ⟶ B :=
  pullback.fst (right e) w ≫ left e

theorem chartRelation_isPullback :
    IsPullback (pullback.snd (right e) w) (newBase e w) (w ≫ e) e :=
  ((IsPullback.of_hasPullback (right e) w).paste_horiz (relation_isPullback e)).flip

variable {F G : Presheaf S}
    {π : G ⟶ F} {p : G ⟶ (schemeYoneda S).obj B}
    {f : F ⟶ (schemeYoneda S).obj T}
    (sq : IsPullback π p f ((schemeYoneda S).map e))
    (a : (schemeYoneda S).obj V ⟶ G)
    (ha : a ≫ p = (schemeYoneda S).map w)

/-- Transport the chart to the first coordinate, using the given base-change square. -/
def translate : (schemeYoneda S).obj (chartRelation e w) ⟶ G :=
  sq.lift ((schemeYoneda S).map (pullback.snd (right e) w) ≫ a ≫ π)
    ((schemeYoneda S).map (newBase e w)) (by
      have hh := congrArg ((schemeYoneda S).map) (chartRelation_isPullback e w).w
      simpa only [Functor.map_comp, ← ha, Category.assoc, sq.w] using hh)

@[reassoc (attr := simp)]
theorem translate_π :
    translate e w sq a ha ≫ π =
      (schemeYoneda S).map (pullback.snd (right e) w) ≫ a ≫ π :=
  sq.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem translate_p :
    translate e w sq a ha ≫ p = (schemeYoneda S).map (newBase e w) :=
  sq.lift_snd _ _ _

/-- The transported chart is the actual pullback of the original chart image. -/
theorem translate_isPullback :
    IsPullback ((schemeYoneda S).map (pullback.snd (right e) w))
      (translate e w sq a ha) (a ≫ π) π := by
  have hcomp : (a ≫ π) ≫ f = (schemeYoneda S).map (w ≫ e) := by
    rw [Category.assoc, sq.w, ← Category.assoc, ha, Functor.map_comp]
  have houter : IsPullback ((schemeYoneda S).map (pullback.snd (right e) w))
      (translate e w sq a ha ≫ p) ((a ≫ π) ≫ f) ((schemeYoneda S).map e) := by
    rw [translate_p, hcomp]
    exact (chartRelation_isPullback e w).map (schemeYoneda S)
  exact houter.of_bot (translate_π e w sq a ha).symm sq

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem diagonalChart_translate :
    (schemeYoneda S).map (diagonalChart e w) ≫ translate e w sq a ha = a := by
  apply sq.hom_ext
  · rw [Category.assoc, translate_π, ← Functor.map_comp_assoc,
      diagonalChart_snd]
    rw [(schemeYoneda S).map_id V, Category.id_comp]
  · rw [Category.assoc, translate_p, ← Functor.map_comp, ha]
    apply congrArg ((schemeYoneda S).map)
    dsimp only [newBase]
    rw [← Category.assoc, diagonalChart_fst, Category.assoc, diagonal_left,
      Category.comp_id]

/-- The inverse image of the local chart image is the local union of the
original chart and its off-diagonal translates. -/
theorem saturation_eq [Etale e.left] [IsSeparated e.left]
    (hG : CategoryTheory.Presheaf.IsSheaf (fppfTopology S) G) :
    ((Subfunctor.range (a ≫ π)).sheafify (fppfTopology S)).preimage π =
      (Subfunctor.range a ⊔ Subfunctor.range
        ((schemeYoneda S).map (offChartι e w) ≫ translate e w sq a ha)).sheafify
          (fppfTopology S) := by
  rw [← OpenSubfunctorImages.sheafify_preimage,
    ← OpenSubfunctorLifting.range_eq_preimage_of_isPullback
      (translate_isPullback e w sq a ha)]
  have h := sheafify_range_eq_sup hG (translate e w sq a ha)
    (diagonalChart e w) (offChartι e w) (diagonal_off_cover e w)
  rwa [diagonalChart_translate] at h

end Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleImageSaturation
