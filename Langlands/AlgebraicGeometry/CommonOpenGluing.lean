import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Gluing schemes along a common open subscheme

Given schemes `U j` (for `j` in an index type `J`), a scheme `W` and open immersions
`g j : W ⟶ U j`, glue the `U j` by identifying the copies `g j (W)` of `W`. This is the special
case of Mathlib's `Scheme.GlueData` in which every overlap is `W` and every transition map is the
identity of `W`; the cocycle conditions then hold trivially.

The glued scheme `glued U W g` has open immersions `ι j : U j ⟶ glued U W g` with
`g i ≫ ι i = g j ≫ ι j`. For `i ≠ j` the overlap of `U i` and `U j` is exactly `W`: two maps
`a : T ⟶ U i` and `b : T ⟶ U j` with the same composite to the glued scheme factor through `W`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.AlgebraicGeometry.CommonOpenGluing

open _root_.AlgebraicGeometry

/-- In a pullback of a monomorphism with itself, the two projections agree. -/
theorem pullback_fst_eq_snd {X Y : Scheme.{u}} (h : X ⟶ Y) [Mono h] :
    pullback.fst h h = pullback.snd h h :=
  (cancel_mono h).1 pullback.condition

variable {J : Type u} (U : J → Scheme.{u}) (W : Scheme.{u}) (g : ∀ j, W ⟶ U j)
  [hg : ∀ j, IsOpenImmersion (g j)]

include hg

/-- The gluing data with every overlap `W` and every transition map the identity of `W`. -/
abbrev glueData' : CategoryTheory.GlueData' Scheme.{u} where
  J := J
  U := U
  V _ _ _ := W
  f i _ _ := g i
  t _ _ _ := 𝟙 W
  t' i j _ _ _ _ := pullback.lift (pullback.fst (g i) (g i)) (pullback.fst (g i) (g i)) rfl
  t_fac i j k _ _ _ := by
    rw [pullback.lift_snd, Category.comp_id]
  t_inv _ _ _ := Category.comp_id _
  cocycle i j k _ _ _ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_fst, Category.id_comp]
      exact pullback_fst_eq_snd (g i)

theorem f'_isOpenImmersion (i j : J) : IsOpenImmersion ((glueData' U W g).f' i j) := by
  classical
  dsimp only [CategoryTheory.GlueData'.f']
  split_ifs with h
  · infer_instance
  · have := hg i
    infer_instance

/-- The scheme gluing data. -/
def glueData : Scheme.GlueData.{u} where
  toGlueData := CategoryTheory.GlueData.ofGlueData' (glueData' U W g)
  f_open i j := f'_isOpenImmersion U W g i j

/-- The glued scheme. -/
abbrev glued : Scheme.{u} := (glueData U W g).glued

/-- The open immersion of the `j`-th piece into the glued scheme. -/
abbrev ι (j : J) : U j ⟶ glued U W g := (glueData U W g).ι j

instance (j : J) : IsOpenImmersion (ι U W g j) :=
  Scheme.GlueData.ι_isOpenImmersion (glueData U W g) j


/-- Away from the diagonal, the inclusion of the overlap is the inclusion of `W`. -/
theorem f_eq {i j : J} (h : i ≠ j) :
    (glueData U W g).f i j = eqToHom (dite_eq_right h) ≫ g i := by
  simp [glueData, CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', h]

/-- Away from the diagonal, the transition map followed by the inclusion is the inclusion of
`W` into the other piece. -/
theorem tf_eq {i j : J} (h : i ≠ j) :
    (glueData U W g).t i j ≫ (glueData U W g).f j i = eqToHom (dite_eq_right h) ≫ g j := by
  simp [glueData, CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', h,
    Ne.symm h]

/-- The copies of `W` in the pieces are identified in the glued scheme. -/
theorem g_ι (i j : J) : g i ≫ ι U W g i = g j ≫ ι U W g j := by
  by_cases hij : i = j
  · subst hij
    rfl
  · have h := (glueData U W g).glue_condition i j
    have e1 := (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ ι U W g j) (tf_eq U W g hij)).trans (Category.assoc _ _ _))
    have e2 := (congrArg (· ≫ ι U W g i) (f_eq U W g hij)).trans (Category.assoc _ _ _)
    exact ((cancel_epi (eqToHom (dite_eq_right hij))).1 (e1.symm.trans (h.trans e2))).symm

/-- For `i ≠ j`, two maps into the pieces `U i` and `U j` with the same image in the glued
scheme come from a map into the common open `W`. -/
theorem exists_of_comp_eq {i j : J} (hij : i ≠ j) {T : Scheme.{u}} (a : T ⟶ U i) (b : T ⟶ U j)
    (h : a ≫ ι U W g i = b ≫ ι U W g j) : ∃ w : T ⟶ W, w ≫ g i = a ∧ w ≫ g j = b := by
  have hlim := (glueData U W g).vPullbackConeIsLimit i j
  let l := PullbackCone.IsLimit.lift hlim a b h
  have hl₁ : l ≫ (glueData U W g).f i j = a := PullbackCone.IsLimit.lift_fst hlim a b h
  have hl₂ : l ≫ (glueData U W g).t i j ≫ (glueData U W g).f j i = b :=
    PullbackCone.IsLimit.lift_snd hlim a b h
  refine ⟨l ≫ eqToHom (dite_eq_right hij), ?_, ?_⟩
  · exact (Category.assoc _ _ _).trans ((congrArg (l ≫ ·) (f_eq U W g hij)).symm.trans hl₁)
  · exact (Category.assoc _ _ _).trans
      ((congrArg (l ≫ ·) (tf_eq U W g hij)).symm.trans ((Category.assoc _ _ _).symm.trans hl₂))

/-- A morphism from the glued scheme is determined by its restrictions to the pieces. -/
theorem hom_ext {Y : Scheme.{u}} {φ ψ : glued U W g ⟶ Y}
    (h : ∀ j, ι U W g j ≫ φ = ι U W g j ≫ ψ) : φ = ψ :=
  Scheme.Cover.hom_ext (glueData U W g).openCover φ ψ h

variable {U W g}

/-- Morphisms from the pieces that agree on the common open glue to a morphism from the glued
scheme. -/
def desc {Y : Scheme.{u}} (m : ∀ j, U j ⟶ Y) (hm : ∀ i j, g i ≫ m i = g j ≫ m j) :
    glued U W g ⟶ Y :=
  Scheme.Cover.glueMorphisms (glueData U W g).openCover m fun (i j : J) => by
    change pullback.fst (ι U W g i) (ι U W g j) ≫ m i =
      pullback.snd (ι U W g i) (ι U W g j) ≫ m j
    by_cases hij : i = j
    · subst hij
      rw [pullback_fst_eq_snd]
    · obtain ⟨w, hw₁, hw₂⟩ := exists_of_comp_eq U W g hij (pullback.fst _ _) (pullback.snd _ _)
        pullback.condition
      rw [← hw₁, ← hw₂, Category.assoc, Category.assoc, hm]

@[reassoc (attr := simp)]
theorem ι_desc {Y : Scheme.{u}} (m : ∀ j, U j ⟶ Y) (hm : ∀ i j, g i ≫ m i = g j ≫ m j)
    (j : J) : ι U W g j ≫ desc m hm = m j :=
  Scheme.Cover.ι_glueMorphisms (glueData U W g).openCover m _ j

/-- Every point of the glued scheme lies in one of the pieces. -/
theorem exists_ι_apply (x : glued U W g) : ∃ (j : J) (y : U j), ι U W g j y = x :=
  (glueData U W g).ι_jointly_surjective x

variable (U W g) in
/-- The pieces form an open cover of the glued scheme. -/
theorem isOpenCover_opensRange :
    TopologicalSpace.IsOpenCover fun j : J => (ι U W g j).opensRange := by
  refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr fun x _ => ?_)
  obtain ⟨j, y, rfl⟩ := exists_ι_apply x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨j, y, rfl⟩

variable (U W g) in
/-- For different pieces, the intersection of their images is the image of `W`. -/
theorem opensRange_inter_opensRange {i j : J} (hij : i ≠ j) :
    ((ι U W g i).opensRange ∩ (ι U W g j).opensRange : Set (glued U W g)) =
      Set.range (g i ≫ ι U W g i) := by
  apply le_antisymm
  · intro x hx
    simp only [Scheme.Hom.coe_opensRange] at hx
    rw [← _root_.AlgebraicGeometry.IsOpenImmersion.range_pullback_to_base_of_left] at hx
    obtain ⟨z, rfl⟩ := hx
    obtain ⟨w, hw, -⟩ := exists_of_comp_eq U W g hij
      (pullback.fst (ι U W g i) (ι U W g j)) (pullback.snd _ _) pullback.condition
    refine ⟨w z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, hw]
  · rintro _ ⟨w, rfl⟩
    refine ⟨⟨(g i) w, rfl⟩, ?_⟩
    rw [g_ι U W g i j]
    exact ⟨(g j) w, rfl⟩

variable (U W g) in
/-- If `W` and the pieces are quasi-compact, pairwise intersections of the pieces are
quasi-compact. -/
theorem isCompact_opensRange_inter [CompactSpace W] [∀ j, CompactSpace (U j)] (i j : J) :
    IsCompact ((ι U W g i).opensRange ∩ (ι U W g j).opensRange : Set (glued U W g)) := by
  by_cases hij : i = j
  · subst hij
    simp only [Set.inter_self, Scheme.Hom.coe_opensRange]
    exact isCompact_range (ι U W g i).continuous
  · rw [opensRange_inter_opensRange U W g hij]
    exact isCompact_range (g i ≫ ι U W g i).continuous

/-- Gluing affine schemes along a quasi-compact common open gives a quasi-separated scheme. -/
instance quasiSeparatedSpace [∀ j, IsAffine (U j)] [CompactSpace W] :
    QuasiSeparatedSpace (glued U W g) :=
  Scheme.quasiSeparatedSpace_of_isOpenCover _ (isOpenCover_opensRange U W g)
    (fun j => isAffineOpen_opensRange (ι U W g j)) (isCompact_opensRange_inter U W g)

/-- A morphism from the spectrum of a local ring to the glued scheme factors through one of the
pieces: the piece containing the image of the closed point contains the whole image. -/
theorem exists_lift_of_isLocalRing {S : Type u} [CommRing S] [IsLocalRing S]
    (x : Spec (CommRingCat.of S) ⟶ glued U W g) :
    ∃ (j : J) (a : Spec (CommRingCat.of S) ⟶ U j), a ≫ ι U W g j = x := by
  obtain ⟨j, y, hy⟩ := exists_ι_apply (x (IsLocalRing.closedPoint S))
  have hrange : Set.range x ⊆ Set.range (ι U W g j) := by
    rintro _ ⟨z, rfl⟩
    have h := ((IsLocalRing.specializes_closedPoint z).map x.continuous).mem_open
      (ι U W g j).opensRange.isOpen ⟨y, hy⟩
    exact h
  exact ⟨j, _root_.AlgebraicGeometry.IsOpenImmersion.lift (ι U W g j) x hrange,
    _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _⟩

end Langlands.AlgebraicGeometry.CommonOpenGluing
