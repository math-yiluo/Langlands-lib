/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartBoundaryLine
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace

/-!
# The diagonal of the projective line

For a scheme `S` put `P = ℙ(n; S)`. Projective space commutes with base change
(`AlgebraicGeometry.ProjectiveSpace.isPullback_map`), so `ℙ(n; P)` is the fibre product
`P ×_S P`, with first projection the structure morphism `ℙ(n; P) ⟶ P` and second projection
`map n (P ↘ S) : ℙ(n; P) ⟶ P`. The diagonal `P ⟶ P ×_S P` is then a section of
`ℙ(n; P) ⟶ P` (`AlgebraicGeometry.ProjectiveSpace.diagonal`).

More generally, a morphism `g : T ⟶ P` has a graph `T ⟶ ℙ(n; T)`
(`AlgebraicGeometry.ProjectiveSpace.graph`), the base change of the diagonal along
`map n g : ℙ(n; T) ⟶ ℙ(n; P)` (`AlgebraicGeometry.ProjectiveSpace.isPullback_graph_diagonal`).

For the projective line `ℙ¹_S = ℙ(Option (ULift (Fin 1)); S)` we record:

* the graph of the section at infinity `ι : Z ⟶ ℙ¹_S` is the section at infinity of `ℙ¹_Z`
  (`AlgebraicGeometry.ProjectiveSpace.graph_lineInfinityι`), so the base change of the diagonal
  along `map ι` is the section at infinity
  (`AlgebraicGeometry.ProjectiveSpace.isPullback_lineInfinityι_diagonal`);
* near the point `(∞, ∞)` the diagonal is cut out by one equation: on the chart
  `𝔸¹_{𝔸¹_S} ⟶ ℙ¹_{ℙ¹_S}` (the chart at infinity of the base and of the fibre), the diagonal is
  the zero locus of `z - t`, `z` the fibre coordinate and `t` the base coordinate
  (`AlgebraicGeometry.ProjectiveSpace.isPullback_zeroLocusSubschemeι_diagonal`);
* the chart at infinity of `ℙ¹_Z` maps to this chart, pulling `z - t` back to the coordinate
  `T_∞ / T₀` (`AlgebraicGeometry.ProjectiveSpace.lineInfinityDiagonalLift`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace CategoryTheory.IsPullback

variable {C : Type*} [Category C] {X' X B' B : C} {g' : X' ⟶ X} {p' : X' ⟶ B'} {p : X ⟶ B}
  {g : B' ⟶ B}

/-- **Sections pull back.** In a pullback square `g' ≫ p = p' ≫ g`, the base change
`σ' = (g ≫ σ, 𝟙)` of a section `σ` of `p` is a section of `p'`, and `σ` pulls back to it: the
square `g ≫ σ = σ' ≫ g'` is cartesian. -/
lemma lift_section (h : IsPullback g' p' p g) (σ : B ⟶ X) (hσ : σ ≫ p = 𝟙 B) :
    IsPullback g (h.lift (g ≫ σ) (𝟙 B') (by rw [Category.assoc, hσ, Category.comp_id,
      Category.id_comp])) σ g' :=
  IsPullback.of_bot (by
    rw [IsPullback.lift_snd, hσ]
    exact IsPullback.id_vert g) (h.lift_fst _ _ _).symm h

end CategoryTheory.IsPullback

namespace AlgebraicGeometry.ProjectiveSpace

variable (n : Type u)

/-- Two morphisms into `ℙ(n; T)` agreeing over `T` and after `map n h` for some `h : T ⟶ S` are
equal. -/
lemma hom_ext_map {X T S : Scheme.{u}} (h : T ⟶ S) {f₁ f₂ : X ⟶ ℙ(n; T)}
    (h₁ : f₁ ≫ ℙ(n; T) ↘ T = f₂ ≫ ℙ(n; T) ↘ T) (h₂ : f₁ ≫ map n h = f₂ ≫ map n h) :
    f₁ = f₂ :=
  hom_ext n T h₁ (by rw [← map_toProjInt n h, reassoc_of% h₂])

variable (S : Scheme.{u})

/-- The *diagonal* of `P = ℙ(n; S)`, as a section of `ℙ(n; P) ⟶ P`. Under
`ℙ(n; P) ≅ P ×_S P` (`AlgebraicGeometry.ProjectiveSpace.isPullback_map`), whose projections are
the structure morphism and `map n (P ↘ S)`, it is the diagonal `P ⟶ P ×_S P`. -/
def diagonal : ℙ(n; S) ⟶ ℙ(n; ℙ(n; S)) :=
  (isPullback_map n (ℙ(n; S) ↘ S)).lift (𝟙 _) (𝟙 _) rfl

@[reassoc (attr := simp)]
lemma diagonal_over : diagonal n S ≫ ℙ(n; ℙ(n; S)) ↘ ℙ(n; S) = 𝟙 _ :=
  IsPullback.lift_snd _ _ _ _

@[reassoc (attr := simp)]
lemma diagonal_map : diagonal n S ≫ map n (ℙ(n; S) ↘ S) = 𝟙 _ :=
  IsPullback.lift_fst _ _ _ _

/-- `ℙ(n; P) ≅ P ×_S P` for `P = ℙ(n; S)`, with first projection the structure morphism
`ℙ(n; P) ⟶ P` and second projection `map n (P ↘ S)`
(`AlgebraicGeometry.ProjectiveSpace.isPullback_map`). -/
def isoPullback : ℙ(n; ℙ(n; S)) ≅ pullback (ℙ(n; S) ↘ S) (ℙ(n; S) ↘ S) :=
  (isPullback_map n (ℙ(n; S) ↘ S)).flip.isoPullback

@[reassoc (attr := simp)]
lemma isoPullback_hom_fst :
    (isoPullback n S).hom ≫ pullback.fst _ _ = ℙ(n; ℙ(n; S)) ↘ ℙ(n; S) :=
  IsPullback.isoPullback_hom_fst _

@[reassoc (attr := simp)]
lemma isoPullback_hom_snd :
    (isoPullback n S).hom ≫ pullback.snd _ _ = map n (ℙ(n; S) ↘ S) :=
  IsPullback.isoPullback_hom_snd _

/-- Under `ℙ(n; P) ≅ P ×_S P`, the diagonal is the diagonal of `P ⟶ S`. -/
@[reassoc (attr := simp)]
lemma diagonal_isoPullback_hom :
    diagonal n S ≫ (isoPullback n S).hom = pullback.diagonal (ℙ(n; S) ↘ S) := by
  ext <;> simp

variable {n S}

/-- The *graph* `T ⟶ ℙ(n; T)` of a morphism `g : T ⟶ ℙ(n; S)`: the section of `ℙ(n; T) ⟶ T`
whose composite with `map n g` is `g ≫ diagonal`, i.e. whose composite with
`map n (g ≫ ℙ(n; S) ↘ S)` is `g`. -/
def graph {T : Scheme.{u}} (g : T ⟶ ℙ(n; S)) : T ⟶ ℙ(n; T) :=
  (isPullback_map n g).lift (g ≫ diagonal n S) (𝟙 T) (by simp)

@[reassoc (attr := simp)]
lemma graph_over {T : Scheme.{u}} (g : T ⟶ ℙ(n; S)) : graph g ≫ ℙ(n; T) ↘ T = 𝟙 T :=
  IsPullback.lift_snd _ _ _ _

@[reassoc (attr := simp)]
lemma graph_map {T : Scheme.{u}} (g : T ⟶ ℙ(n; S)) : graph g ≫ map n g = g ≫ diagonal n S :=
  IsPullback.lift_fst _ _ _ _

/-- The graph of `g` is the section of `ℙ(n; T) ⟶ T` whose composite with
`map n (g ≫ ℙ(n; S) ↘ S)` is `g`. -/
lemma eq_graph {T : Scheme.{u}} (g : T ⟶ ℙ(n; S)) (f : T ⟶ ℙ(n; T))
    (h₁ : f ≫ ℙ(n; T) ↘ T = 𝟙 T) (h₂ : f ≫ map n (g ≫ ℙ(n; S) ↘ S) = g) : f = graph g :=
  hom_ext_map n (g ≫ ℙ(n; S) ↘ S) (by rw [h₁, graph_over]) (by
    rw [h₂, map_comp, graph_map_assoc, diagonal_map, Category.comp_id])

/-- **The base change of the diagonal along `map n g` is the graph of `g`.** -/
lemma isPullback_graph_diagonal {T : Scheme.{u}} (g : T ⟶ ℙ(n; S)) :
    IsPullback g (graph g) (diagonal n S) (map n g) :=
  (isPullback_map n g).lift_section (diagonal n S) (diagonal_over n S)

/-- The graph of a morphism `ι : Z ⟶ ℙ(n; S)` that is a section over `S` up to the isomorphism
`ι ≫ ℙ(n; S) ↘ S`, compared with a section `ι' : Z' ⟶ ℙ(n; Z)` lying over `ι` (through
`gZ : Z' ⟶ Z`). -/
lemma graph_eq_of_isIso {Z Z' : Scheme.{u}} (ι : Z ⟶ ℙ(n; S)) (ι' : Z' ⟶ ℙ(n; Z))
    [IsIso (ι ≫ ℙ(n; S) ↘ S)] [IsIso (ι' ≫ ℙ(n; Z) ↘ Z)] (gZ : Z' ⟶ Z)
    (hgZ : gZ ≫ ι = ι' ≫ map n (ι ≫ ℙ(n; S) ↘ S)) :
    graph ι = inv (ι' ≫ ℙ(n; Z) ↘ Z) ≫ ι' := by
  symm
  refine eq_graph _ _ (by rw [Category.assoc, IsIso.inv_hom_id]) ?_
  have hg : inv (ι' ≫ ℙ(n; Z) ↘ Z) ≫ gZ = 𝟙 Z := by
    rw [← cancel_mono (ι ≫ ℙ(n; S) ↘ S), Category.assoc, reassoc_of% hgZ, map_over,
      ← Category.assoc ι', IsIso.inv_hom_id_assoc, Category.id_comp]
  rw [Category.assoc, ← hgZ, reassoc_of% hg]

variable (n S) in
/-- The automorphism of `ℙ(n; ℙ(n; S)) ≅ P ×_S P` exchanging the two factors: it exchanges the
structure morphism `ℙ(n; P) ⟶ P` and `map n (P ↘ S)`. -/
def diagonalSwap : ℙ(n; ℙ(n; S)) ⟶ ℙ(n; ℙ(n; S)) :=
  (isPullback_map n (ℙ(n; S) ↘ S)).lift (ℙ(n; ℙ(n; S)) ↘ ℙ(n; S)) (map n (ℙ(n; S) ↘ S))
    (map_over n _).symm

variable (n S) in
@[reassoc (attr := simp)]
lemma diagonalSwap_over :
    diagonalSwap n S ≫ ℙ(n; ℙ(n; S)) ↘ ℙ(n; S) = map n (ℙ(n; S) ↘ S) :=
  IsPullback.lift_snd _ _ _ _

variable (n S) in
@[reassoc (attr := simp)]
lemma diagonalSwap_map :
    diagonalSwap n S ≫ map n (ℙ(n; S) ↘ S) = ℙ(n; ℙ(n; S)) ↘ ℙ(n; S) :=
  IsPullback.lift_fst _ _ _ _

variable (n S) in
@[reassoc (attr := simp)]
lemma diagonalSwap_diagonalSwap : diagonalSwap n S ≫ diagonalSwap n S = 𝟙 _ :=
  hom_ext_map n (ℙ(n; S) ↘ S) (by simp) (by simp)

instance : IsIso (diagonalSwap n S) :=
  ⟨diagonalSwap n S, diagonalSwap_diagonalSwap n S, diagonalSwap_diagonalSwap n S⟩

variable (n S) in
/-- The exchange of the factors fixes the diagonal. -/
@[reassoc (attr := simp)]
lemma diagonal_diagonalSwap : diagonal n S ≫ diagonalSwap n S = diagonal n S :=
  hom_ext_map n (ℙ(n; S) ↘ S) (by simp) (by simp)

section Line

variable (S)

/-- The section at infinity of `ℙ¹_S`, as an isomorphism `S ⟶ Z` onto the zero locus `Z` of
`T_∞ / T₀`; composed with `AlgebraicGeometry.ProjectiveSpace.lineInfinityι` it is a section of
`ℙ¹_S ⟶ S`. -/
def lineInfinitySection : S ⟶ lineInfinity S :=
  inv (lineInfinityι S ≫ ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)

instance : IsIso (lineInfinitySection S) := by
  rw [lineInfinitySection]
  infer_instance

/-- **The graph of the section at infinity is the section at infinity.** For the section at
infinity `ι : Z ⟶ ℙ¹_S`, the graph `Z ⟶ ℙ¹_Z` of `ι` is the section at infinity of `ℙ¹_Z`. -/
lemma graph_lineInfinityι :
    graph (lineInfinityι S) = lineInfinitySection (lineInfinity S) ≫
      lineInfinityι (lineInfinity S) := by
  obtain ⟨gZ, hgZ⟩ := exists_isPullback_lineInfinityι_map
    (lineInfinityι S ≫ ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)
  exact graph_eq_of_isIso _ _ gZ hgZ.w


/-- **The diagonal meets `ℙ¹_Z` in its section at infinity.** For the section at infinity
`ι : Z ⟶ ℙ¹_S`, the base change of the diagonal of `ℙ¹_S` along `map ι : ℙ¹_Z ⟶ ℙ¹_{ℙ¹_S}` is
the section at infinity of `ℙ¹_Z`. -/
lemma isPullback_lineInfinityι_diagonal :
    IsPullback (inv (lineInfinitySection (lineInfinity S)) ≫ lineInfinityι S)
      (lineInfinityι (lineInfinity S)) (diagonal (Option (ULift.{u} (Fin 1))) S)
      (map (Option (ULift.{u} (Fin 1))) (lineInfinityι S)) :=
  (isPullback_graph_diagonal (lineInfinityι S)).of_iso
    (asIso (lineInfinitySection (lineInfinity S))) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp [graph_lineInfinityι]) (by simp) (by simp)

/-- The coordinate `z - t` on `𝔸¹_{𝔸¹_S}`: the fibre coordinate `z` minus the pullback `t` of
the coordinate of the base `𝔸¹_S`. -/
def diagonalChartEquation : Γ(𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin 1); S)), ⊤) :=
  AffineSpace.coord _ (ULift.up 0) -
    (𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin 1); S)) ↘ 𝔸(ULift.{u} (Fin 1); S)).appTop
      (AffineSpace.coord S (ULift.up 0))

/-- The diagonal section `t ↦ (t, t)` of `𝔸¹_{𝔸¹_S} ⟶ 𝔸¹_S`. -/
def affineLineDiagonal : 𝔸(ULift.{u} (Fin 1); S) ⟶ 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin 1); S)) :=
  AffineSpace.homOfVector (𝟙 _) fun _ ↦ AffineSpace.coord S (ULift.up 0)

/-- The translation `z ↦ z - t` of `𝔸¹_{𝔸¹_S}` over `𝔸¹_S`. -/
def diagonalTranslation :
    𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin 1); S)) ⟶ 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin 1); S)) :=
  AffineSpace.homOfVector (𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin 1); S)) ↘ 𝔸(ULift.{u} (Fin 1); S))
    fun _ ↦ diagonalChartEquation S

/-- The translation `z ↦ z + t` of `𝔸¹_{𝔸¹_S}` over `𝔸¹_S`, inverse to
`AlgebraicGeometry.ProjectiveSpace.diagonalTranslation`. -/
def diagonalTranslationInv :
    𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin 1); S)) ⟶ 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin 1); S)) :=
  AffineSpace.homOfVector (𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin 1); S)) ↘ 𝔸(ULift.{u} (Fin 1); S))
    fun _ ↦ AffineSpace.coord _ (ULift.up 0) +
      (𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin 1); S)) ↘ 𝔸(ULift.{u} (Fin 1); S)).appTop
        (AffineSpace.coord S (ULift.up 0))

lemma diagonalTranslation_inv :
    diagonalTranslation S ≫ diagonalTranslationInv S = 𝟙 _ := by
  refine AffineSpace.hom_ext (by simp [diagonalTranslation, diagonalTranslationInv]) fun i ↦ ?_
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, diagonalTranslationInv,
    AffineSpace.homOfVector_appTop_coord, map_add, diagonalTranslation,
    AffineSpace.homOfVector_appTop_coord, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    AffineSpace.homOfVector_over, diagonalChartEquation, Subsingleton.elim i (ULift.up 0)]
  simp

lemma diagonalTranslationInv_hom :
    diagonalTranslationInv S ≫ diagonalTranslation S = 𝟙 _ := by
  refine AffineSpace.hom_ext (by simp [diagonalTranslation, diagonalTranslationInv]) fun i ↦ ?_
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, diagonalTranslation,
    AffineSpace.homOfVector_appTop_coord, diagonalChartEquation, map_sub, diagonalTranslationInv,
    AffineSpace.homOfVector_appTop_coord, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    AffineSpace.homOfVector_over, Subsingleton.elim i (ULift.up 0)]
  simp

instance : IsIso (diagonalTranslation S) :=
  ⟨diagonalTranslationInv S, diagonalTranslation_inv S, diagonalTranslationInv_hom S⟩

/-- The translation `z ↦ z - t` carries the diagonal section to the zero section. -/
lemma affineLineDiagonal_diagonalTranslation :
    affineLineDiagonal S ≫ diagonalTranslation S =
      AffineSpace.zeroSection (ULift.{u} (Fin 1)) 𝔸(ULift.{u} (Fin 1); S) := by
  refine AffineSpace.hom_ext (by simp [affineLineDiagonal, diagonalTranslation]) fun i ↦ ?_
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, diagonalTranslation,
    AffineSpace.homOfVector_appTop_coord, diagonalChartEquation, map_sub, affineLineDiagonal,
    AffineSpace.homOfVector_appTop_coord, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    AffineSpace.homOfVector_over, AffineSpace.zeroSection_appTop_coord]
  simp

/-- **The diagonal of `𝔸¹_S` is cut out by `z - t`.** -/
lemma isPullback_zeroLocusSubschemeι_affineLineDiagonal :
    ∃ w, IsPullback w (𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin 1); S)).zeroLocusSubschemeι
      (Set.range fun _ : Fin 1 ↦ diagonalChartEquation S)) (affineLineDiagonal S) (𝟙 _) := by
  have hs : (diagonalTranslation S).appTop '' {AffineSpace.coord _ (ULift.up 0)} =
      Set.range fun _ : Fin 1 ↦ diagonalChartEquation S := by
    rw [Set.image_singleton, Set.range_const, diagonalTranslation,
      AffineSpace.homOfVector_appTop_coord]
  have h₁ := Scheme.isPullback_zeroLocusSubschemeι (diagonalTranslation S) _ _ hs
  let e := AffineSpace.zeroSectionIsoZeroLocusSubscheme (ULift.{u} (Fin 1))
    𝔸(ULift.{u} (Fin 1); S) (s := {AffineSpace.coord _ (ULift.up 0)}) Set.range_unique
  have he : e.hom ≫ 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin 1); S)).zeroLocusSubschemeι
      {AffineSpace.coord _ (ULift.up 0)} = AffineSpace.zeroSection _ _ :=
    AffineSpace.zeroSectionIsoZeroLocusSubscheme_hom_zeroLocusSubschemeι _ _ _
  have h₂ : IsPullback (Scheme.Hom.zeroLocusSubschemeMap _ _ _ hs ≫ e.inv)
      (𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin 1); S)).zeroLocusSubschemeι
        (Set.range fun _ : Fin 1 ↦ diagonalChartEquation S))
      (affineLineDiagonal S ≫ diagonalTranslation S) (diagonalTranslation S) :=
    h₁.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id, affineLineDiagonal_diagonalTranslation,
        ← he,
        Iso.inv_hom_id_assoc]) (by simp)
  refine ⟨_, IsPullback.of_right (h₁₂ := 𝟙 _) (h₂₂ := diagonalTranslation S)
    (by simpa using h₂) ?_ (IsPullback.of_horiz_isIso_mono ⟨by simp⟩)⟩
  rw [← cancel_mono (diagonalTranslation S), Category.assoc, h₂.w, Category.comp_id]

/-- The chart `𝔸¹_{𝔸¹_S} ⟶ ℙ¹_{ℙ¹_S}` at the point `(∞, ∞)`: the chart at infinity of the fibre
over the chart at infinity `𝔸¹_S ⟶ ℙ¹_S` of the base. -/
def diagonalChart : 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin 1); S)) ⟶
    ℙ(Option (ULift.{u} (Fin 1)); ℙ(Option (ULift.{u} (Fin 1)); S)) :=
  lineInfinityChart 𝔸(ULift.{u} (Fin 1); S) ≫
    map (Option (ULift.{u} (Fin 1))) (lineInfinityChart S)

instance : IsOpenImmersion (map (Option (ULift.{u} (Fin 1))) (lineInfinityChart S)) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (isPullback_map (Option (ULift.{u} (Fin 1))) (lineInfinityChart S)).flip inferInstance

instance : IsOpenImmersion (diagonalChart S) := by
  rw [diagonalChart]
  infer_instance

/-- The graph of the chart at infinity `𝔸¹_S ⟶ ℙ¹_S` is the diagonal `t ↦ (t, t)` of `𝔸¹_S`
followed by the chart at infinity of `ℙ¹_{𝔸¹_S}`. -/
lemma graph_lineInfinityChart :
    graph (lineInfinityChart S) = affineLineDiagonal S ≫ lineInfinityChart _ := by
  symm
  refine eq_graph _ _ (by rw [Category.assoc, lineInfinityChart_over, affineLineDiagonal,
    AffineSpace.homOfVector_over]) ?_
  rw [lineInfinityChart_over, Category.assoc, ← map_comp_lineInfinityChart, ← Category.assoc,
    affineLineDiagonal, AffineSpace.homOfVector_comp_map, Category.id_comp,
    homOfVector_over_coord_uLift, Category.id_comp]

/-- **A chart of the diagonal at `(∞, ∞)`.** Along the chart
`AlgebraicGeometry.ProjectiveSpace.diagonalChart`, the diagonal of `ℙ¹_S` is the zero locus of
`z - t` (`AlgebraicGeometry.ProjectiveSpace.diagonalChartEquation`). -/
lemma exists_isPullback_diagonalChart :
    ∃ toZ, IsPullback toZ (𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin 1); S)).zeroLocusSubschemeι
      (Set.range fun _ : Fin 1 ↦ diagonalChartEquation S))
      (diagonal (Option (ULift.{u} (Fin 1))) S) (diagonalChart S) := by
  have h₁ := isPullback_graph_diagonal (lineInfinityChart S)
  rw [graph_lineInfinityChart] at h₁
  have h₀ : IsPullback (𝟙 _) (affineLineDiagonal S) (affineLineDiagonal S ≫ lineInfinityChart _)
      (lineInfinityChart _) := IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  obtain ⟨w, hw⟩ := isPullback_zeroLocusSubschemeι_affineLineDiagonal S
  have h := hw.paste_horiz (h₀.paste_horiz h₁)
  rw [Category.id_comp, Category.id_comp] at h
  exact ⟨_, h⟩

/-- The inverse of the chart at infinity pulls the coordinate of `𝔸¹_B` back to `T_∞ / T₀`. -/
lemma inv_lineInfinityChartToOpen_appTop (B : Scheme.{u}) :
    (inv (lineInfinityChartToOpen B)).appTop (AffineSpace.coord B (ULift.up 0)) =
      lineInfinityCoord B := by
  rw [← lineInfinityChartToOpen_appTop B, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    IsIso.inv_hom_id, Scheme.Hom.id_appTop, CommRingCat.id_apply]

/-- The section at infinity `Z ⟶ ℙ¹_S` factors through the chart at infinity `𝔸¹_S ⟶ ℙ¹_S`, as
the zero locus of the coordinate. -/
def lineInfinityToAffine : lineInfinity S ⟶ 𝔸(ULift.{u} (Fin 1); S) :=
  (lineInfinityOpen S).toScheme.zeroLocusSubschemeι {lineInfinityCoord S} ≫
    inv (lineInfinityChartToOpen S)

lemma lineInfinityToAffine_lineInfinityChart :
    lineInfinityToAffine S ≫ lineInfinityChart S = lineInfinityι S := by
  rw [lineInfinityToAffine, Category.assoc, ← lineInfinityChartToOpen_ι, IsIso.inv_hom_id_assoc]

lemma lineInfinityToAffine_appTop :
    (lineInfinityToAffine S).appTop (AffineSpace.coord S (ULift.up 0)) = 0 := by
  rw [lineInfinityToAffine, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    inv_lineInfinityChartToOpen_appTop]
  exact Scheme.zeroLocusSubschemeι_appTop (Set.mem_singleton _)

/-- The chart at infinity of `ℙ¹_Z`, for the section at infinity `ι : Z ⟶ ℙ¹_S`, mapped to the
chart `AlgebraicGeometry.ProjectiveSpace.diagonalChart` at `(∞, ∞)` of `ℙ¹_{ℙ¹_S}`. -/
def lineInfinityDiagonalLift :
    (lineInfinityOpen (lineInfinity S)).toScheme ⟶ 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin 1); S)) :=
  inv (lineInfinityChartToOpen (lineInfinity S)) ≫
    AffineSpace.map (ULift.{u} (Fin 1)) (lineInfinityToAffine S)

lemma lineInfinityDiagonalLift_diagonalChart :
    lineInfinityDiagonalLift S ≫ diagonalChart S =
      (lineInfinityOpen (lineInfinity S)).ι ≫
        map (Option (ULift.{u} (Fin 1))) (lineInfinityι S) := by
  rw [lineInfinityDiagonalLift, diagonalChart, Category.assoc, map_comp_lineInfinityChart_assoc,
    ← map_comp, lineInfinityToAffine_lineInfinityChart, ← lineInfinityChartToOpen_ι, Category.assoc,
    IsIso.inv_hom_id_assoc]

/-- The lift of the chart at infinity of `ℙ¹_Z` pulls the equation `z - t` of the diagonal back
to the coordinate `T_∞ / T₀` of `ℙ¹_Z`. -/
lemma lineInfinityDiagonalLift_appTop :
    (lineInfinityDiagonalLift S).appTop (diagonalChartEquation S) =
      lineInfinityCoord (lineInfinity S) := by
  have h₁ : (lineInfinityDiagonalLift S).appTop (AffineSpace.coord _ (ULift.up 0)) =
      lineInfinityCoord (lineInfinity S) := by
    rw [lineInfinityDiagonalLift, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.map_appTop_coord, inv_lineInfinityChartToOpen_appTop]
  have h₂ : (lineInfinityDiagonalLift S).appTop
      ((𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin 1); S)) ↘ 𝔸(ULift.{u} (Fin 1); S)).appTop
        (AffineSpace.coord S (ULift.up 0))) = 0 := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, lineInfinityDiagonalLift,
      Category.assoc, AffineSpace.map_over, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, lineInfinityToAffine_appTop, map_zero,
      map_zero]
  rw [diagonalChartEquation, map_sub, h₁, h₂, sub_zero]

end Line

end AlgebraicGeometry.ProjectiveSpace
