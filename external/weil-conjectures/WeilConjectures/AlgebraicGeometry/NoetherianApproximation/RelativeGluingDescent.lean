/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.DescentStages
public import WeilConjectures.Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.RelativeGluingDatum
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.RelativeGluingOpens
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.RelativeGluingPresentation

/-!
# The raw relative gluing datum at a finite stage

Let `{Dⱼ}` be a cofiltered system of quasi-compact quasi-separated schemes with affine
transition maps and limit cone `c`, let `g : X ⟶ lim Dⱼ` be of finite presentation and let
`R` be a finite relative affine presentation of `X`
(`AlgebraicGeometry.RelativeAffinePresentation`).

1. Every affine chart `Wₐ` of `R` descends to an affine scheme `Yₐ` of finite presentation
   over a common stage `D_i` (`AlgebraicGeometry.RelativeAffinePresentation.ChartModels`), so
   that `Wₐ ≅ Lₐ := Yₐ ×_{D_i} lim Dⱼ`; we write `ℓₐ : Lₐ ⟶ X` for the resulting open immersions.
2. Every overlap `Lₐ ∩ ℓₐ⁻¹(L_b)` descends to a quasi-compact open of `Yₐ ×_{D_i} D_μ`
   (by `AlgebraicGeometry.baseChangeQcOpenDescent`), and every overlap map, viewed as a
   morphism to `Y_b` over `D_i`, descends to that open at a later stage `ν`.
3. All these data are transported to a common stage `λ_raw`, giving the raw relative gluing
   datum `AlgebraicGeometry.RelativeAffinePresentation.ChartModels.rawDatum`, whose base change
   to the limit is compatible with the `ℓₐ`
   (`AlgebraicGeometry.RelativeAffinePresentation.ChartModels.isCompatible_rawDatum`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
  [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]

include hc in
/-- An affine open of a scheme of finite presentation over the limit lying over an affine open
of a stage descends to an affine scheme of finite presentation over some stage. -/
theorem exists_isAffine_isPullback_of_isAffineOpen {X : Scheme.{u}} (g : X ⟶ c.pt)
    [LocallyOfFinitePresentation g] {i₀ : I} {W : X.Opens} (hW : IsAffineOpen W)
    {V : (D.obj i₀).Opens} (hV : IsAffineOpen V) (hle : W ≤ (g ≫ c.π.app i₀) ⁻¹ᵁ V) :
    ∃ (k : I) (Y : Scheme.{u}) (_ : IsAffine Y) (p : Y ⟶ D.obj k)
      (_ : LocallyOfFinitePresentation p) (h : W.toScheme ⟶ Y),
      IsPullback h (W.ι ≫ g) p (c.π.app k) := by
  have : IsAffine W.toScheme := hW
  have : IsAffine V.toScheme := hV
  let q := (g ≫ c.π.app i₀).resLE V W hle
  have hq : q ≫ V.ι = (W.ι ≫ g) ≫ c.π.app i₀ := by simp [q]
  have : ∀ j : Over i₀, IsAffine ((baseChangeDiagram D V.ι).obj j) := fun j ↦
    inferInstanceAs (IsAffine (pullback V.ι (D.map j.hom)))
  have hsnd : pullback.lift q (W.ι ≫ g) hq ≫ pullback.snd V.ι (c.π.app i₀) = W.ι ≫ g :=
    pullback.lift_snd ..
  have hmono : MorphismProperty.monomorphisms Scheme.{u} (pullback.snd V.ι (c.π.app i₀)) :=
    inferInstanceAs (Mono _)
  have hcomp : LocallyOfFinitePresentation
      (pullback.lift q (W.ι ≫ g) hq ≫ pullback.snd V.ι (c.π.app i₀)) := by
    rw [hsnd]
    infer_instance
  have : @LocallyOfFinitePresentation W.toScheme (baseChangeCone D c V.ι).pt
      (pullback.lift q (W.ι ≫ g) hq) :=
    MorphismProperty.of_postcomp (W := @LocallyOfFinitePresentation)
      (W' := MorphismProperty.monomorphisms Scheme.{u}) _ (pullback.snd V.ι (c.π.app i₀))
      hmono hcomp
  obtain ⟨j, Y, hYaff, p, hp, h, hsq⟩ :=
    Scheme.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine
      (baseChangeDiagram D V.ι) (baseChangeCone D c V.ι)
      (isLimitBaseChangeCone D c V.ι hc) (pullback.lift q (W.ι ≫ g) hq)
  have := hp
  have : IsOpenImmersion ((baseChangeDiagramπ D V.ι).app j) :=
    inferInstanceAs (IsOpenImmersion (pullback.snd V.ι (D.map j.hom)))
  refine ⟨j.left, Y, hYaff, p ≫ (baseChangeDiagramπ D V.ι).app j, inferInstance, h, ?_⟩
  rw [← hsnd]
  exact hsq.paste_vert (isPullback_baseChangeCone_π D c V.ι j)

namespace RelativeAffinePresentation

variable {X : Scheme.{u}} {g : X ⟶ c.pt} (R : RelativeAffinePresentation c g)

/-- Models of the charts of `R` over a common stage `D_i`: affine schemes `Yₐ` of finite
presentation over `D_i` whose base change to the limit is the chart `Wₐ`. -/
structure ChartModels where
  /-- The common stage `i`. -/
  stage : I
  /-- The models `Yₐ` of the charts. -/
  Y (a : R.J) : Scheme.{u}
  /-- The structure morphisms `Yₐ ⟶ D_i`. -/
  p (a : R.J) : Y a ⟶ D.obj stage
  /-- The projections `Wₐ ⟶ Yₐ`. -/
  h (a : R.J) : (R.chart a).toScheme ⟶ Y a
  /-- The models are affine. -/
  isAffine (a : R.J) : IsAffine (Y a)
  /-- The models are locally of finite presentation over `D_i`. -/
  locallyOfFinitePresentation (a : R.J) : LocallyOfFinitePresentation (p a)
  /-- Each chart `Wₐ` is the base change of its model `Yₐ` along `c.pt ⟶ D_i`. -/
  isPullback (a : R.J) : IsPullback (h a) ((R.chart a).ι ≫ g) (p a) (c.π.app stage)

include hc in
theorem nonempty_chartModels [LocallyOfFinitePresentation g] : Nonempty R.ChartModels := by
  classical
  choose k Y hY p hp h H using fun a ↦ exists_isAffine_isPullback_of_isAffineOpen hc g
    (R.isAffineOpen_chart a) (R.isAffineOpen_base a) (R.chart_le a)
  obtain ⟨i, hi⟩ := IsCofiltered.exists_forall_nonempty_hom k
  let f (a : R.J) : i ⟶ k a := (hi a).some
  refine ⟨{
    stage := i
    Y a := pullback (p a) (D.map (f a))
    p a := pullback.snd _ _
    h a := isPullbackLift D c (f a) (H a)
    isAffine a := ?_
    locallyOfFinitePresentation a := MorphismProperty.pullback_snd _ _ (hp a)
    isPullback a := isPullback_isPullbackLift (f a) (H a) }⟩
  have := hY a
  have : IsAffineHom (pullback.fst (p a) (D.map (f a))) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  exact isAffine_of_isAffineHom (pullback.fst (p a) (D.map (f a)))

/-- The selected chart models of `R`. -/
noncomputable def chartModels [LocallyOfFinitePresentation g] : R.ChartModels :=
  Classical.choice (R.nonempty_chartModels hc)

namespace ChartModels

variable {R} (M : R.ChartModels)

attribute [instance] ChartModels.isAffine ChartModels.locallyOfFinitePresentation

/-- The comparison isomorphism between the chart `Wₐ` and `Lₐ = Yₐ ×_{D_i} lim Dⱼ`. -/
noncomputable def chartIso (a : R.J) : (R.chart a).toScheme ≅ pullback (M.p a) (c.π.app M.stage) :=
  (M.isPullback a).isoPullback

/-- The open immersion `ℓₐ : Yₐ ×_{D_i} lim Dⱼ ⟶ X` onto the chart `Wₐ`. -/
noncomputable def ℓ (a : R.J) : pullback (M.p a) (c.π.app M.stage) ⟶ X :=
  (M.chartIso a).inv ≫ (R.chart a).ι

instance (a : R.J) : IsOpenImmersion (M.ℓ a) := by
  dsimp [ℓ]
  infer_instance

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
@[reassoc (attr := simp)]
lemma ℓ_comp (a : R.J) : M.ℓ a ≫ g = pullback.snd (M.p a) (c.π.app M.stage) := by
  simp [ℓ, chartIso]

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
lemma opensRange_ℓ (a : R.J) : (M.ℓ a).opensRange = R.chart a := by
  dsimp only [ℓ]
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
lemma iSup_opensRange_ℓ : ⨆ a, (M.ℓ a).opensRange = ⊤ := by
  simp only [opensRange_ℓ]
  exact R.iSup_chart

instance (a : R.J) : CompactSpace ↥(pullback (M.p a) (c.π.app M.stage)) :=
  have : IsAffine (R.chart a) := R.isAffineOpen_chart a
  have : IsAffine (pullback (M.p a) (c.π.app M.stage)) := .of_isIso (M.chartIso a).inv
  inferInstance

/-- The overlap of the chart `a` with the chart `b` in the limit. -/
noncomputable def limitOverlap (a b : R.J) : (pullback (M.p a) (c.π.app M.stage)).Opens :=
  M.ℓ a ⁻¹ᵁ (M.ℓ b).opensRange

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
lemma isCompact_limitOverlap [QuasiSeparatedSpace X] (a b : R.J) :
    IsCompact (M.limitOverlap a b : Set ↥(pullback (M.p a) (c.π.app M.stage))) :=
  QuasiCompact.isCompact_preimage _ (M.ℓ b).opensRange.2
    (isCompact_range (M.ℓ b).continuous)

/-- The overlap map `Lₐ ∩ ℓₐ⁻¹(L_b) ⟶ L_b` in the limit. -/
noncomputable def limitOverlapMap (a b : R.J) :
    (M.limitOverlap a b).toScheme ⟶ pullback (M.p b) (c.π.app M.stage) :=
  IsOpenImmersion.lift (M.ℓ b) ((M.limitOverlap a b).ι ≫ M.ℓ a) (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact x.2)

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
@[reassoc (attr := simp)]
lemma limitOverlapMap_ℓ (a b : R.J) :
    M.limitOverlapMap a b ≫ M.ℓ b = (M.limitOverlap a b).ι ≫ M.ℓ a :=
  IsOpenImmersion.lift_fac _ _ _

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
@[reassoc (attr := simp)]
lemma limitOverlapMap_snd (a b : R.J) :
    M.limitOverlapMap a b ≫ pullback.snd _ _ = (M.limitOverlap a b).ι ≫ pullback.snd _ _ := by
  rw [← ℓ_comp, limitOverlapMap_ℓ_assoc, ℓ_comp]

/-! ### Descending the overlaps -/

variable [QuasiSeparatedSpace X]

/-- The stage `μ_{ab}` to which the overlap `Lₐ ∩ ℓₐ⁻¹(L_b)` descends. -/
noncomputable def overlapStage (a b : R.J) : Over M.stage :=
  baseChangeQcOpenDescentStage hc (M.p a) (M.limitOverlap a b) (M.isCompact_limitOverlap a b)

/-- The descended overlap, a quasi-compact open of `Yₐ ×_{D_i} D_{μ_{ab}}`. -/
noncomputable def overlapOpen (a b : R.J) :
    (pullback (M.p a) (D.map (M.overlapStage hc a b).hom)).Opens :=
  baseChangeQcOpenDescent hc (M.p a) (M.limitOverlap a b) (M.isCompact_limitOverlap a b)

lemma isCompact_overlapOpen (a b : R.J) :
    IsCompact (M.overlapOpen hc a b :
      Set ↥(pullback (M.p a) (D.map (M.overlapStage hc a b).hom))) :=
  isCompact_baseChangeQcOpenDescent hc (M.p a) _ _

lemma preimage_overlapOpen (a b : R.J) :
    (baseChangeCone D c (M.p a)).π.app (M.overlapStage hc a b) ⁻¹ᵁ M.overlapOpen hc a b =
      M.limitOverlap a b :=
  preimage_baseChangeQcOpenDescent hc (M.p a) _ _

/-- The overlap map in the limit, as a morphism to `Y_b`, on the preimage of the descended
overlap. -/
noncomputable def limitOverlapMapFst (a b : R.J) :
    ((baseChangeCone D c (M.p a)).π.app (M.overlapStage hc a b) ⁻¹ᵁ
      M.overlapOpen hc a b).toScheme ⟶ M.Y b :=
  Scheme.homOfLE _ (M.preimage_overlapOpen hc a b).le ≫ M.limitOverlapMap a b ≫
    pullback.fst _ _

lemma limitOverlapMapFst_comp (a b : R.J) :
    M.limitOverlapMapFst hc a b ≫ M.p b =
      ((baseChangeCone D c (M.p a)).π.app (M.overlapStage hc a b) ⁻¹ᵁ M.overlapOpen hc a b).ι ≫
        (baseChangeCone D c (M.p a)).π.app (M.overlapStage hc a b) ≫
          (baseChangeDiagramStructure D (M.p a)).app (M.overlapStage hc a b) := by
  simp [limitOverlapMapFst, pullback.condition, Scheme.homOfLE_ι_assoc]

lemma exists_overlapMap (a b : R.J) :
    ∃ (k : Over (M.overlapStage hc a b))
      (ψ : ((baseChangeDiagram D (M.p a)).map k.hom ⁻¹ᵁ M.overlapOpen hc a b).toScheme ⟶ M.Y b),
      ψ ≫ M.p b = ((baseChangeDiagram D (M.p a)).map k.hom ⁻¹ᵁ M.overlapOpen hc a b).ι ≫
          (baseChangeDiagramStructure D (M.p a)).app k.left ∧
        ((baseChangeCone D c (M.p a)).π.app k.left).resLE _ _
          (by rw [← Scheme.Hom.comp_preimage, Cone.w]) ≫ ψ = M.limitOverlapMapFst hc a b :=
  exists_resLE_comp_eq_of_locallyOfFinitePresentation (isLimitBaseChangeCone D c (M.p a) hc)
    (baseChangeDiagramStructure D (M.p a)) (M.isCompact_overlapOpen hc a b) (M.p b)
    (M.limitOverlapMapFst hc a b) (M.limitOverlapMapFst_comp hc a b)

/-- The stage `ν_{ab} ≥ μ_{ab}` to which the overlap map descends. -/
noncomputable def overlapMapStage (a b : R.J) : Over (M.overlapStage hc a b) :=
  (M.exists_overlapMap hc a b).choose

/-- The descended overlap map, from the descended overlap at the stage `ν_{ab}` to `Y_b`. -/
noncomputable def overlapMapDescent (a b : R.J) :
    ((baseChangeDiagram D (M.p a)).map (M.overlapMapStage hc a b).hom ⁻¹ᵁ
      M.overlapOpen hc a b).toScheme ⟶ M.Y b :=
  (M.exists_overlapMap hc a b).choose_spec.choose

lemma overlapMapDescent_comp (a b : R.J) :
    M.overlapMapDescent hc a b ≫ M.p b =
      ((baseChangeDiagram D (M.p a)).map (M.overlapMapStage hc a b).hom ⁻¹ᵁ
        M.overlapOpen hc a b).ι ≫ pullback.fst _ _ ≫ M.p a := by
  refine (M.exists_overlapMap hc a b).choose_spec.choose_spec.1.trans ?_
  rfl

lemma resLE_overlapMapDescent (a b : R.J) :
    ((baseChangeCone D c (M.p a)).π.app (M.overlapMapStage hc a b).left).resLE _ _
        (by rw [← Scheme.Hom.comp_preimage, Cone.w]) ≫ M.overlapMapDescent hc a b =
      M.limitOverlapMapFst hc a b :=
  (M.exists_overlapMap hc a b).choose_spec.choose_spec.2

lemma exists_rawStage :
    ∃ (l : Over M.stage), ∀ a b : R.J, Nonempty (l ⟶ (M.overlapMapStage hc a b).left) := by
  obtain ⟨l, hl⟩ := IsCofiltered.exists_forall_nonempty_hom
    fun x : R.J × R.J ↦ (M.overlapMapStage hc x.1 x.2).left
  exact ⟨l, fun a b ↦ hl (a, b)⟩

/-- The stage `λ_raw`, a selected common upper bound of the stages `ν_{ab}` of the descended overlap
maps (and hence of the stages of the descended overlaps and of the chart stage). -/
noncomputable def rawStage : Over M.stage := (M.exists_rawStage hc).choose

/-- The selected transition `λ_raw ⟶ ν_{ab}`. -/
noncomputable def rawStageHom (a b : R.J) : M.rawStage hc ⟶ (M.overlapMapStage hc a b).left :=
  ((M.exists_rawStage hc).choose_spec a b).some

/-- The raw relative gluing datum `R^raw_{X,λ_raw}` over `D_{λ_raw}`: the charts
are `Yₐ ×_{D_i} D_{λ_raw}`, the overlaps are the descended overlaps and the overlap maps are the
descended overlap maps, all transported to `λ_raw`. -/
noncomputable def rawDatum : RelativeGluingDatum M.p (D.map (M.rawStage hc).hom) where
  V a b := (baseChangeDiagram D (M.p a)).map (M.rawStageHom hc a b) ⁻¹ᵁ
    ((baseChangeDiagram D (M.p a)).map (M.overlapMapStage hc a b).hom ⁻¹ᵁ M.overlapOpen hc a b)
  ψ a b := ((baseChangeDiagram D (M.p a)).map (M.rawStageHom hc a b)).resLE _ _ le_rfl ≫
    M.overlapMapDescent hc a b
  ψ_comp a b := by
    rw [Category.assoc, overlapMapDescent_comp, Scheme.Hom.resLE_comp_ι_assoc,
      baseChangeDiagram_map_fst_assoc]

/-- The transport of a datum at a stage `j` to the limit. -/
noncomputable abbrev limitTransport {j : Over M.stage}
    (d : RelativeGluingDatum M.p (D.map j.hom)) : RelativeGluingDatum M.p (c.π.app M.stage) :=
  d.transport (c.π.app j.left) (c.w j.hom)

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [QuasiSeparatedSpace X] in
lemma chartMap_limit_eq {j : Over M.stage} (a : R.J) :
    RelativeGluingDatum.chartMap M.p (c.π.app j.left) (c.w j.hom) a =
      (baseChangeCone D c (M.p a)).π.app j :=
  rfl

lemma limitTransport_rawDatum_ψ (a b : R.J) :
    (M.limitTransport (M.rawDatum hc)).ψ a b =
      ((baseChangeCone D c (M.p a)).π.app (M.overlapMapStage hc a b).left).resLE _ _
        (by
          simp only [RelativeGluingDatum.transport, rawDatum]
          rw [chartMap_limit_eq, ← Scheme.Hom.comp_preimage, Cone.w]) ≫
        M.overlapMapDescent hc a b := by
  dsimp only [limitTransport, RelativeGluingDatum.transport, rawDatum]
  rw [← Category.assoc]
  congr 1
  rw [← cancel_mono (Scheme.Opens.ι _), Category.assoc, Scheme.Hom.resLE_comp_ι,
    Scheme.Hom.resLE_comp_ι_assoc, Scheme.Hom.resLE_comp_ι, chartMap_limit_eq, Cone.w]

/-- The base change of the raw datum to the limit is the overlap datum of `X`:
its overlaps are the overlaps `Lₐ ∩ ℓₐ⁻¹(L_b)` and its overlap maps are compatible with the
open immersions `ℓₐ` (i.e. they are the overlap maps of `X`). -/
theorem isCompatible_rawDatum :
    RelativeGluingDatum.IsCompatible M.ℓ (M.limitTransport (M.rawDatum hc)) := by
  have hV (a b : R.J) : (M.limitTransport (M.rawDatum hc)).V a b = M.limitOverlap a b := by
    simp only [RelativeGluingDatum.transport, rawDatum]
    rw [chartMap_limit_eq, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, Cone.w,
      Cone.w]
    exact M.preimage_overlapOpen hc a b
  refine ⟨hV, fun a b ↦ ?_⟩
  have key : (M.limitTransport (M.rawDatum hc)).map a b =
      Scheme.homOfLE _ (hV a b).le ≫ M.limitOverlapMap a b := by
    apply pullback.hom_ext
    · rw [RelativeGluingDatum.map_fst, limitTransport_rawDatum_ψ,
        ← Scheme.Hom.map_resLE _ (by rw [← Scheme.Hom.comp_preimage, Cone.w])
          (by rw [hV, ← M.preimage_overlapOpen hc a b]),
        Category.assoc, resLE_overlapMapDescent, limitOverlapMapFst, Category.assoc]
      exact Scheme.homOfLE_homOfLE_assoc _ _ _ _
    · rw [RelativeGluingDatum.map_snd, Category.assoc, limitOverlapMap_snd,
        Scheme.homOfLE_ι_assoc]
  rw [key, Category.assoc, limitOverlapMap_ℓ, Scheme.homOfLE_ι_assoc]

end ChartModels

end RelativeAffinePresentation

end AlgebraicGeometry
