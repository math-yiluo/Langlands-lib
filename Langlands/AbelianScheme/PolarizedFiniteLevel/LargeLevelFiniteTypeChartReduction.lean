import Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelFiniteTypeStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameChartFiniteTypeStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelChartCoverReduction
import Langlands.AbelianScheme.PolarizedFiniteLevel.LevelBaseZariski

/-! # Finite type of the fine moduli scheme from finite type of the frame charts -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

namespace LevelBase

variable {n : ℕ}

/-- A morphism of level bases that is injective on test points, and through which a
test morphism to `X` factors exactly when it lands in the open `U`, identifies its
source with the open subscheme `U`. -/
theorem nonempty_iso_ofOpen {X Y : LevelBase n} (j : Y ⟶ X)
    (hinj : ∀ (T : LevelBase n) (y y' : T ⟶ Y), y ≫ j = y' ≫ j → y = y')
    (U : X.obj.Opens)
    (hU : ∀ (T : LevelBase n) (f : T ⟶ X),
      (∃ y : T ⟶ Y, y ≫ j = f) ↔ Set.range f.hom.base ⊆ (U : Set X.obj)) :
    Nonempty (Y ≅ X.ofOpen U) := by
  have hj : Set.range j.hom.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    exact (hU Y j).1 ⟨𝟙 Y, Category.id_comp j⟩
  let l : Y.obj ⟶ U.toScheme := IsOpenImmersion.lift U.ι j.hom hj
  let j' : Y ⟶ X.ofOpen U := homMk l
  have hj' : j' ≫ X.openι U = j := by
    ext1
    exact IsOpenImmersion.lift_fac U.ι j.hom hj
  obtain ⟨s, hs⟩ := (hU (X.ofOpen U) (X.openι U)).2 (by
    change Set.range U.ι.base ⊆ _
    rw [Scheme.Opens.range_ι])
  refine ⟨⟨j', s, ?_, ?_⟩⟩
  · apply hinj
    rw [Category.assoc, hs, hj', Category.id_comp]
  · ext1
    have h : (s ≫ j').hom ≫ U.ι = 𝟙 U.toScheme ≫ U.ι := by
      rw [Category.id_comp]
      change ((s ≫ j') ≫ X.openι U).hom = (X.openι U).hom
      rw [Category.assoc, hj', hs]
    exact (cancel_mono U.ι).mp h

/-- Local finite type and quasi-compactness over `Spec ℤ[1/n]` transfer along an
isomorphism of level bases. -/
theorem finiteType_of_iso {X Y : LevelBase n} (e : Y ≅ X)
    (h : LocallyOfFiniteType Y.toLocalizationSpec ∧ QuasiCompact Y.toLocalizationSpec) :
    LocallyOfFiniteType X.toLocalizationSpec ∧ QuasiCompact X.toLocalizationSpec := by
  obtain ⟨h₁, h₂⟩ := h
  have : IsIso e.inv.hom := inferInstanceAs (IsIso ((forget n).map e.inv))
  rw [← toLocalizationSpec_naturality e.inv.hom]
  exact ⟨inferInstance, inferInstance⟩

end LevelBase

/-- For a natural transformation `a` from a representable functor `Y` to a functor
represented by `X` through `α`, the point `a(y)` is the image under `α` of `y ≫ j`, where
`j` corresponds to the universal point of `Y`. -/
theorem app_eq_hom_app_comp {n : ℕ} {F : (LevelBase n)ᵒᵖ ⥤ Type 1} {X Y : LevelBase n}
    (α : uliftYoneda.{1}.obj X ≅ F) (a : uliftYoneda.{1}.obj Y ⟶ F)
    {T : LevelBase n} (y : T ⟶ Y) :
    a.app (op T) ⟨y⟩ =
      α.hom.app (op T) ⟨y ≫ (α.inv.app (op Y) (a.app (op Y) ⟨𝟙 Y⟩)).down⟩ := by
  have h1 := NatTrans.naturality_apply a y.op (⟨𝟙 Y⟩ : ULift (Y ⟶ Y))
  have h2 := NatTrans.naturality_apply α.inv y.op (a.app (op Y) ⟨𝟙 Y⟩)
  have h3 : (uliftYoneda.{1}.obj Y).map y.op (⟨𝟙 Y⟩ : ULift (Y ⟶ Y)) = ⟨y⟩ := by
    rfl
  have h4 : F.map y.op (a.app (op Y) ⟨𝟙 Y⟩) =
      α.hom.app (op T) (α.inv.app (op T) (F.map y.op (a.app (op Y) ⟨𝟙 Y⟩))) := by
    rw [Iso.inv_hom_id_app_apply]
  rw [h3] at h1
  rw [h1, h4, h2]
  rfl

set_option linter.defProp false in
/-- Proved definition: eventual local finite type and quasi-compactness of the
representing objects of the projective frame charts, base change of the frame locus and
covering by frame loci at large level imply the published
`LargeLevelFiniteTypeStatement`. -/
def largeLevelFiniteType_of_frameChartFiniteType
    (Hfc : FrameChartFiniteTypeStatement)
    (Hbc : FrameLocusBaseChangeStatement.{0})
    (Hcov : FrameLocusCoverStatement.{0}) :
    LargeLevelFiniteTypeStatement := by
  intro P g d hg hd
  obtain ⟨N₁, hN₁⟩ := Hfc P g d hg hd
  obtain ⟨N₂, hN₂⟩ := Hcov P g d hg hd
  refine ⟨max N₁ N₂, fun n hNn hn X ⟨α⟩ => ?_⟩
  have : NeZero n := ⟨by omega⟩
  -- the universal datum on `X`
  obtain ⟨b, hb⟩ := Quotient.exists_rep (α.hom.app (op X) ⟨𝟙 X⟩ : Moduli P X.obj g d n)
  have hres : ∀ (T : LevelBase n) (f : T ⟶ X),
      (moduliFunctor P g d n hd hn).map f.op b.classOf = α.hom.app (op T) ⟨f⟩ := by
    intro T f
    have h := NatTrans.naturality_apply α.hom f.op (⟨𝟙 X⟩ : ULift (X ⟶ X))
    change (moduliFunctor P g d n hd hn).map f.op (Quotient.mk _ b) = _
    rw [hb, ← h]
    change α.hom.app (op T) ⟨f ≫ 𝟙 X⟩ = _
    rw [Category.comp_id]
  have hαinj : ∀ T : LevelBase n, Function.Injective (α.hom.app (op T)) := by
    intro T x y h
    have h' := congrArg (α.inv.app (op T)) h
    rwa [Iso.hom_inv_id_app_apply, Iso.hom_inv_id_app_apply] at h'
  -- every frame locus of the universal datum is of finite type over `Spec ℤ[1/n]`
  have hchart : ∀ (ρ : Fin (cubicProjectiveDimension g d + 2) → Fin (2 * g) → ZMod n),
      LocallyOfFiniteType (X.ofOpen (b.frameLocus ρ)).toLocalizationSpec ∧
      QuasiCompact (X.ofOpen (b.frameLocus ρ)).toLocalizationSpec := by
    intro ρ
    obtain ⟨Y, a, hinj, hrange, hlft, hqc⟩ := hN₁ n (le_of_max_le_left hNn) hn ρ
    let j : Y ⟶ X := (α.inv.app (op Y) (a.app (op Y) ⟨𝟙 Y⟩)).down
    have ha : ∀ (T : LevelBase n) (y : T ⟶ Y),
        a.app (op T) ⟨y⟩ = α.hom.app (op T) ⟨y ≫ j⟩ :=
      fun T y => app_eq_hom_app_comp α a y
    obtain ⟨e⟩ := LevelBase.nonempty_iso_ofOpen j
      (fun T y y' h => by
        have := hinj (op T)
          (show a.app (op T) ⟨y⟩ = a.app (op T) ⟨y'⟩ by rw [ha, ha, h])
        exact congrArg ULift.down this)
      (b.frameLocus ρ)
      (fun T f => by
        refine Iff.trans ?_ (frameChart_mem_range_iff Hbc hd hn a hrange b f)
        rw [hres]
        constructor
        · rintro ⟨y, rfl⟩
          exact ⟨⟨y⟩, ha T y⟩
        · rintro ⟨⟨y⟩, hy⟩
          exact ⟨y, congrArg ULift.down (hαinj T ((ha T y).symm.trans hy))⟩)
    exact LevelBase.finiteType_of_iso e ⟨hlft, hqc⟩
  -- the frame loci cover `X`
  have hcov : ⨆ (ρ : Fin (cubicProjectiveDimension g d + 2) → Fin (2 * g) → ZMod n), b.frameLocus ρ = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨ρ, hρ⟩ := hN₂ n (le_of_max_le_right hNn) X.obj X.level_isUnit b x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨ρ, hρ⟩
  have hι : ∀ (ρ : Fin (cubicProjectiveDimension g d + 2) → Fin (2 * g) → ZMod n), (b.frameLocus ρ).ι ≫ X.toLocalizationSpec =
      (X.ofOpen (b.frameLocus ρ)).toLocalizationSpec :=
    fun ρ => LevelBase.localization_hom_ext _ _
  refine ⟨IsZariskiLocalAtSource.of_iSup_eq_top _ hcov fun ρ => (hι ρ) ▸ (hchart ρ).1, ?_⟩
  have hcpt : ∀ (ρ : Fin (cubicProjectiveDimension g d + 2) → Fin (2 * g) → ZMod n), IsCompact (b.frameLocus ρ : Set X.obj) := by
    intro ρ
    have := (hchart ρ).2
    have : CompactSpace (X.ofOpen (b.frameLocus ρ)).obj :=
      QuasiCompact.compactSpace_of_compactSpace (X.ofOpen (b.frameLocus ρ)).toLocalizationSpec
    exact isCompact_iff_compactSpace.mpr this
  have : CompactSpace X.obj := by
    refine ⟨?_⟩
    have hU : (Set.univ : Set X.obj) = ⋃ (ρ : Fin (cubicProjectiveDimension g d + 2) → Fin (2 * g) → ZMod n),
        (b.frameLocus ρ : Set X.obj) := by
      rw [← TopologicalSpace.Opens.coe_iSup, hcov]
      rfl
    rw [hU]
    exact isCompact_iUnion hcpt
  exact (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr this

end Langlands.AbelianScheme.PolarizedFiniteLevel
