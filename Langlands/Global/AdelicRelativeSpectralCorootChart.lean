import Langlands.Global.AdelicRelativeTruncationCoordinates
import Langlands.Global.AdelicRelativeAmbientParameterProduct
import Langlands.GroupScheme.Rational.RelativeCentralDirectionsProof

/-! # Coroot evaluation coordinates on the relative spectral space -/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj Classical

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints ArthurParabolicSpaces

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (Q : StandardIndex F G fam.i fam.ν)

local notation "T" => fam.T
local notation "P" => fam.P Q
local notation "pQ" => fam.p Q
local notation "Pstd" => Standard.parabolicScheme fam.i fam.ν Q.val
local notation "pstd" => Standard.parabolicHom fam.i fam.ν Q.val
local notation "ZT" => RestrictionSplitCentre.canonicalTorus F G
local notation "zG" => RestrictionSplitCentre.canonicalComponent F G
local notation "Δ" => simpleRelativeRoots fam.i fam.ν

omit [NumberField F] in
private theorem realParameterRestriction_comp {A B : CommGroupScheme (Spec (CommRingCat.of F))}
    {H : GroupScheme (Spec (CommRingCat.of F))} (f : A ⟶ B) (j : B.toGrp ⟶ H)
    (lam : RealCharacterParameter F H) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom f) (realParameterRestriction j lam) =
      realParameterRestriction (CommGroupScheme.groupHom f ≫ j) lam := by
  induction lam using TensorProduct.inductionOn with
  | tmul r χ =>
    simp only [realParameterRestriction, AlgebraTensorModule.map_tmul, LinearMap.id_apply,
      characterRestrict_comp]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [NumberField F] in
private theorem chamberEmbedding_comparison :
    Function.Injective (fam.chamberEmbedding Q) ∧
      LinearMap.range (fam.chamberEmbedding Q) = corootAnnihilator fam.i fam.coroots Q.val := by
  let := fam.isClosedImmersion_p Q
  let rep : (standardParabolic fam.i fam.ν Q.val).IsRepresentedBy pQ :=
    ⟨Over.mono_of_mono_left _, (fam.isCompatible Q).parabolic_eq⟩
  let can := Standard.isRepresentedBy_parabolicHom fam.i fam.ν Q.val
  let e : Pstd ≅ P := can.isoOfIsRepresentedBy rep
  have he : e.hom ≫ pQ = pstd := can.isoOfIsRepresentedBy_hom_comp rep
  have ht : torusToParabolic F fam.i fam.ν Q.val ≫ e.hom = fam.torus Q ≫ fam.l Q := by
    apply rep.hom_ext
    rw [Category.assoc, he, torusToParabolic_comp, Category.assoc, fam.torus_comp]
  let E : RealCharacterParameter F P ≃ₗ[ℝ] RealCharacterParameter F Pstd :=
    LinearEquiv.ofLinearMap (realCharacterParameterPullback e.hom) (realCharacterParameterPullback e.inv)
      (by rw [← realCharacterParameterPullback_comp, e.hom_inv_id, realCharacterParameterPullback_id])
      (by rw [← realCharacterParameterPullback_comp, e.inv_hom_id, realCharacterParameterPullback_id])
  have hEmb : fam.chamberEmbedding Q = (restrictToTorus F fam.i fam.ν Q.val).comp E.toLinearMap := by
    apply AlgebraTensorModule.ext
    intro c χ
    change rationalCharacterRestrictReal (fam.torus Q ≫ fam.l Q) (c ⊗ₜ[ℤ] χ) =
      rationalCharacterRestrictReal (torusToParabolic F fam.i fam.ν Q.val)
        (c ⊗ₜ[ℤ] characterRestrict e.hom χ)
    rw [← ht, ← rationalCharacterRestrictReal_comp_apply, rationalCharacterRestrictReal_tmul]
  have hComp := parabolicSpacesComparison F G fam.connectedReductive T fam.i fam.maximalSplit
    fam.ν fam.generic fam.coroots Q.val Q.property
  rw [hEmb]
  exact ⟨hComp.1.comp E.injective, by rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, hComp.2.1]⟩

private theorem relativeParameter_iff_central
    (r : ParabolicRootPresentation pQ (fam.l Q) (fam.a Q)) {lam : RealCharacterParameter F P} :
    lam ∈ relativeParameterSpace (F := F) pQ ↔
      ∀ v ∈ relativeCentralDirections fam.i, pair T (fam.chamberEmbedding Q lam) v = 0 := by
  let := fam.isClosedImmersion_p Q
  obtain ⟨f, hf, _, _, hRange, _⟩ := (GroupScheme.relativeCentralDirections.2 F G
    fam.connectedReductive T fam.i fam.maximalSplit).2.2.2.2.2.2
      ZT zG (RestrictionSplitCentre.isSplitComponent_canonicalComponent F G)
  have hh : CommGroupScheme.groupHom f ≫ fam.torus Q ≫ fam.l Q = splitCentreParabolicLift r := by
    apply (fam.isCompatible Q).parabolic.isClosedSubgroup.isRepresentedBy_range.hom_ext
    rw [Category.assoc, Category.assoc, fam.torus_comp, hf, splitCentreParabolicLift_comp]
  have hEmb : rationalCharacterRestrictReal (CommGroupScheme.groupHom f) (fam.chamberEmbedding Q lam) =
      realParameterRestriction (splitCentreParabolicLift r) lam := by
    rw [chamberEmbedding, realParameterRestriction_comp, hh]
  let e : RealCharacterParameter F (ZT).toGrp ≃ₗ[ℝ] Vstar ZT :=
    LinearEquiv.baseChange ℤ ℝ _ _ (rationalCharacters.equivCharacterLattice ZT).toIntLinearEquiv
  have he (x : RealCharacterParameter F P) :
      e (realCharacterParameterPullback (splitCentreParabolicLift r) x) =
        realParameterRestriction (splitCentreParabolicLift r) x := by
    induction x using TensorProduct.inductionOn with
    | tmul c χ => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hT := (RestrictionSplitCentre.isSplitComponent_canonicalComponent F G).isCentralSplitTorus.isSplitSubtorus.1
  let : (pair ZT).IsPerfPair := isPerfPair_of_isSplitTorus hT
  rw [relativeParameterSpace_eq_ker_centralRestriction r, LinearMap.mem_ker, ← e.map_eq_zero_iff,
    he lam]
  constructor
  · intro h v hv
    rw [← hRange, LinearMap.mem_range] at hv
    obtain ⟨u, rfl⟩ := hv
    rw [pair_cocharacterMapReal, hEmb, h, map_zero, LinearMap.zero_apply]
  · intro h
    apply (LinearMap.IsPerfPair.bijective_left (pair ZT)).injective
    apply LinearMap.ext
    intro v
    have hv : cocharacterMapReal f v ∈ relativeCentralDirections fam.i :=
      hRange ▸ LinearMap.mem_range_self _ _
    have hh := h _ hv
    rw [pair_cocharacterMapReal, hEmb] at hh
    simpa only [map_zero, LinearMap.zero_apply] using hh

/-- Relative spectral parameters are exactly the coordinates given by their real
pairings with the projected simple coroots outside the Levi. -/
def RelativeSpectralCorootChartStatement : Prop :=
  ∃ e : (fam.relativeSimpleRoots Q → ℝ) ≃ₗ[ℝ] relativeParameterSpace (F := F) pQ,
    ∀ c α, realParameterPairing F P (e c).val (fam.relativeCoroot Q α) = c α

theorem relativeSpectralCorootChart : RelativeSpectralCorootChartStatement fam Q := by
  let r : ParabolicRootPresentation pQ (fam.l Q) (fam.a Q) :=
    ⟨⟨fam.T, fam.i, fam.ν, Q.val, fam.f Q⟩, fam.isCompatible Q⟩
  let Vrel := relativeParameterSpace (F := F) pQ
  let ev : Vrel →ₗ[ℝ] (fam.relativeSimpleRoots Q → ℝ) := LinearMap.pi fun α =>
    ((realParameterPairing F P).flip (fam.relativeCoroot Q α)).comp Vrel.subtype
  have hApply (u : Vrel) (α : fam.relativeSimpleRoots Q) :
      ev u α = pair T (fam.chamberEmbedding Q u.val)
        (fam.coroots.realCoroot ⟨α, fam.mem_relativeRoots_of_mem_relativeSimpleRoots Q α⟩) :=
    fam.realParameterPairing_splitDual Q _ _
  have hEmb := fam.chamberEmbedding_comparison Q
  have hinj : Function.Injective ev := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro u hu
    rw [LinearMap.mem_ker] at hu
    apply Subtype.ext
    apply hEmb.1
    let : (pair T).IsPerfPair := isPerfPair_of_isSplitTorus fam.maximalSplit.isSplitSubtorus.1
    apply (LinearMap.IsPerfPair.bijective_left (pair T)).injective
    apply LinearMap.ext
    intro v
    let d := ArthurRelative.toCorootSpan fam.connectedReductive fam.maximalSplit fam.coroots v
    have hcentral : pair T (fam.chamberEmbedding Q u.val) (v - d.val) = 0 :=
      (fam.relativeParameter_iff_central Q r).mp u.property _
        (ArthurRelative.sub_toCorootSpan_mem fam.connectedReductive fam.maximalSplit fam.coroots v)
    have hD : pair T (fam.chamberEmbedding Q u.val) d.val = 0 := by
      rw [← fam.realParameterPairing_splitDual Q, fam.splitDual_eq_sum_relativeCoroot Q d.property,
        map_sum]
      refine Finset.sum_eq_zero fun α _ => ?_
      rw [map_smul, show realParameterPairing F P u.val (fam.relativeCoroot Q α) = 0 from congrFun hu α,
        smul_zero]
    simp only [map_sub, sub_eq_zero] at hcentral
    change pair T (fam.chamberEmbedding Q u.val) v = pair T (fam.chamberEmbedding Q 0) v
    simpa only [map_zero, LinearMap.zero_apply, ← hcentral] using hD
  have hsurj : Function.Surjective ev := by
    intro c
    let ℓ : Module.Dual ℝ (V T) := ∑ β : fam.relativeSimpleRoots Q,
      c β • ArthurRelative.weight fam.connectedReductive fam.maximalSplit fam.ν fam.coroots Δ β
    let : (pair T).IsPerfPair := isPerfPair_of_isSplitTorus fam.maximalSplit.isSplitSubtorus.1
    obtain ⟨Y, hY⟩ := (LinearMap.IsPerfPair.bijective_left (pair T)).surjective ℓ
    have hw (β : fam.relativeSimpleRoots Q) : (β : characterLattice T) ∈ Δ :=
      (ArthurTruncation.mem_simpleFinset fam.connectedReductive fam.maximalSplit).mp
        (Finset.mem_filter.mp β.property).1
    have hEval (α : relativeRoots fam.i) (hα : α.val ∈ Δ) :
        pair T Y (fam.coroots.realCoroot α) =
          ∑ β : fam.relativeSimpleRoots Q, c β * (if β.val = α.val then 1 else 0) := by
      rw [hY]
      simp only [ℓ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun β _ => congrArg (c β * ·)
        (ArthurRelative.weight_coroot fam.connectedReductive fam.maximalSplit fam.coroots
          fam.generic Set.Subset.rfl (hw β) α hα)
    have hyQ : Y ∈ corootAnnihilator fam.i fam.coroots Q.val := by
      rw [mem_corootAnnihilator]
      intro α hα
      change pair T Y (fam.coroots.realCoroot α) = 0
      rw [hEval α (Q.property hα)]
      refine Finset.sum_eq_zero fun β _ => ?_
      have hne : β.val ≠ α.val := fun he => (Finset.mem_filter.mp β.property).2 (he ▸ hα)
      simp [hne]
    obtain ⟨u, hu⟩ := (show Y ∈ LinearMap.range (fam.chamberEmbedding Q) from hEmb.2.symm ▸ hyQ)
    have huC : u ∈ Vrel := by
      apply (fam.relativeParameter_iff_central Q r).mpr
      intro v hv
      rw [hu, hY]
      simp only [ℓ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      refine Finset.sum_eq_zero fun β _ => ?_
      rw [ArthurRelative.weight_eq_zero_of_mem_rootAnnihilator fam.connectedReductive
        fam.maximalSplit fam.ν fam.coroots Δ β (by
          rw [mem_rootAnnihilator]
          exact fun α hα => (mem_relativeCentralDirections fam.i _).mp hv _
            (simpleRelativeRoots_subset_relativeRoots fam.i fam.ν hα)), mul_zero]
    refine ⟨⟨u, huC⟩, funext fun α => ?_⟩
    rw [hApply, show (⟨u, huC⟩ : Vrel).val = u from rfl, hu,
      hEval ⟨α.val, fam.mem_relativeRoots_of_mem_relativeSimpleRoots Q α⟩ (hw α)]
    rw [Finset.sum_eq_single α]
    · simp
    · intro β _ hβ
      have hne : β.val ≠ α.val := fun he => hβ (Subtype.ext he)
      simp [hne]
    · simp
  let E := LinearEquiv.ofBijective ev ⟨hinj, hsurj⟩
  refine ⟨E.symm, fun c α => ?_⟩
  exact congrFun (E.apply_symm_apply c) α

/-- An actual relative real displacement can be chosen with unit coroot evaluations
outside the Levi and zero evaluations on the Levi. -/
theorem exists_relativeDominantParameter :
    ∃ u : relativeParameterSpace (F := F) pQ,
      ∀ α : relativeRoots fam.i, α.val ∈ Δ →
        pair T (fam.chamberEmbedding Q u.val) (fam.coroots.realCoroot α) =
          if α.val ∈ Q.val then 0 else 1 := by
  obtain ⟨e, he⟩ := fam.relativeSpectralCorootChart Q
  let u := e (fun _ => 1)
  have hu : fam.chamberEmbedding Q u.val ∈ corootAnnihilator fam.i fam.coroots Q.val :=
    (fam.chamberEmbedding_comparison Q).2 ▸ LinearMap.mem_range_self _ _
  refine ⟨u, fun α hα => ?_⟩
  by_cases hQ : α.val ∈ Q.val
  · rw [ite_eq_left hQ]
    exact (mem_corootAnnihilator fam.i fam.coroots Q.val _).mp hu α hQ
  · rw [ite_eq_right hQ, ← fam.realParameterPairing_splitDual Q]
    let β : fam.relativeSimpleRoots Q := ⟨α.val, Finset.mem_filter.mpr
      ⟨(ArthurTruncation.mem_simpleFinset fam.connectedReductive fam.maximalSplit).mpr hα, hQ⟩⟩
    exact he (fun _ => 1) β

end Langlands.Global.StandardParabolicFamily
