import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductRestrictionStatement
import Langlands.AllFieldBZ.Representation.Derivative.RestrictionBridge
import Langlands.AllFieldBZ.Representation.Derivative.RightMixedLevel
import Langlands.Representation.Derivative.RestrictedProductLevel

/-!
# All-field port of `Langlands.Representation.Derivative.RestrictedProductLevel`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.RestrictedProductLevel` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding HasNonzeroDerivative IsHomogeneous LeftMixedProductDerivative LeftMixedProductDerivativeIso LeftMixedProductDerivativeVanishing MirabolicDerivativeDetection MirabolicProductMinusCompatibilityStatement MirabolicProductRestrictionStatement RightMixedProductPhiMinusDetection generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeDetection mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicRankCast mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
universe uF uV uW

variable {F : LocalFieldPackage.{uF}}

namespace RestrictedProductLevel
open Langlands.Derivative.RestrictedProductLevel hiding hasNonzeroDerivative_leftMixed hasNonzeroDerivative_of_leftMixed isHomogeneous_restrictedProduct le_level_leftMixed level_le_of_imp_of_rank level_leftMixed_le
open Langlands.Derivative.LevelCalculus hiding hasNonzeroDerivative_iff_of_iso hasNonzeroDerivative_level hasNonzeroDerivative_of_injective hasNonzeroDerivative_succ_iff hasNonzeroDerivative_succ_iff_cast isHomogeneous_of_forall_injective isHomogeneous_of_iso level_eq_level_phiMinus_succ level_eq_of_isHomogeneous level_eq_of_iso level_le_level_phiMinus_succ level_le_max_of_isShortExact level_le_of_imp level_le_of_injective level_le_one_of_subsingleton_phiMinus level_mirabolicRankCast level_pos mapsShortExact_mirabolicDerivative mapsShortExact_mirabolicDerivativeOfOrder mapsShortExact_mirabolicRankCast mapsShortExact_phiMinusIterate mirabolicDerivative_succ_cast_obj nontrivial_mirabolicDerivative_cast_congr nontrivial_of_hasNonzeroDerivative nontrivial_phiMinus_iff
open Langlands.AllFieldBZ.Derivative.LevelCalculus
open Langlands.Derivative.RightMixedLevel hiding isHomogeneous_mirabolicRankCast level_eq_of_phiMinus_injective level_eq_succ_of_phiMinus level_of_injective_rightMixed level_of_injective_rightMixed_zero mirabolicDerivative_zero_cast_obj nontrivial_phiMinus_of_injective phiMinus_cast_map_injective
open Langlands.AllFieldBZ.Derivative.RightMixedLevel
open Langlands.Derivative.MirabolicProductRestriction hiding restrictedProduct restrictionQuotient restrictionSubobject
open Langlands.AllFieldBZ.Derivative.MirabolicProductRestriction
/-! ## Comparisons across ranks and casts -/

section Comparison
variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

theorem level_le_of_imp_of_rank {N M : ℕ} :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier))
      (B : SmoothRep.{0, uF, uW} ℂ (mirabolic M F.Carrier)),
      (∀ k, HasNonzeroDerivative T ψ A k → HasNonzeroDerivative T ψ B k) →
        level T ψ A ≤ level T ψ B := by
  intro A B h
  by_cases h0 : level T ψ A = 0
  · rw [h0]
    exact Nat.zero_le _
  · exact le_level_of_hasNonzeroDerivative T ψ B (h _ (Langlands.AllFieldBZ.Derivative.LevelCalculus.hasNonzeroDerivative_level T ψ A h0))

end Comparison
/-! ## Levels of left mixed products (BZ77 4.14(a)) -/

section LeftLevel
variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
  (hLD : LeftMixedProductDerivative.{uF, uV} F T)
include hLD

/-- A nonzero derivative of `ρ × τ` comes from a nonzero derivative of `τ`. -/
theorem hasNonzeroDerivative_of_leftMixed {k r : ℕ} :
    letI := T.topology
    ∀ (ρ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
      (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)) (i : ℕ),
      HasNonzeroDerivative T ψ ((T.leftMixedProductFunctor k r).obj (ρ, τ)) i →
        HasNonzeroDerivative T ψ τ i := by
  let _ := T.topology
  rintro ρ τ i ⟨hi, h⟩
  by_cases hir : i ≤ r + 1
  · obtain ⟨e⟩ := hLD.1 ψ k r i ⟨hi.1, hir⟩
    have h1 : Nontrivial ((T.binaryNormalizedProductFunctor k (r + 1 - i)).obj
        (ρ, (mirabolicDerivativeOfOrder T ψ r i ⟨hi.1, hir⟩).obj τ)) :=
      (nontrivial_iff_of_iso (e.app (ρ, τ))).mp
        ((RestrictionBridge.nontrivial_generalLinearRankCast_iff T _ _).mpr h)
    refine ⟨⟨hi.1, hir⟩, ?_⟩
    by_contra h2
    rw [not_nontrivial_iff_subsingleton] at h2
    exact not_subsingleton _ (ProductVanishing.subsingleton_binary T
      (ρ, (mirabolicDerivativeOfOrder T ψ r i ⟨hi.1, hir⟩).obj τ) (Or.inr h2))
  · exact absurd h (not_nontrivial_iff_subsingleton.mpr (hLD.2 ψ k r i hi (by omega) ρ τ))

/-- If `ρ ≠ 0`, every nonzero derivative of `τ` gives one of `ρ × τ`. -/
theorem hasNonzeroDerivative_leftMixed {k r : ℕ} :
    letI := T.topology
    ∀ (ρ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
      (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)), Nontrivial ρ → ∀ i : ℕ,
      HasNonzeroDerivative T ψ τ i →
        HasNonzeroDerivative T ψ ((T.leftMixedProductFunctor k r).obj (ρ, τ)) i := by
  let _ := T.topology
  rintro ρ τ hρ i ⟨hi, h⟩
  obtain ⟨e⟩ := hLD.1 ψ k r i hi
  have h1 : Nontrivial ((T.binaryNormalizedProductFunctor k (r + 1 - i)).obj
      (ρ, (mirabolicDerivativeOfOrder T ψ r i hi).obj τ)) :=
    ProductVanishing.nontrivial_binary T _
  refine ⟨⟨hi.1, by omega⟩, ?_⟩
  exact (RestrictionBridge.nontrivial_generalLinearRankCast_iff T
    (show k + r + 1 - i = k + (r + 1 - i) by omega) _).mp
      ((nontrivial_iff_of_iso (e.app (ρ, τ))).mpr h1)

theorem level_leftMixed_le {k r : ℕ} :
    letI := T.topology
    ∀ (ρ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
      (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)),
      level T ψ ((T.leftMixedProductFunctor k r).obj (ρ, τ)) ≤ level T ψ τ :=
  fun ρ τ => level_le_of_imp_of_rank T ψ _ _ (hasNonzeroDerivative_of_leftMixed T ψ hLD ρ τ)

theorem le_level_leftMixed {k r : ℕ} :
    letI := T.topology
    ∀ (ρ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
      (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)), Nontrivial ρ →
      level T ψ τ ≤ level T ψ ((T.leftMixedProductFunctor k r).obj (ρ, τ)) :=
  fun ρ τ hρ => level_le_of_imp_of_rank T ψ _ _ (hasNonzeroDerivative_leftMixed T ψ hLD ρ τ hρ)

end LeftLevel
/-! ## The restricted binary product -/

section Main
variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
  (hE : Mirabolic.MinusExactnessStatement.{uF, max uF uV} F T)
  (hD : RightMixedProductPhiMinusDetection.{uF, uV} F T)
  (hS : MirabolicProductMinus.RightPhiShortExact.{uF, uV} F T)
  (hB : MirabolicProductMinus.RightPhiBoundary.{uF, uV} F T)
  (hR : MirabolicProductRestrictionStatement.{uF, uV} F T)
  (hLD : LeftMixedProductDerivative.{uF, uV} F T)
include hE hD hS hB hR hLD

/-- If `D|P` has a single nonzero derivative, of order `s + 1`, and
`D^(s+1) × P'|P` is homogeneous, then `(D × P')|P` is homogeneous unless some
nonzero representation injects both into `(D × P')|P` and into `D × (P'|P)`. -/
theorem isHomogeneous_restrictedProduct (m n n' s : ℕ) (hm : m = n' + s) :
    letI := T.topology
    ∀ (D : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier))
      (P : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier)),
      (∀ j, HasNonzeroDerivative T ψ ((generalLinearRestriction T m).obj D) j → j = s + 1) →
      IsHomogeneous T ψ ((T.leftMixedProductFunctor n' n).obj
        ((mirabolicDerivative T ψ n' s).obj
          ((mirabolicRankCast T hm).obj ((generalLinearRestriction T m).obj D)),
          (generalLinearRestriction T n).obj P)) →
      (∀ (W : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (m + n + 1) F.Carrier))
          (f : W ⟶ (Langlands.AllFieldBZ.Derivative.MirabolicProductRestriction.restrictedProduct T m n).obj (D, P))
          (g : W ⟶ (Langlands.AllFieldBZ.Derivative.MirabolicProductRestriction.restrictionQuotient T m n).obj (D, P)),
          Function.Injective (SmoothRep.hom f) → Function.Injective (SmoothRep.hom g) →
            Nontrivial W → False) →
      IsHomogeneous T ψ ((Langlands.AllFieldBZ.Derivative.MirabolicProductRestriction.restrictedProduct T m n).obj (D, P)) := by
  let _ := T.topology
  intro D P hDj hY hC2
  obtain ⟨i, q, hiq⟩ := hR m n
  obtain ⟨hi, hex, hq⟩ := hiq (D, P)
  have hσ : ∀ (W : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (m + n + 1) F.Carrier))
      (f : W ⟶ (Langlands.AllFieldBZ.Derivative.MirabolicProductRestriction.restrictionSubobject T m n).obj (D, P)), Function.Injective (SmoothRep.hom f) →
        Nontrivial W → level T ψ W = level T ψ ((T.leftMixedProductFunctor n' n).obj
          ((mirabolicDerivative T ψ n' s).obj
            ((mirabolicRankCast T hm).obj ((generalLinearRestriction T m).obj D)),
            (generalLinearRestriction T n).obj P)) + (s + 1) :=
    fun W f hf hW => Langlands.AllFieldBZ.Derivative.RightMixedLevel.level_of_injective_rightMixed T ψ hE hD hS hB n n' s m hm P
      ((generalLinearRestriction T m).obj D) hDj hY (m + n + 1) _ W f hf hW
  apply Langlands.AllFieldBZ.Derivative.LevelCalculus.isHomogeneous_of_forall_injective T ψ _ (level T ψ ((T.leftMixedProductFunctor n' n).obj
    ((mirabolicDerivative T ψ n' s).obj
      ((mirabolicRankCast T hm).obj ((generalLinearRestriction T m).obj D)),
      (generalLinearRestriction T n).obj P)) + (s + 1))
  intro W f hf hW
  by_cases h1 : comap f (SmoothRep.hom (i.app (D, P))).range = ⊥
  · exfalso
    refine hC2 W f (f ≫ q.app (D, P)) hf ?_ hW
    intro x y hxy
    have h2 : x - y ∈ (comap f (SmoothRep.hom (i.app (D, P))).range).toSubmodule := by
      rw [mem_comap]
      change SmoothRep.hom f (x - y) ∈ LinearMap.range (SmoothRep.hom (i.app (D, P))).toLinearMap
      rw [hex, LinearMap.mem_ker]
      change SmoothRep.hom (q.app (D, P)) (SmoothRep.hom f (x - y)) = 0
      rw [map_sub, map_sub]
      exact sub_eq_zero.mpr hxy
    rw [h1] at h2
    exact sub_eq_zero.mp ((Submodule.mem_bot ℂ).mp h2)
  · have hW1 := subrepresentation_nontrivial _ h1
    let g := comapMap f (SmoothRep.hom (i.app (D, P))).range ≫ (isoRange (i.app (D, P)) hi).inv
    have hg : Function.Injective (SmoothRep.hom g) :=
      (iso_hom_injective (isoRange (i.app (D, P)) hi).symm).comp (comapMap_injective f _ hf)
    have hlev1 := hσ _ g hg hW1
    have hσne : Nontrivial ((Langlands.AllFieldBZ.Derivative.MirabolicProductRestriction.restrictionSubobject T m n).obj (D, P)) :=
      nontrivial_of_injective g hg
    have hlevσ := hσ _ (𝟙 _) (fun _ _ h => h) hσne
    have hlow := Langlands.AllFieldBZ.Derivative.LevelCalculus.level_le_of_injective T ψ hE (SmoothRep.subtype W _)
      (SmoothRep.subtype_injective W (comap f (SmoothRep.hom (i.app (D, P))).range))
    have hup1 := Langlands.AllFieldBZ.Derivative.LevelCalculus.level_le_of_injective T ψ hE f hf
    have hup2 := Langlands.AllFieldBZ.Derivative.LevelCalculus.level_le_max_of_isShortExact T ψ hE
      (⟨hi, hq, hex⟩ : IsShortExact (i.app (D, P)) (q.app (D, P)))
    have hDne : Nontrivial ((generalLinearRestriction T m).obj D) := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      have h' := mirabolicRankCast_obj_subsingleton T (show (n + 1) + m = m + n + 1 by omega) _
        (ProductVanishing.subsingleton_rightMixed T ((generalLinearRestriction T m).obj D, P)
          (Or.inl h))
      exact (not_nontrivial_iff_subsingleton.mpr h') hσne
    have hQ : Nontrivial ((mirabolicDerivative T ψ n' s).obj
        ((mirabolicRankCast T hm).obj ((generalLinearRestriction T m).obj D))) := by
      have hpos := Langlands.AllFieldBZ.Derivative.LevelCalculus.level_pos T ψ ((generalLinearRestriction T m).obj D)
      have hl := Langlands.AllFieldBZ.Derivative.LevelCalculus.hasNonzeroDerivative_level T ψ _ hpos.ne'
      rw [hDj _ hl] at hl
      exact (Langlands.AllFieldBZ.Derivative.LevelCalculus.hasNonzeroDerivative_succ_iff_cast T ψ hm _).mp hl
    have hτ1 : level T ψ ((Langlands.AllFieldBZ.Derivative.MirabolicProductRestriction.restrictionQuotient T m n).obj (D, P)) ≤
        level T ψ ((generalLinearRestriction T n).obj P) :=
      (Langlands.AllFieldBZ.Derivative.LevelCalculus.level_mirabolicRankCast T ψ (show (m + 1) + n = m + n + 1 by omega)
        ((T.leftMixedProductFunctor (m + 1) n).obj
          (D, (generalLinearRestriction T n).obj P))).le.trans
        (level_leftMixed_le T ψ hLD _ _)
    have hτ2 := le_level_leftMixed T ψ hLD _ ((generalLinearRestriction T n).obj P) hQ
    have hup3 := hup2.trans (max_le hlevσ.le (hτ1.trans (hτ2.trans (Nat.le_add_right _ _))))
    omega

end Main
end RestrictedProductLevel
end Langlands.AllFieldBZ.Derivative
