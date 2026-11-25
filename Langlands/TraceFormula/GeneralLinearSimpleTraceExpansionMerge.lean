import Langlands.TraceFormula.GeneralLinearTensorSimpleTraceFormulaStatement
import Langlands.TraceFormula.SimpleTraceGeometricExpansionSum
import Langlands.Global.AdelicNormOneDecomposition

/-!
# The simple trace formula for `GL_n` on a finite sum of functions with their own expansions

* `integrable_comp_positivePointMap_mul`: for `g` continuous with compact support on `G(𝔸_F)` and
  `z ∈ G(𝔸_F)¹`, `a ↦ g(a z)` is integrable on `A⁺`, so the positive average `f¹` of a finite sum is
  the sum of the averages.
* `generalLinearSimpleTraceExpansion_finsetSum`: if `f = ∑ₖ gₖ` with every `gₖ` continuous with
  compact support and satisfying `GeneralLinearSimpleTraceExpansion` (each with its own family of
  representatives), `R(f)` is trace class and `tr R(f) = ∑ₖ tr R(gₖ)`, then `f` satisfies
  `GeneralLinearSimpleTraceExpansion`, with one family of representatives
  (`exists_simpleTraceGeometricExpansion_sum`).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.QuotientIntegration Langlands.JacquetLanglands
open Langlands.Analysis.OperatorIdeals

namespace Langlands.TraceFormula

/-- For `g` continuous with compact support on `G(𝔸_F)` and a norm-one point `z`, the function
`a ↦ g(a z)` on the positive points `A⁺` of the central torus is integrable for the normalized Haar
measure. It is continuous, and its support lies in the first projection of the compact set
`D⁻¹(supp g)`, where `D : A⁺ × G(𝔸_F)¹ ≃ G(𝔸_F)` is `normOneDecomposition`. -/
theorem integrable_comp_positivePointMap_mul (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
    (hc : IsCentral i) {g : AdelicGroupPoints F G → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (z : normOneSubgroup F G) :
    Integrable (fun a => g (positivePointMap F G T i a * (z : AdelicGroupPoints F G)))
      (normalizedPositiveHaarMeasure F G T i hi I e hc) := by
  let D := normOneDecomposition F G T i hi I e
  have := positiveIsTopologicalGroup F T I e
  have := normalizedPositiveHaarMeasure_isHaarMeasure F G T i hi I e hc
  have hslice : Continuous (fun a : intrinsicSubgroup F T => D (a, z)) :=
    D.continuous.comp (continuous_id.prodMk continuous_const)
  refine (hg.comp hslice).integrable_of_hasCompactSupport ?_
  have hK : IsCompact (Prod.fst '' (D.symm '' tsupport g)) :=
    (hgc.image D.symm.continuous).image continuous_fst
  have hclosed : IsClosed {a : intrinsicSubgroup F T | D (a, z) ∈ tsupport g} :=
    (isClosed_tsupport g).preimage hslice
  refine HasCompactSupport.intro' (hK.of_isClosed_subset hclosed ?_) hclosed ?_
  · intro a ha
    exact ⟨(a, z), ⟨D (a, z), ha, D.symm_apply_apply _⟩, rfl⟩
  · intro a ha
    change g (D (a, z)) = 0
    exact image_eq_zero_of_notMem_tsupport ha

local instance generalLinearExpansionMergeIsAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance generalLinearExpansionMergeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

set_option hygiene false in
/-- The `GL_n` group scheme over `F`, for the bound variables `F` and `n`. -/
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

/-- **One expansion for a finite sum.** Let `f = ∑ₖ gₖ` on `GL_n(𝔸_F)`, where every `gₖ` is
continuous with compact support and satisfies the simple trace formula at `v`
(`GeneralLinearSimpleTraceExpansion`) with its own family of representatives. If `R(f)` is trace
class and `tr R(f) = ∑ₖ tr R(gₖ)`, then `f` satisfies the simple trace formula at `v`, with one
family of representatives chosen among those of the pieces. -/
theorem generalLinearSimpleTraceExpansion_finsetSum (F : Type u) [Field F] [NumberField F] (n : ℕ)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ GLₙ)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F GLₙ)).IsMulRightInvariant]
    (v : Langlands.Global.FinitePlace F) {f : AdelicGroupPoints F GLₙ → ℂ}
    (h : Integrable f (Measure.haar : Measure (AdelicGroupPoints F GLₙ))) {N : ℕ}
    (g : Fin N → AdelicGroupPoints F GLₙ → ℂ) (hgc : ∀ k, Continuous (g k))
    (hgs : ∀ k, HasCompactSupport (g k))
    (hg : ∀ k, Integrable (g k) (Measure.haar : Measure (AdelicGroupPoints F GLₙ)))
    (hfg : ∀ x, f x = ∑ k, g k x)
    (hexp : ∀ k, GeneralLinearSimpleTraceExpansion F n T i hi I e hc v (g k) (hg k))
    (htc : IsTraceClass (haarQuotientL2IntegratedAction F GLₙ T i hi I e hc Measure.haar f h))
    (htr : operatorTrace (haarQuotientL2IntegratedAction F GLₙ T i hi I e hc Measure.haar f h) =
      ∑ k, operatorTrace (haarQuotientL2IntegratedAction F GLₙ T i hi I e hc Measure.haar (g k)
        (hg k))) :
    GeneralLinearSimpleTraceExpansion F n T i hi I e hc v f h := by
  let ρ := normalizedPositiveHaarMeasure F GLₙ T i hi I e hc
  let gOne : Fin N → normOneSubgroup F GLₙ → ℂ := fun k x =>
    ∫ a, g k (positivePointMap F GLₙ T i a * (x : AdelicGroupPoints F GLₙ)) ∂ρ
  have hsplit (x : normOneSubgroup F GLₙ) :
      (∫ a, f (positivePointMap F GLₙ T i a * (x : AdelicGroupPoints F GLₙ)) ∂ρ) =
        ∑ k, gOne k x := by
    simp_rw [hfg]
    exact integral_finsetSum _ fun k _ =>
      integrable_comp_positivePointMap_mul F GLₙ T i hi I e hc (hgc k) (hgs k) x
  have hpieces (k : Fin N) := (hexp k).2
  obtain ⟨m, r, hd, hP, hcov, hblock⟩ := exists_simpleTraceGeometricExpansion_sum
    (rationalNormOneSubgroup F GLₙ) (Measure.haar : Measure (normOneSubgroup F GLₙ))
    (fun x : normOneSubgroup F GLₙ => IsRegularElliptic (FiniteAdelicGL.localProjection F n v
      (AdelicGL.finite F n (GeneralLinearGroupPoints.adelicHomeomorph F n
        (x : AdelicGroupPoints F GLₙ)))))
    gOne (fun k => operatorTrace (haarQuotientL2IntegratedAction F GLₙ T i hi I e hc
      Measure.haar (g k) (hg k))) hpieces
  have hfOne : (fun x => ∑ k, gOne k x) = fun x : normOneSubgroup F GLₙ =>
      ∫ a, f (positivePointMap F GLₙ T i a * (x : AdelicGroupPoints F GLₙ)) ∂ρ :=
    funext fun x => (hsplit x).symm
  rw [hfOne, ← htr] at hblock
  refine ⟨htc, m, r, hd, hP, fun q hq hx => hcov q hq ?_, hblock⟩
  obtain ⟨x, hx⟩ := hx
  exact ⟨x, by rwa [← hsplit]⟩

end Langlands.TraceFormula
