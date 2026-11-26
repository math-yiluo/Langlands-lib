import Langlands.Analysis.Local.QuotientMeasure
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The right regular representation on `L²(Γ \ G)`

For a topological group `G`, a subgroup `Γ` and a measure `ν` on the left coset space `Γ \ G`
preserved by every right translation `Γ x ↦ Γ x g`, right translation of square-integrable
classes, `(R(g) φ)(Γ x) = φ(Γ x g)`, is a homomorphism from `G` to the bounded operators on
`L²(Γ \ G, ν)` by linear isometries. When `ν` is regular and `Γ \ G` is Hausdorff, every orbit
map `g ↦ R(g) φ` is continuous, hence strongly measurable for a Borel measure on a second
countable `G`. These are the hypotheses on the representation in the Library's abstract simple
twisted trace formula and in the comparison of the positive and norm-one quotients.
-/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory Filter
open Langlands.QuotientIntegration

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (Γ : Subgroup G)

/-- Right translation `(Γ x, g) ↦ Γ x g` is jointly continuous. -/
theorem continuous_rightTranslate_uncurry :
    Continuous (fun p : G × LeftQuotient Γ => rightTranslate Γ p.1 p.2) := by
  rw [← (IsOpenQuotientMap.id.prodMap (leftQuotient_isOpenQuotientMap Γ)).continuous_comp_iff]
  exact continuous_quotient_mk'.comp (continuous_snd.mul continuous_fst)

variable [MeasurableSpace (LeftQuotient Γ)] (ν : Measure (LeftQuotient Γ))
  (hν : ∀ g : G, MeasurePreserving (rightTranslate Γ g) ν ν)

/-- Right translation by `g` on `L²(Γ \ G, ν)`: `φ ↦ φ(· g)`. -/
def quotientRightTranslateL2 (g : G) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
  (Lp.compMeasurePreservingₗᵢ ℂ (rightTranslate Γ g) (hν g)).toContinuousLinearMap

/-- The right regular representation of `G` on `L²(Γ \ G, ν)`. -/
def quotientRightRegular : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) where
  toFun := quotientRightTranslateL2 Γ ν hν
  map_one' := by
    refine ContinuousLinearMap.ext fun φ => ?_
    change Lp.compMeasurePreserving (rightTranslate Γ 1) (hν 1) φ = φ
    refine Lp.ext ((Lp.coeFn_compMeasurePreserving φ (hν 1)).trans
      (Eventually.of_forall fun q => ?_))
    simp only [Function.comp_apply, rightTranslate_one]
  map_mul' g h := by
    refine ContinuousLinearMap.ext fun φ => ?_
    change Lp.compMeasurePreserving (rightTranslate Γ (g * h)) (hν (g * h)) φ =
      Lp.compMeasurePreserving (rightTranslate Γ g) (hν g)
        (Lp.compMeasurePreserving (rightTranslate Γ h) (hν h) φ)
    refine Lp.ext ((Lp.coeFn_compMeasurePreserving φ (hν (g * h))).trans ?_)
    refine EventuallyEq.symm ((Lp.coeFn_compMeasurePreserving _ (hν g)).trans ?_)
    refine ((hν g).quasiMeasurePreserving.ae_eq_comp
      (Lp.coeFn_compMeasurePreserving φ (hν h))).trans (Eventually.of_forall fun q => ?_)
    simp only [Function.comp_apply, rightTranslate_mul]

theorem quotientRightRegular_apply (g : G) (φ : Lp ℂ 2 ν) :
    quotientRightRegular Γ ν hν g φ =
      Lp.compMeasurePreserving (rightTranslate Γ g) (hν g) φ := rfl

/-- Each `R(g)` is an isometry. -/
theorem norm_quotientRightRegular_apply (g : G) (φ : Lp ℂ 2 ν) :
    ‖quotientRightRegular Γ ν hν g φ‖ = ‖φ‖ :=
  Lp.norm_compMeasurePreserving φ (hν g)

/-- `R(g) φ` is almost everywhere the function `Γ x ↦ φ(Γ x g)`. -/
theorem quotientRightRegular_coeFn (g : G) (φ : Lp ℂ 2 ν) :
    (quotientRightRegular Γ ν hν g φ : LeftQuotient Γ → ℂ) =ᵐ[ν]
      fun q => φ (rightTranslate Γ g q) :=
  Lp.coeFn_compMeasurePreserving φ (hν g)

variable [BorelSpace (LeftQuotient Γ)] [R1Space (LeftQuotient Γ)]
  [ν.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure ν]

/-- The orbit map `g ↦ R(g) φ` is continuous. -/
theorem continuous_quotientRightRegular_apply (φ : Lp ℂ 2 ν) :
    Continuous fun g : G => quotientRightRegular Γ ν hν g φ := by
  let r : C(G × LeftQuotient Γ, LeftQuotient Γ) :=
    ⟨fun p => rightTranslate Γ p.1 p.2, continuous_rightTranslate_uncurry Γ⟩
  exact continuous_const.compMeasurePreservingLp r.curry.continuous (fun g => hν g)
    (by simp)

/-- The orbit map `g ↦ R(g) φ` is strongly measurable for every measure on a second countable
Borel group. -/
theorem aestronglyMeasurable_quotientRightRegular_apply [SecondCountableTopology G]
    [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) (φ : Lp ℂ 2 ν) :
    AEStronglyMeasurable (fun g : G => quotientRightRegular Γ ν hν g φ) μ :=
  (continuous_quotientRightRegular_apply Γ ν hν φ).aestronglyMeasurable

end Langlands.TraceFormula
