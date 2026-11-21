import Langlands.Global.AdelicSplitComponentCentralizer
import Langlands.Global.AdelicL2HarishChandraDecomposition
import Langlands.Analysis.FundamentalDomainConstantTermInvariance
import Langlands.Analysis.InvariantTranslationOperator

/-! # Translated Harish-Chandra components on weighted `L²`

For a split-component point `b` of `A_J` and a weight `W` with `W ≤ κ W(b ·)`, translation by `b`
multiplies weighted `L²` norms of functions invariant under `P₀(F)` and `U_J(𝔸)` by at most
`(κ c(b))^{1/2}`. Applied to the Harish-Chandra components `Σ_{S ⊆ P} (−1)^{|P ∖ S|} CT_S`, whose
folded representatives have these invariances, this gives bounded operators "translate by `b` after
the component". The translation is the raw left shift `f ↦ f(b ·)`, without the modulus factor of
Bernstein–Lapid's twisted action `T_b`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Opposite
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicSubgroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν

/-- **Weighted `L²` bound.** Let `b` be the image of an adelic point `a` of `A_J`, let `f` be
measurable and left-invariant under `P₀(F)` and `U_J(𝔸)`, and let `W` be a measurable weight with the
same invariance and `W g ≤ κ W(b g)` for all `g`. Then
`∫_{D₀} ‖f(b g)‖² W(g) ≤ κ · c(b) · ∫_{D₀} ‖f‖² W`, with `c(b)` the Haar scaling factor of conjugation
by `b` on `U_J(𝔸)`. -/
theorem setLIntegral_enorm_sq_splitComponent_le (J : Idx)
    (a : (algSpec (CommRingCat.of F)).obj
      (op (CommAlgCat.of F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F))) ⟶
        (𝓕.A J).toGrp.X)
    {f : AdelicGroupPoints F G → ℂ} (hf : Measurable f)
    (hfΛ : ∀ l ∈ StandardConstantTerm.minimalParabolicImage F G 𝓕.i 𝓕.ν, ∀ x, f (l * x) = f x)
    (hfU : ∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J.1), ∀ x, f (w * x) = f x)
    {W : AdelicGroupPoints F G → ℝ≥0∞} (hW : Measurable W)
    (hWΛ : ∀ l ∈ StandardConstantTerm.minimalParabolicImage F G 𝓕.i 𝓕.ν, ∀ x, W (l * x) = W x)
    (hWU : ∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J.1), ∀ x, W (w * x) = W x)
    {κ : ℝ≥0∞} (hκ : ∀ g, W g ≤ κ * W ((a ≫ (𝓕.a J ≫ 𝓕.l J ≫ 𝓕.p J).hom.hom) * g)) :
    haveI hcl := StandardConstantTerm.isClosed_adelicPoints_standardUnipotent F G 𝓕.i 𝓕.ν J.1
    haveI : LocallyCompactSpace (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J.1)) :=
      hcl.locallyCompactSpace
    ∫⁻ g in LeftCosetSpace.fundamentalDomain
        (StandardConstantTerm.minimalParabolicImage F G 𝓕.i 𝓕.ν)
        (StandardConstantTerm.isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν),
        ‖f ((a ≫ (𝓕.a J ≫ 𝓕.l J ≫ 𝓕.p J).hom.hom) * g)‖ₑ ^ 2 * W g ∂Measure.haar ≤
      κ * (mulEquivHaarChar (StandardConstantTerm.conjPoints F G
            (a ≫ (𝓕.a J ≫ 𝓕.l J ≫ 𝓕.p J).hom.hom)
            (fun _ hw => 𝓕.splitComponent_conj_mem J _ a hw)
            (fun _ hw => 𝓕.splitComponent_conj_inv_mem J _ a hw)) : ℝ≥0∞) *
        ∫⁻ g in LeftCosetSpace.fundamentalDomain
          (StandardConstantTerm.minimalParabolicImage F G 𝓕.i 𝓕.ν)
          (StandardConstantTerm.isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν),
          ‖f g‖ₑ ^ 2 * W g ∂Measure.haar := by
  let hcl := StandardConstantTerm.isClosed_adelicPoints_standardUnipotent F G 𝓕.i 𝓕.ν J.1
  let : LocallyCompactSpace (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J.1)) :=
    hcl.locallyCompactSpace
  set b := a ≫ (𝓕.a J ≫ 𝓕.l J ≫ 𝓕.p J).hom.hom with hb
  let φ : AdelicGroupPoints F G → ℝ≥0∞ := fun g => ‖f g‖ₑ ^ 2 * W g
  have hφ : Measurable φ := (hf.enorm.pow_const 2).mul hW
  have hφΛ : ∀ l ∈ StandardConstantTerm.minimalParabolicImage F G 𝓕.i 𝓕.ν, ∀ x, φ (l * x) = φ x :=
    fun l hl x => by simp only [φ, hfΛ l hl x, hWΛ l hl x]
  have hφU : ∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J.1), ∀ x, φ (w * x) = φ x :=
    fun w hw x => by simp only [φ, hfU w hw x, hWU w hw x]
  have key := 𝓕.setLIntegral_splitComponent_mul_left_eq J a hφ hφΛ hφU
  calc ∫⁻ g in LeftCosetSpace.fundamentalDomain
          (StandardConstantTerm.minimalParabolicImage F G 𝓕.i 𝓕.ν)
          (StandardConstantTerm.isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν),
          ‖f (b * g)‖ₑ ^ 2 * W g ∂Measure.haar
      ≤ ∫⁻ g in LeftCosetSpace.fundamentalDomain
          (StandardConstantTerm.minimalParabolicImage F G 𝓕.i 𝓕.ν)
          (StandardConstantTerm.isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν),
          κ * φ (b * g) ∂Measure.haar := by
        refine lintegral_mono fun g => ?_
        calc ‖f (b * g)‖ₑ ^ 2 * W g ≤ ‖f (b * g)‖ₑ ^ 2 * (κ * W (b * g)) := by
              gcongr
              exact hκ g
          _ = κ * φ (b * g) := by simp only [φ]; ring
    _ = κ * ∫⁻ g in LeftCosetSpace.fundamentalDomain
          (StandardConstantTerm.minimalParabolicImage F G 𝓕.i 𝓕.ν)
          (StandardConstantTerm.isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν),
          φ (b * g) ∂Measure.haar :=
        lintegral_const_mul _ (hφ.comp (measurable_const_mul b))
    _ = _ := by rw [key, mul_assoc]


end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global.StandardConstantTerm

open Langlands.GroupScheme AdelicSubgroupPoints Langlands.Analysis.FibreAverage

variable (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The folded constant term along a standard unipotent radical `U_J` is, at every point,
left-invariant under `P₀(F)` and under `U_J(𝔸)`. -/
theorem foldConstantTerm_standard_invariant (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν) {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) (f : AdelicGroupPoints F G → ℂ) :
    haveI hcl := isClosed_adelicPoints_standardUnipotent F G i ν J
    haveI : LocallyCompactSpace (adelicPoints F G (standardUnipotent i ν J)) :=
      hcl.locallyCompactSpace
    (∀ l ∈ minimalParabolicImage F G i ν, ∀ x,
      foldConstantTerm (minimalParabolicImage F G i ν)
        (LeftCosetSpace.fundamentalDomain (minimalParabolicImage F G i ν)
          (isDiscrete_minimalParabolicImage F G i ν))
        (LeftCosetSpace.fundamentalDomain_unique _ (isDiscrete_minimalParabolicImage F G i ν))
        (adelicPoints F G (standardUnipotent i ν J)).subtype Measure.haar
        (ConstantTermAverage.rationalFundamentalDomain F G (standardUnipotent i ν J)) f (l * x) =
      foldConstantTerm (minimalParabolicImage F G i ν)
        (LeftCosetSpace.fundamentalDomain (minimalParabolicImage F G i ν)
          (isDiscrete_minimalParabolicImage F G i ν))
        (LeftCosetSpace.fundamentalDomain_unique _ (isDiscrete_minimalParabolicImage F G i ν))
        (adelicPoints F G (standardUnipotent i ν J)).subtype Measure.haar
        (ConstantTermAverage.rationalFundamentalDomain F G (standardUnipotent i ν J)) f x) ∧
    (∀ w ∈ adelicPoints F G (standardUnipotent i ν J), ∀ x,
      foldConstantTerm (minimalParabolicImage F G i ν)
        (LeftCosetSpace.fundamentalDomain (minimalParabolicImage F G i ν)
          (isDiscrete_minimalParabolicImage F G i ν))
        (LeftCosetSpace.fundamentalDomain_unique _ (isDiscrete_minimalParabolicImage F G i ν))
        (adelicPoints F G (standardUnipotent i ν J)).subtype Measure.haar
        (ConstantTermAverage.rationalFundamentalDomain F G (standardUnipotent i ν J)) f (w * x) =
      foldConstantTerm (minimalParabolicImage F G i ν)
        (LeftCosetSpace.fundamentalDomain (minimalParabolicImage F G i ν)
          (isDiscrete_minimalParabolicImage F G i ν))
        (LeftCosetSpace.fundamentalDomain_unique _ (isDiscrete_minimalParabolicImage F G i ν))
        (adelicPoints F G (standardUnipotent i ν J)).subtype Measure.haar
        (ConstantTermAverage.rationalFundamentalDomain F G (standardUnipotent i ν J)) f x) := by
  let U := standardUnipotent i ν J
  let hcl : IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G)) :=
    isClosed_adelicPoints_standardUnipotent F G i ν J
  let : LocallyCompactSpace (adelicPoints F G U) := hcl.locallyCompactSpace
  let : CompactSpace (RationalQuotient F G U) := compactSpace_standardUnipotent F G i ν hG hi hν J hJ
  let Λ := minimalParabolicImage F G i ν
  have hΛ := isDiscrete_minimalParabolicImage F G i ν
  let : Countable Λ := LeftCosetSpace.countable_of_isDiscrete Λ hΛ
  let : Countable (rationalSubgroup F G U) :=
    LeftCosetSpace.countable_of_isDiscrete _ (isDiscrete_rationalSubgroup F G U)
  have hΓ := And.intro
    (rationalSubgroup_standardUnipotent_le F G i ν (hG := hG) (hi := hi) (hν := hν) J hJ)
    (conj_rationalSubgroup_standardUnipotent F G i ν (hG := hG) (hi := hi) (hν := hν) J hJ)
  have hnorm := conj_adelicPoints_standardUnipotent F G i ν (hG := hG) (hi := hi) (hν := hν) J hJ
  let : (Measure.haar : Measure (adelicPoints F G U)).IsMulRightInvariant :=
    haar_isMulRightInvariant_of_compactRationalQuotient F G U
  have hC : IsFundamentalDomain (rationalSubgroup F G U)
      (ConstantTermAverage.rationalFundamentalDomain F G U) Measure.haar :=
    LeftCosetSpace.isFundamentalDomain _ (isDiscrete_rationalSubgroup F G U) _
  refine ⟨fun l hl x => ?_, fun w hw x => ?_⟩
  · exact foldConstantTerm_mul_left Λ _ (LeftCosetSpace.fundamentalDomain_unique Λ hΛ)
      (adelicPoints F G U).subtype Subtype.val_injective (rationalSubgroup F G U)
      (fun w hw => hΓ.1 w hw) (fun l => ConstantTermAverage.conjEquiv F G U Λ hnorm l)
      (fun _ _ => rfl)
      (fun l w hw =>
        (ConstantTermAverage.mem_rationalSubgroup_conjEquiv_iff F G U Λ hΓ hnorm l w).mp hw)
      Measure.haar (ConstantTermAverage.measurePreserving_conjEquiv F G U Λ hΓ hnorm) _ hC
      ⟨l, hl⟩ f x
  · exact foldConstantTerm_mul_left_j Λ _ (LeftCosetSpace.fundamentalDomain_unique Λ hΛ)
      (adelicPoints F G U).subtype (rationalSubgroup F G U) (fun w hw => hΓ.1 w hw)
      Measure.haar _ hC ⟨w, hw⟩ f x

end Langlands.Global.StandardConstantTerm

namespace Langlands.Global.HarishChandraDecomposition

/-- Finite sums in `Lp` are computed pointwise almost everywhere. -/
theorem coeFn_finset_sum_ae {X : Type*} [MeasurableSpace X] {m : Measure X} {I : Type*}
    (s : Finset I) (u : I → Lp ℂ 2 m) :
    ⇑(∑ i ∈ s, u i) =ᵐ[m] ∑ i ∈ s, ⇑(u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Lp.coeFn_zero ℂ 2 m
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (u a) (∑ i ∈ s, u i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Pi.add_apply]

/-- The alternating sum of operators applied to a class is almost everywhere the alternating sum
of representatives. -/
theorem alternatingSum_apply_ae {X : Type*} [MeasurableSpace X] {m : Measure X} {α : Type*}
    [DecidableEq α] (T : Finset α → (Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m)) (Fn : Lp ℂ 2 m)
    (h : Finset α → X → ℂ) (hT : ∀ S, ⇑(T S Fn) =ᵐ[m] h S) (P : Finset α) :
    ⇑(alternatingSum T P Fn) =ᵐ[m] alternatingSum h P := by
  unfold alternatingSum
  rw [FunLike.coe_sum, Finset.sum_apply]
  refine (coeFn_finset_sum_ae P.powerset _).trans ?_
  have hall : ∀ᵐ x ∂m, ∀ S ∈ P.powerset, (T S Fn : X → ℂ) x = h S x := by
    rw [Filter.eventually_all_finset]
    exact fun S _ => hT S
  have hsm : ∀ S ∈ P.powerset,
      ⇑(((-1 : ℂ) ^ (P \ S).card • T S) Fn) =ᵐ[m] (-1 : ℂ) ^ (P \ S).card • ⇑(T S Fn) :=
    fun S _ => Lp.coeFn_smul _ _
  have hsm' : ∀ᵐ x ∂m, ∀ S ∈ P.powerset, (((-1 : ℂ) ^ (P \ S).card • T S) Fn : X → ℂ) x =
      ((-1 : ℂ) ^ (P \ S).card • ⇑(T S Fn)) x := by
    rw [Filter.eventually_all_finset]
    exact hsm
  filter_upwards [hall, hsm'] with x h1 h2
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [h2 S hS, Pi.smul_apply, smul_eq_mul, h1 S hS]

end Langlands.Global.HarishChandraDecomposition

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicSubgroupPoints Langlands.Analysis.FibreAverage
open Langlands.Global.HarishChandraDecomposition Langlands.Global.StandardConstantTerm
open Classical

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

/-- The folded constant term along `U_{S ∩ Δ₀}`, for a finset `S`. -/
def componentFoldCT (S : Finset (characterLattice 𝓕.T)) (f : AdelicGroupPoints F G → ℂ) :
    AdelicGroupPoints F G → ℂ :=
  haveI hcl := isClosed_adelicPoints_standardUnipotent F G 𝓕.i 𝓕.ν (𝓕.finsetIndex S).1
  haveI : LocallyCompactSpace (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex S).1)) :=
    hcl.locallyCompactSpace
  foldConstantTerm (minimalParabolicImage F G 𝓕.i 𝓕.ν)
    (LeftCosetSpace.fundamentalDomain (minimalParabolicImage F G 𝓕.i 𝓕.ν)
      (isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν))
    (LeftCosetSpace.fundamentalDomain_unique _ (isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν))
    (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex S).1)).subtype Measure.haar
    (ConstantTermAverage.rationalFundamentalDomain F G
      (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex S).1)) f

theorem measurable_componentFoldCT (S : Finset (characterLattice 𝓕.T))
    {f : AdelicGroupPoints F G → ℂ} (hf : Measurable f) : Measurable (𝓕.componentFoldCT S f) := by
  let hcl := isClosed_adelicPoints_standardUnipotent F G 𝓕.i 𝓕.ν (𝓕.finsetIndex S).1
  let : LocallyCompactSpace (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex S).1)) :=
    hcl.locallyCompactSpace
  let : Countable (minimalParabolicImage F G 𝓕.i 𝓕.ν) :=
    LeftCosetSpace.countable_of_isDiscrete _ (isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν)
  let : CompactSpace (RationalQuotient F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex S).1)) :=
    compactSpace_standardUnipotent F G 𝓕.i 𝓕.ν 𝓕.connectedReductive 𝓕.maximalSplit 𝓕.generic _
      (𝓕.finsetIndex S).2
  let : (Measure.haar : Measure (adelicPoints F G
      (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex S).1))).IsMulRightInvariant :=
    haar_isMulRightInvariant_of_compactRationalQuotient F G _
  let : (Measure.haar : Measure (adelicPoints F G
      (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex S).1))).IsInvInvariant :=
    ConstantTermAverage.isInvInvariant_of_isMulRightInvariant _
  exact (stronglyMeasurable_foldConstantTerm (minimalParabolicImage F G 𝓕.i 𝓕.ν) _
    (LeftCosetSpace.measurableSet_fundamentalDomain _ (isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν))
    (LeftCosetSpace.fundamentalDomain_unique _ (isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν))
    (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex S).1)).subtype
    continuous_subtype_val.measurable Measure.haar _ hf).measurable

/-- For `S ⊆ P`, the folded constant term along `U_{S ∩ Δ₀}` is invariant under `P₀(F)` and under
`U_{P ∩ Δ₀}(𝔸)`, at every point. -/
theorem componentFoldCT_invariant {S P : Finset (characterLattice 𝓕.T)} (hSP : S ⊆ P)
    (f : AdelicGroupPoints F G → ℂ) :
    (∀ l ∈ minimalParabolicImage F G 𝓕.i 𝓕.ν, ∀ x,
      𝓕.componentFoldCT S f (l * x) = 𝓕.componentFoldCT S f x) ∧
    (∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1), ∀ x,
      𝓕.componentFoldCT S f (w * x) = 𝓕.componentFoldCT S f x) := by
  have h := foldConstantTerm_standard_invariant F G 𝓕.i 𝓕.ν 𝓕.connectedReductive 𝓕.maximalSplit
    𝓕.generic (𝓕.finsetIndex S).2 f
  have hsub : (𝓕.finsetIndex S).1 ⊆ (𝓕.finsetIndex P).1 := by
    intro x hx
    exact ⟨hSP hx.1, hx.2⟩
  have hle := (((standardParabolicOrder F G 𝓕.connectedReductive 𝓕.T 𝓕.i 𝓕.maximalSplit 𝓕.ν
    𝓕.generic).1 _ _ (𝓕.finsetIndex S).2 (𝓕.finsetIndex P).2).2 hsub).2
  exact ⟨h.1, fun w hw x => h.2 w (hle _ hw) x⟩

/-- **Translated Harish-Chandra components, for given constant-term operators.** For contractions
`T S` of `L²(μ_W)` computing the folded constant terms, "translate by `b` after the component
`Σ_{S ⊆ P} (−1)^{|P ∖ S|} T S`" is a continuous linear operator of norm at most
`(κ c(b))^{1/2} 2^{|P|}`, computed on every measurable representative. -/
theorem translatedComponent_of_operators (W : AdelicGroupPoints F G → ℝ≥0∞) (hW : Measurable W)
    (hWΛ : ∀ l ∈ minimalParabolicImage F G 𝓕.i 𝓕.ν, ∀ x, W (l * x) = W x)
    (hWU : ∀ J ⊆ simpleRelativeRoots 𝓕.i 𝓕.ν,
      ∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J), ∀ x, W (w * x) = W x)
    (T : Finset (characterLattice 𝓕.T) →
        (Lp ℂ 2 (𝓕.weightedHaar W) →L[ℂ] Lp ℂ 2 (𝓕.weightedHaar W)))
    (hT1 : ∀ S, ‖T S‖ ≤ 1)
    (hT2 : ∀ S (Fn : Lp ℂ 2 (𝓕.weightedHaar W)) {f : AdelicGroupPoints F G → ℂ}, Measurable f →
        f =ᵐ[𝓕.weightedHaar W] Fn → T S Fn =ᵐ[𝓕.weightedHaar W] 𝓕.componentFoldCT S f)
    (P : Finset (characterLattice 𝓕.T))
    (a : (algSpec (CommRingCat.of F)).obj
      (op (CommAlgCat.of F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F))) ⟶
        (𝓕.A (𝓕.finsetIndex P)).toGrp.X)
    {κ : ℝ≥0∞} (hκtop : κ ≠ ∞)
    (hκ : ∀ g, W g ≤ κ * W ((a ≫ (𝓕.a (𝓕.finsetIndex P) ≫ 𝓕.l (𝓕.finsetIndex P) ≫
      𝓕.p (𝓕.finsetIndex P)).hom.hom) * g)) :
    haveI hcl := isClosed_adelicPoints_standardUnipotent F G 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1
    haveI : LocallyCompactSpace (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1)) :=
      hcl.locallyCompactSpace
    ∃ L : Lp ℂ 2 (𝓕.weightedHaar W) →L[ℂ] Lp ℂ 2 (𝓕.weightedHaar W),
      ‖L‖ ≤ ((κ * (mulEquivHaarChar (conjPoints F G
          (a ≫ (𝓕.a (𝓕.finsetIndex P) ≫ 𝓕.l (𝓕.finsetIndex P) ≫ 𝓕.p (𝓕.finsetIndex P)).hom.hom)
          (fun _ hw => 𝓕.splitComponent_conj_mem (𝓕.finsetIndex P) _ a hw)
          (fun _ hw => 𝓕.splitComponent_conj_inv_mem (𝓕.finsetIndex P) _ a hw)) : ℝ≥0∞)) ^
            (1 / 2 : ℝ)).toReal * 2 ^ P.card ∧
      ∀ (Fn : Lp ℂ 2 (𝓕.weightedHaar W)) {f : AdelicGroupPoints F G → ℂ}, Measurable f →
        f =ᵐ[𝓕.weightedHaar W] Fn →
        L Fn =ᵐ[𝓕.weightedHaar W] fun g => alternatingSum (fun S => 𝓕.componentFoldCT S f) P
          ((a ≫ (𝓕.a (𝓕.finsetIndex P) ≫ 𝓕.l (𝓕.finsetIndex P) ≫
            𝓕.p (𝓕.finsetIndex P)).hom.hom) * g) := by
  let hcl := isClosed_adelicPoints_standardUnipotent F G 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1
  let : LocallyCompactSpace (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1)) :=
    hcl.locallyCompactSpace
  let Pinv : (AdelicGroupPoints F G → ℂ) → Prop := fun h =>
    (∀ l ∈ minimalParabolicImage F G 𝓕.i 𝓕.ν, ∀ x, h (l * x) = h x) ∧
    (∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1), ∀ x,
      h (w * x) = h x)
  have hsub : ∀ f g, Pinv f → Pinv g → Pinv (f - g) := fun f g hf hg =>
    ⟨fun l hl x => by simp only [Pi.sub_apply, hf.1 l hl x, hg.1 l hl x],
     fun w hw x => by simp only [Pi.sub_apply, hf.2 w hw x, hg.2 w hw x]⟩
  have hadd : ∀ f g, Pinv f → Pinv g → Pinv (f + g) := fun f g hf hg =>
    ⟨fun l hl x => by simp only [Pi.add_apply, hf.1 l hl x, hg.1 l hl x],
     fun w hw x => by simp only [Pi.add_apply, hf.2 w hw x, hg.2 w hw x]⟩
  have hsmul : ∀ (c : ℂ) f, Pinv f → Pinv (c • f) := fun c f hf =>
    ⟨fun l hl x => by simp only [Pi.smul_apply, hf.1 l hl x],
     fun w hw x => by simp only [Pi.smul_apply, hf.2 w hw x]⟩
  let c : ℝ≥0∞ := (mulEquivHaarChar (conjPoints F G
    (a ≫ (𝓕.a (𝓕.finsetIndex P) ≫ 𝓕.l (𝓕.finsetIndex P) ≫ 𝓕.p (𝓕.finsetIndex P)).hom.hom)
    (fun _ hw => 𝓕.splitComponent_conj_mem (𝓕.finsetIndex P) _ a hw)
    (fun _ hw => 𝓕.splitComponent_conj_inv_mem (𝓕.finsetIndex P) _ a hw)) : ℝ≥0∞)
  have hKtop : κ * c ≠ ∞ := ENNReal.mul_ne_top hκtop (by simp only [c]; exact ENNReal.coe_ne_top)
  have hbound : ∀ f, Measurable f → Pinv f →
      ∫⁻ g in LeftCosetSpace.fundamentalDomain (minimalParabolicImage F G 𝓕.i 𝓕.ν)
          (isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν),
          ‖f ((a ≫ (𝓕.a (𝓕.finsetIndex P) ≫ 𝓕.l (𝓕.finsetIndex P) ≫
            𝓕.p (𝓕.finsetIndex P)).hom.hom) * g)‖ₑ ^ 2 * W g ∂Measure.haar ≤
        κ * c * ∫⁻ g in LeftCosetSpace.fundamentalDomain (minimalParabolicImage F G 𝓕.i 𝓕.ν)
          (isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν), ‖f g‖ₑ ^ 2 * W g ∂Measure.haar :=
    fun f hf hP => 𝓕.setLIntegral_enorm_sq_splitComponent_le (𝓕.finsetIndex P) a hf hP.1 hP.2 hW
      hWΛ (hWU (𝓕.finsetIndex P).1 (𝓕.finsetIndex P).2) hκ
  have hrep : ∀ (Fn : Lp ℂ 2 (𝓕.weightedHaar W)) {f : AdelicGroupPoints F G → ℂ}, Measurable f →
      f =ᵐ[𝓕.weightedHaar W] Fn →
      Measurable (alternatingSum (fun S => 𝓕.componentFoldCT S f) P) ∧
      Pinv (alternatingSum (fun S => 𝓕.componentFoldCT S f) P) ∧
      alternatingSum (fun S => 𝓕.componentFoldCT S f) P =ᵐ[𝓕.weightedHaar W]
        alternatingSum T P Fn := by
    intro Fn f hf hfF
    refine ⟨?_, ⟨fun l hl x => ?_, fun w hw x => ?_⟩, ?_⟩
    · unfold alternatingSum
      have h := Finset.measurable_sum P.powerset
        (f := fun S => ((-1 : ℂ) ^ (P \ S).card) • 𝓕.componentFoldCT S f)
        fun S _ => (𝓕.measurable_componentFoldCT S hf).const_smul _
      convert h using 1
      funext x
      simp [Finset.sum_apply]
    · unfold alternatingSum
      simp only [Finset.sum_apply, Pi.smul_apply]
      exact Finset.sum_congr rfl fun S hS => by
        rw [(𝓕.componentFoldCT_invariant (Finset.mem_powerset.mp hS) f).1 l hl x]
    · unfold alternatingSum
      simp only [Finset.sum_apply, Pi.smul_apply]
      exact Finset.sum_congr rfl fun S hS => by
        rw [(𝓕.componentFoldCT_invariant (Finset.mem_powerset.mp hS) f).2 w hw x]
    · exact (alternatingSum_apply_ae T Fn (fun S => 𝓕.componentFoldCT S f)
        (fun S => hT2 S Fn hf hfF) P).symm
  have hTrep : ∀ Fn, ∃ h : AdelicGroupPoints F G → ℂ, Measurable h ∧ Pinv h ∧
      h =ᵐ[𝓕.weightedHaar W] alternatingSum T P Fn := fun Fn => by
    have hm := Lp.aestronglyMeasurable Fn
    obtain ⟨h1, h2, h3⟩ := hrep Fn hm.stronglyMeasurable_mk.measurable hm.ae_eq_mk.symm
    exact ⟨_, h1, h2, h3⟩
  refine ⟨Langlands.Analysis.InvariantTranslation.translateCLM
    (a ≫ (𝓕.a (𝓕.finsetIndex P) ≫ 𝓕.l (𝓕.finsetIndex P) ≫ 𝓕.p (𝓕.finsetIndex P)).hom.hom) Pinv (κ * c) hW hsub hadd hsmul
    hKtop hbound (alternatingSum T P) hTrep, ?_, fun Fn f hf hfF => ?_⟩
  · refine (Langlands.Analysis.InvariantTranslation.norm_translateCLM_le _ Pinv (κ * c) hW hsub
      hadd hsmul hKtop hbound (alternatingSum T P) hTrep).trans ?_
    exact mul_le_mul_of_nonneg_left (norm_alternatingSum_le T hT1 P) ENNReal.toReal_nonneg
  · obtain ⟨h1, h2, h3⟩ := hrep Fn hf hfF
    exact Langlands.Analysis.InvariantTranslation.translateCLM_ae _ Pinv (κ * c) hW hsub hadd
      hsmul hKtop hbound (alternatingSum T P) hTrep Fn h1 h2 h3



/-- **Translated Harish-Chandra components.** Let `W` be a measurable weight, left-invariant under
`P₀(F)` and every `U_J(𝔸)`, let `T` be the constant-term contractions of
`exists_componentOperators`, let `P` be a finset with `J = P ∩ Δ₀`, let `b` be the image of an adelic
point `a` of `A_J`, and let `W g ≤ κ W(b g)` for all `g`, with `κ < ∞`. Then
"translate by `b` after the component `Σ_{S ⊆ P} (−1)^{|P ∖ S|} T S`" is a continuous linear operator
of norm at most `(κ c(b))^{1/2} 2^{|P|}`, computed on every measurable representative `f` as
`g ↦ Σ_{S ⊆ P} (−1)^{|P ∖ S|} (CT_S f)(b g)`. -/
theorem exists_translatedComponent (W : AdelicGroupPoints F G → ℝ≥0∞) (hW : Measurable W)
    (hWΛ : ∀ l ∈ minimalParabolicImage F G 𝓕.i 𝓕.ν, ∀ x, W (l * x) = W x)
    (hWU : ∀ J ⊆ simpleRelativeRoots 𝓕.i 𝓕.ν,
      ∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J), ∀ x, W (w * x) = W x)
    (P : Finset (characterLattice 𝓕.T))
    (a : (algSpec (CommRingCat.of F)).obj
      (op (CommAlgCat.of F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F))) ⟶
        (𝓕.A (𝓕.finsetIndex P)).toGrp.X)
    {κ : ℝ≥0∞} (hκtop : κ ≠ ∞)
    (hκ : ∀ g, W g ≤ κ * W ((a ≫ (𝓕.a (𝓕.finsetIndex P) ≫ 𝓕.l (𝓕.finsetIndex P) ≫
      𝓕.p (𝓕.finsetIndex P)).hom.hom) * g)) :
    haveI hcl := isClosed_adelicPoints_standardUnipotent F G 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1
    haveI : LocallyCompactSpace (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1)) :=
      hcl.locallyCompactSpace
    ∃ T : Finset (characterLattice 𝓕.T) →
        (Lp ℂ 2 (𝓕.weightedHaar W) →L[ℂ] Lp ℂ 2 (𝓕.weightedHaar W)),
      (∀ S, ‖T S‖ ≤ 1) ∧
      (∀ S (Fn : Lp ℂ 2 (𝓕.weightedHaar W)) {f : AdelicGroupPoints F G → ℂ}, Measurable f →
        f =ᵐ[𝓕.weightedHaar W] Fn → T S Fn =ᵐ[𝓕.weightedHaar W] 𝓕.componentFoldCT S f) ∧
      T 𝓕.simpleRootFinset = ContinuousLinearMap.id ℂ _ ∧
      ∃ L : Lp ℂ 2 (𝓕.weightedHaar W) →L[ℂ] Lp ℂ 2 (𝓕.weightedHaar W),
        ‖L‖ ≤ ((κ * (mulEquivHaarChar (conjPoints F G
            (a ≫ (𝓕.a (𝓕.finsetIndex P) ≫ 𝓕.l (𝓕.finsetIndex P) ≫ 𝓕.p (𝓕.finsetIndex P)).hom.hom)
            (fun _ hw => 𝓕.splitComponent_conj_mem (𝓕.finsetIndex P) _ a hw)
            (fun _ hw => 𝓕.splitComponent_conj_inv_mem (𝓕.finsetIndex P) _ a hw)) : ℝ≥0∞)) ^
              (1 / 2 : ℝ)).toReal * 2 ^ P.card ∧
        ∀ (Fn : Lp ℂ 2 (𝓕.weightedHaar W)) {f : AdelicGroupPoints F G → ℂ}, Measurable f →
          f =ᵐ[𝓕.weightedHaar W] Fn →
          L Fn =ᵐ[𝓕.weightedHaar W] fun g => alternatingSum (fun S => 𝓕.componentFoldCT S f) P
            ((a ≫ (𝓕.a (𝓕.finsetIndex P) ≫ 𝓕.l (𝓕.finsetIndex P) ≫
              𝓕.p (𝓕.finsetIndex P)).hom.hom) * g) := by
  let hcl := isClosed_adelicPoints_standardUnipotent F G 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1
  let : LocallyCompactSpace (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1)) :=
    hcl.locallyCompactSpace
  obtain ⟨T, hT1, hT2, hT3⟩ := 𝓕.exists_componentOperators W hW hWΛ hWU
  exact ⟨T, hT1, fun S Fn f hf hfF => hT2 S Fn hf hfF, hT3,
    𝓕.translatedComponent_of_operators W hW hWΛ hWU T hT1 (fun S Fn f hf hfF => hT2 S Fn hf hfF)
      P a hκtop hκ⟩

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open Langlands.GroupScheme AdelicSubgroupPoints Langlands.Analysis.FibreAverage
open Langlands.Global.HarishChandraDecomposition Langlands.Global.StandardConstantTerm
open Classical

/-- **Statement form** of `StandardParabolicFamily.exists_translatedComponent`. -/
def TranslatedComponentStatement : Prop :=
  ∀ {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (𝓕 : StandardParabolicFamily F G) (W : AdelicGroupPoints F G → ℝ≥0∞) (_hW : Measurable W)
    (_hWΛ : ∀ l ∈ minimalParabolicImage F G 𝓕.i 𝓕.ν, ∀ x, W (l * x) = W x)
    (_hWU : ∀ J ⊆ simpleRelativeRoots 𝓕.i 𝓕.ν,
      ∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J), ∀ x, W (w * x) = W x)
    (P : Finset (characterLattice 𝓕.T))
    (a : (algSpec (CommRingCat.of F)).obj
      (op (CommAlgCat.of F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F))) ⟶
        (𝓕.A (𝓕.finsetIndex P)).toGrp.X)
    {κ : ℝ≥0∞} (_hκtop : κ ≠ ∞)
    (_hκ : ∀ g, W g ≤ κ * W ((a ≫ (𝓕.a (𝓕.finsetIndex P) ≫ 𝓕.l (𝓕.finsetIndex P) ≫
      𝓕.p (𝓕.finsetIndex P)).hom.hom) * g)),
    haveI hcl := isClosed_adelicPoints_standardUnipotent F G 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1
    haveI : LocallyCompactSpace (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν (𝓕.finsetIndex P).1)) :=
      hcl.locallyCompactSpace
    ∃ T : Finset (characterLattice 𝓕.T) →
        (Lp ℂ 2 (𝓕.weightedHaar W) →L[ℂ] Lp ℂ 2 (𝓕.weightedHaar W)),
      (∀ S, ‖T S‖ ≤ 1) ∧
      (∀ S (Fn : Lp ℂ 2 (𝓕.weightedHaar W)) {f : AdelicGroupPoints F G → ℂ}, Measurable f →
        f =ᵐ[𝓕.weightedHaar W] Fn → T S Fn =ᵐ[𝓕.weightedHaar W] 𝓕.componentFoldCT S f) ∧
      T 𝓕.simpleRootFinset = ContinuousLinearMap.id ℂ _ ∧
      ∃ L : Lp ℂ 2 (𝓕.weightedHaar W) →L[ℂ] Lp ℂ 2 (𝓕.weightedHaar W),
        ‖L‖ ≤ ((κ * (mulEquivHaarChar (conjPoints F G
            (a ≫ (𝓕.a (𝓕.finsetIndex P) ≫ 𝓕.l (𝓕.finsetIndex P) ≫ 𝓕.p (𝓕.finsetIndex P)).hom.hom)
            (fun _ hw => 𝓕.splitComponent_conj_mem (𝓕.finsetIndex P) _ a hw)
            (fun _ hw => 𝓕.splitComponent_conj_inv_mem (𝓕.finsetIndex P) _ a hw)) : ℝ≥0∞)) ^
              (1 / 2 : ℝ)).toReal * 2 ^ P.card ∧
        ∀ (Fn : Lp ℂ 2 (𝓕.weightedHaar W)) {f : AdelicGroupPoints F G → ℂ}, Measurable f →
          f =ᵐ[𝓕.weightedHaar W] Fn →
          L Fn =ᵐ[𝓕.weightedHaar W] fun g => alternatingSum (fun S => 𝓕.componentFoldCT S f) P
            ((a ≫ (𝓕.a (𝓕.finsetIndex P) ≫ 𝓕.l (𝓕.finsetIndex P) ≫
              𝓕.p (𝓕.finsetIndex P)).hom.hom) * g)

/-- Proof of `TranslatedComponentStatement`. -/
theorem translatedComponent : TranslatedComponentStatement.{u} :=
  fun 𝓕 W hW hWΛ hWU P a _ hκtop hκ => 𝓕.exists_translatedComponent W hW hWΛ hWU P a hκtop hκ

end Langlands.Global
