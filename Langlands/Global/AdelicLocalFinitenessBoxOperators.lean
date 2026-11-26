import Langlands.Global.AdelicHarishChandraBoundaryCompact
import Langlands.Global.AdelicFoldConstantTermBridge
import Langlands.Global.AdelicLocalFinitenessResidualOperators

/-! # Compact Harish-Chandra restrictions to boxes on the weighted Siegel space

The compact Harish-Chandra restriction of `AdelicHarishChandraBoundaryCompact`, for the box of
a component and an orthant, transported from the rational quotient `P₀(F) \ G(𝔸)` to the
fundamental domain of `P₀(F)` in `G(𝔸)` with the Siegel weight in chamber coordinates.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal NNReal

namespace Langlands.Global.WeightedSiegel

open AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

/-- Restricting the frame measure of a height region `S₁` to the heights in `S₂` gives the frame
measure of `S₁ ∩ S₂`. -/
theorem frameMeasure_restrict_height (ell : RealCharacterDual F P → ℝ)
    (S₁ S₂ : Set (RealCharacterDual F P)) (hS₂ : @MeasurableSet _ (borel _) S₂) :
    (frameMeasure hK ell S₁).restrict (hK.height ⁻¹' S₂) = frameMeasure hK ell (S₁ ∩ S₂) := by
  let : MeasurableSpace (RealCharacterDual F P) := borel _
  have : BorelSpace (RealCharacterDual F P) := ⟨rfl⟩
  have hm : MeasurableSet (hK.height ⁻¹' S₂) := hK.continuous_height.measurable hS₂
  rw [frameMeasure, frameMeasure, restrict_withDensity hm, ← withDensity_indicator hm]
  congr 1
  funext g
  unfold chamberDensity
  rw [indicator_indicator, preimage_inter, inter_comm]

end Langlands.Global.WeightedSiegel

namespace Langlands.Global.StandardConstantTerm

/-- The coordinate box of `orthantBox`: `orthantBox c = c⁻¹ (orthantBox id)`. -/
theorem orthantBox_eq_preimage {X D : Type*} {r : ℕ} (c : X → (D → ℝ) × (Fin r → ℝ))
    (τ : D → ℝ) (J : D → Prop) (ε : Fin r → Bool) (m : ({β : D // ¬ J β} ⊕ Fin r) → ℕ) :
    orthantBox c τ J ε m = c ⁻¹' orthantBox id τ J ε m := by
  ext g
  simp only [orthantBox, mem_ofPred_eq, mem_preimage]
  refine forall_congr' fun k => ?_
  rcases k with β | j <;> rfl

theorem measurableSet_orthantBox_id {D : Type*} [Fintype D] {r : ℕ} (τ : D → ℝ) (J : D → Prop)
    (ε : Fin r → Bool) (m : ({β : D // ¬ J β} ⊕ Fin r) → ℕ) :
    MeasurableSet (orthantBox (id : (D → ℝ) × (Fin r → ℝ) → (D → ℝ) × (Fin r → ℝ)) τ J ε m) := by
  have hfin : Finite ({β : D // ¬ J β} ⊕ Fin r) := inferInstance
  have hc (k : {β : D // ¬ J β} ⊕ Fin r) :
      Measurable (orthantHeight (id : (D → ℝ) × (Fin r → ℝ) → (D → ℝ) × (Fin r → ℝ)) τ J ε k) := by
    rcases k with β | j
    · exact ((measurable_pi_apply β.1).comp measurable_fst).sub_const _
    · simp only [orthantHeight, Sum.elim_inr, orthantCoord]
      split_ifs
      · exact ((measurable_pi_apply j).comp measurable_snd).add_const _
      · exact ((measurable_pi_apply j).comp measurable_snd).neg.add_const _
  have : orthantBox (id : (D → ℝ) × (Fin r → ℝ) → (D → ℝ) × (Fin r → ℝ)) τ J ε m =
      ⋂ k, ({x | 0 < orthantHeight id τ J ε k x} ∩ {x | orthantHeight id τ J ε k x ≤ m k}) := by
    ext x
    simp [orthantBox]
  rw [this]
  exact MeasurableSet.iInter fun k =>
    (measurableSet_lt measurable_const (hc k)).inter (measurableSet_le (hc k) measurable_const)

/-- The heights of the box `orthantBox` inside the Siegel region, as a subset of the source of
the coordinate map `e`: `e⁻¹(siegelRegion τ) ∩ e⁻¹(orthantBox id τ J ε m)`. -/
def boxHeightRegion {V D : Type*} {r : ℕ} (e : V → (D → ℝ) × (Fin r → ℝ)) (τ : D → ℝ)
    (J : D → Prop) (ε : Fin r → Bool) (m : ({β : D // ¬ J β} ⊕ Fin r) → ℕ) : Set V :=
  e ⁻¹' siegelRegion τ ∩ e ⁻¹' orthantBox id τ J ε m

theorem measurableSet_siegelRegion {D : Type*} [Fintype D] {r : ℕ} (τ : D → ℝ) :
    MeasurableSet (siegelRegion (r := r) τ) := by
  have : siegelRegion (r := r) τ = ⋂ β, {x : (D → ℝ) × (Fin r → ℝ) | τ β < x.1 β} := by
    ext x
    simp [siegelRegion]
  rw [this]
  exact MeasurableSet.iInter fun β =>
    measurableSet_lt measurable_const ((measurable_pi_apply β).comp measurable_fst)

end Langlands.Global.StandardConstantTerm

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicSubgroupPoints AdelicGroupPoints AdelicSiegelFactors
  PositiveRealTorus Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Global.HarishChandraDecomposition Langlands.Global.StandardConstantTerm
open Classical

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

private instance : IsClosedImmersion (Standard.parabolicHom 𝓕.i 𝓕.ν ∅).hom.hom.left :=
  Standard.isClosedSubgroup_parabolicHom 𝓕.i 𝓕.ν ∅

private instance : IsAffine (Standard.parabolicScheme 𝓕.i 𝓕.ν ∅).X.left :=
  isAffine_of_isAffineHom (Standard.parabolicHom 𝓕.i 𝓕.ν ∅).hom.hom.left

/-- On a measurable `P₀(F)`-invariant function the Harish-Chandra component is the alternating
sum of the folded constant terms. -/
theorem hcComponent_eq_alternatingSum_componentFoldCT (P : Finset (characterLattice 𝓕.T))
    {φ : AdelicGroupPoints F G → ℂ} (hφ : Measurable φ)
    (hinv : ∀ l ∈ minimalParabolicImage F G 𝓕.i 𝓕.ν, ∀ x, φ (l * x) = φ x) :
    𝓕.hcComponent P φ = alternatingSum (fun S => 𝓕.componentFoldCT S φ) P := by
  unfold hcComponent alternatingSum
  refine Finset.sum_congr rfl fun S _ => ?_
  congr 1
  funext g
  exact 𝓕.constantTerm_eq_foldConstantTerm (𝓕.finsetIndex S) hφ hinv g

/-- On a measurable `P₀(F)`-invariant function the Harish-Chandra component is `P₀(F)`-invariant. -/
theorem hcComponent_minimalParabolicImage_mul (P : Finset (characterLattice 𝓕.T))
    {φ : AdelicGroupPoints F G → ℂ} (hφ : Measurable φ)
    (hinv : ∀ l ∈ minimalParabolicImage F G 𝓕.i 𝓕.ν, ∀ x, φ (l * x) = φ x)
    {l : AdelicGroupPoints F G} (hl : l ∈ minimalParabolicImage F G 𝓕.i 𝓕.ν)
    (g : AdelicGroupPoints F G) : 𝓕.hcComponent P φ (l * g) = 𝓕.hcComponent P φ g := by
  rw [𝓕.hcComponent_eq_alternatingSum_componentFoldCT P hφ hinv]
  unfold alternatingSum
  simp only [Finset.sum_apply, Pi.smul_apply]
  exact Finset.sum_congr rfl fun S hS => by
    rw [(𝓕.componentFoldCT_invariant (Finset.mem_powerset.mp hS) φ).1 l hl g]

variable {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (j : T₀ ⟶ 𝓕.T)
  {d N : ℕ} (hG : SmoothOfRelativeDimension d G.X.hom) (rho : MatrixRepresentation G (Fin N))
  (hcalc : AdelicDifferentialCommutator F G hG) (hN : 0 < N) (hrho : IsClosedSubgroup rho)

/-- The function of an element of a uniform-growth space is measurable and `P₀(F)`-invariant. -/
theorem toFun_measurable_invariant {R : ℝ} {L : Subgroup (FiniteAdelicGroupPoints F G)}
    (v : UniformGrowthFrechetSpace F G rho hG hcalc hN hrho R L) :
    Measurable (UniformGrowthFrechetSpace.toFun F G rho hG hcalc hN hrho R L v) ∧
      ∀ l ∈ minimalParabolicImage F G 𝓕.i 𝓕.ν, ∀ x,
        UniformGrowthFrechetSpace.toFun F G rho hG hcalc hN hrho R L v (l * x) =
          UniformGrowthFrechetSpace.toFun F G rho hG hcalc hN hrho R L v x := by
  refine ⟨(v : uniformGrowthLevelSubmodule F G rho hG hcalc R L).val.val.property.measurable,
    fun l hl x => ?_⟩
  obtain ⟨q, hq⟩ := minimalParabolicImage_le F G 𝓕.i 𝓕.ν hl
  rw [← hq]
  exact evaluate_rational_mul F G _ q x

/-- **Compact Harish-Chandra restriction to a box on the weighted Siegel space.** In the setting
of `AdelicHarishChandraBoundaryCompactStatement` there is `c > 0` such that for all rates
`ra_β, rb_j ≥ c`, thresholds `τ`, every finset `P`, orthant `ε` and degrees `m`, every growth
exponent `R ≥ 0`, open level `L` and continuous linear map `smooth : E → 𝔉^R_L` from a Hilbert
space, there is a compact operator `T` from `E` to `L²` of the Siegel weight restricted to the box
`orthantBox (chamberCoords hK e) τ J_P ε m`, with `T q` almost everywhere the Harish-Chandra
component `𝓕.hcComponent P` of the function of `smooth q`. -/
theorem exists_boxBoundaryOperator [Fintype (simpleRelativeRoots 𝓕.i 𝓕.ν)]
    [DecidableEq (simpleRelativeRoots 𝓕.i 𝓕.ν)] {r : ℕ}
    (dT : RealCharacterDual F 𝓕.T.toGrp ≃L[ℝ] RealCharacterDual F (Standard.parabolicScheme 𝓕.i 𝓕.ν ∅))
    (e : RealCharacterDual F (Standard.parabolicScheme 𝓕.i 𝓕.ν ∅) ≃L[ℝ]
      ((simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ) × (Fin r → ℝ)))
    (step : simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ)
    (hRed : IsConnectedReductive G) (hsetup : IsSiegelAlgebraicSetup F G 𝓕.T 𝓕.i 𝓕.ν T₀ j)
    (hd : ∀ h, dT h = realCharacterDualMap F 𝓕.T.toGrp (Standard.parabolicScheme 𝓕.i 𝓕.ν ∅)
      (torusToStandardParabolic F G 𝓕.T 𝓕.i 𝓕.ν) h)
    (hstep : ∀ α, 0 < step α)
    (hRoot : ∀ (h : RealCharacterDual F 𝓕.T.toGrp) (α : simpleRelativeRoots 𝓕.i 𝓕.ν),
      (e (dT h)).1 α = h α.val / step α)
    (hCen : ∀ h : RealCharacterDual F 𝓕.T.toGrp, (e (dT h)).2 = 0 →
      realCharacterDualMap F 𝓕.T.toGrp G 𝓕.i h = 0)
    {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (Standard.parabolicHom 𝓕.i 𝓕.ν ∅) K) :
    ∃ c : ℝ, 0 < c ∧ ∀ (ra : simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ) (rb : Fin r → ℝ),
      (∀ β, c ≤ ra β) → (∀ k, c ≤ rb k) →
    ∀ (τ : simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ) (P : Finset (characterLattice 𝓕.T))
      (ε : Fin r → Bool)
      (m : ({β : simpleRelativeRoots 𝓕.i 𝓕.ν // ¬ β.val ∈ (𝓕.finsetIndex P).1} ⊕ Fin r) → ℕ)
      (R : ℝ), 0 ≤ R → ∀ (L : Subgroup (FiniteAdelicGroupPoints F G)),
        IsOpen (L : Set (FiniteAdelicGroupPoints F G)) →
      ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
        (smooth : E →L[ℂ] UniformGrowthFrechetSpace F G rho hG hcalc hN hrho R L),
      ∃ T : E →L[ℂ] Lp ℂ 2 ((𝓕.siegelHaar hK e ra τ rb).restrict
          (orthantBox (chamberCoords hK e) τ
            (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P).1) ε m)),
        IsCompactOperator T ∧ ∀ q, T q =ᵐ[(𝓕.siegelHaar hK e ra τ rb).restrict
          (orthantBox (chamberCoords hK e) τ
            (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P).1) ε m)]
          𝓕.hcComponent P (UniformGrowthFrechetSpace.toFun F G rho hG hcalc hN hrho R L
            (smooth q)) := by
  obtain ⟨c, hc, hBC⟩ := adelicHarishChandraBoundaryCompact.{u, v} 𝓕 j hG rho hcalc hN hrho dT e
    step hRed hsetup hd hstep hRoot hCen K hK
  refine ⟨c, hc, fun ra rb hra hrb τ P ε m R hR L hL E _ _ _ smooth => ?_⟩
  let : MeasurableSpace (RealCharacterDual F (Standard.parabolicScheme 𝓕.i 𝓕.ν ∅)) := borel _
  have : BorelSpace (RealCharacterDual F (Standard.parabolicScheme 𝓕.i 𝓕.ν ∅)) := ⟨rfl⟩
  set J : simpleRelativeRoots 𝓕.i 𝓕.ν → Prop := fun β => β.val ∈ (𝓕.finsetIndex P).1 with hJ
  set box := orthantBox (id : (simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ) × (Fin r → ℝ) → _) τ J ε m
    with hbox
  set ell := localFinitenessLogWeight ra rb ∘ e with hell
  have hellc : Continuous ell := (continuous_localFinitenessLogWeight ra rb).comp e.continuous
  have hS₁ : MeasurableSet (e ⁻¹' siegelRegion τ) :=
    e.continuous.measurable (measurableSet_siegelRegion τ)
  have hS₂ : MeasurableSet (e ⁻¹' box) := e.continuous.measurable (measurableSet_orthantBox_id τ J ε m)
  set Sc := boxHeightRegion (⇑e) τ J ε m with hSc
  have hScm : MeasurableSet Sc := hS₁.inter hS₂
  set S := WeightedSiegel.domainHeight F (Standard.parabolicHom 𝓕.i 𝓕.ν ∅) hK ⁻¹' Sc with hSdef
  have hS : MeasurableSet S :=
    (WeightedSiegel.continuous_domainHeight F (Standard.parabolicHom 𝓕.i 𝓕.ν ∅) hK).measurable hScm
  let κ : simpleRelativeRoots 𝓕.i 𝓕.ν → ℝ := fun α =>
    if h : J α then 0 else τ α + m (Sum.inl ⟨α, h⟩)
  let m' : Fin r → ℝ := fun k => m (Sum.inr k) + 1
  have hslab : ∀ z ∈ S,
      let x := e (WeightedSiegel.domainHeight F (Standard.parabolicHom 𝓕.i 𝓕.ν ∅) hK z)
      (∀ α : simpleRelativeRoots 𝓕.i 𝓕.ν, τ α ≤ x.1 α) ∧
        (∀ α : simpleRelativeRoots 𝓕.i 𝓕.ν, α.val ∉ P → x.1 α ≤ κ α) ∧
          (∀ k, |x.2 k| ≤ m' k) := by
    intro z hz
    obtain ⟨hz₁, hz₂⟩ := hz
    set x := e (WeightedSiegel.domainHeight F (Standard.parabolicHom 𝓕.i 𝓕.ν ∅) hK z)
    have hreg : ∀ α, τ α < x.1 α := hz₁
    have hb : ∀ k, 0 < orthantHeight id τ J ε k x ∧ orthantHeight id τ J ε k x ≤ m k := hz₂
    refine ⟨fun α => (hreg α).le, fun α hα => ?_, fun k => ?_⟩
    · have hJα : ¬ J α := fun h => hα h.1
      have := (hb (Sum.inl ⟨α, hJα⟩)).2
      simp only [orthantHeight, Sum.elim_inl, id] at this
      simp only [κ, hJα, dite_false]
      linarith
    · have h := hb (Sum.inr k)
      simp only [orthantHeight, Sum.elim_inr, id, orthantCoord] at h
      have hm0 : (0 : ℝ) ≤ m (Sum.inr k) := Nat.cast_nonneg _
      simp only [m']
      split_ifs at h
      · rw [abs_le]; constructor <;> linarith [h.1, h.2]
      · rw [abs_le]; constructor <;> linarith [h.1, h.2]
  obtain ⟨T₀, -, hT₀, hT₀ae⟩ := hBC ra rb hra hrb P τ κ m' S hS hslab R hR L hL E smooth
  -- the quotient map is measure preserving from the box of the Siegel measure
  have hmeas : (𝓕.siegelHaar hK e ra τ rb).restrict
      (orthantBox (chamberCoords hK e) τ J ε m) =
      WeightedSiegel.frameMeasure hK ell Sc := by
    have h1 : 𝓕.siegelHaar hK e ra τ rb =
        WeightedSiegel.frameMeasure hK ell (e ⁻¹' siegelRegion τ) :=
      (frameMeasure_eq_domainWeightedHaar hK e ra τ rb).symm
    have h2 : orthantBox (chamberCoords hK e) τ J ε m = hK.height ⁻¹' (e ⁻¹' box) := by
      rw [orthantBox_eq_preimage]
      rfl
    rw [h1, h2, WeightedSiegel.frameMeasure_restrict_height hK ell _ _ hS₂]
    rfl
  have hmp : MeasurePreserving
      (LeftCosetSpace.mk (WeightedSiegel.parabolicPrincipalSubgroup F (Standard.parabolicHom 𝓕.i 𝓕.ν ∅)))
      ((𝓕.siegelHaar hK e ra τ rb).restrict (orthantBox (chamberCoords hK e) τ J ε m))
      (WeightedSiegel.domainMeasure F (Standard.parabolicHom 𝓕.i 𝓕.ν ∅) hK ell S) := by
    rw [hmeas]
    exact WeightedSiegel.measurePreserving_mk_frameMeasure hK ell hellc Sc hScm
  refine ⟨(Lp.compMeasurePreservingₗᵢ ℂ _ hmp).toContinuousLinearMap ∘L T₀,
    hT₀.clm_comp (Lp.compMeasurePreservingₗᵢ ℂ _ hmp).toContinuousLinearMap, fun q => ?_⟩
  obtain ⟨hφm, hφinv⟩ := 𝓕.toFun_measurable_invariant hG rho hcalc hN hrho (smooth q)
  have h1 := Lp.coeFn_compMeasurePreserving (T₀ q) hmp
  have h2 := hmp.quasiMeasurePreserving.ae_eq_comp (hT₀ae q)
  refine (h1.trans h2).trans (ae_of_all _ fun g => ?_)
  simp only [Function.comp_apply]
  set Γ := WeightedSiegel.parabolicPrincipalSubgroup F (Standard.parabolicHom 𝓕.i 𝓕.ν ∅)
  have hmem : g * (Quotient.out (LeftCosetSpace.mk Γ g))⁻¹ ∈ Γ :=
    (LeftCosetSpace.mk_eq_mk_iff Γ _ g).mp (Quotient.out_eq _)
  have hl : (g * (Quotient.out (LeftCosetSpace.mk Γ g))⁻¹)⁻¹ ∈
      minimalParabolicImage F G 𝓕.i 𝓕.ν := by
    rw [← WeightedSiegel.parabolicPrincipalSubgroup_eq_minimalParabolicImage F 𝓕.i 𝓕.ν]
    exact Γ.inv_mem hmem
  have heq : Quotient.out (LeftCosetSpace.mk Γ g) =
      (g * (Quotient.out (LeftCosetSpace.mk Γ g))⁻¹)⁻¹ * g := by group
  change 𝓕.hcComponent P _ (Quotient.out (LeftCosetSpace.mk Γ g)) = _
  rw [heq, 𝓕.hcComponent_minimalParabolicImage_mul P hφm hφinv hl]

end Langlands.Global.StandardParabolicFamily
