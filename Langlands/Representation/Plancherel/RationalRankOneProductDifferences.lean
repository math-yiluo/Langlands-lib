import Langlands.Representation.Plancherel.RationalRankOneDifferenceRegularity

/-! # Pointwise rank-one products and rational multiplicative differences -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel.ValuationKernelCoordinates

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (H : GroupScheme (Spec (CommRingCat.of F))) [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

local instance rankOneProductPointTopology : TopologicalSpace (rationalPoints H) :=
  rationalPointTopology F H.X

set_option hygiene false in
local notation "ν" => (fun ψ => (rationalNormCharacters H ψ).toMul)
set_option hygiene false in
local notation "Z" => unramifiedCharacters ν
set_option hygiene false in
local notation "R" => unramifiedRegularFunctions ν
local notation "hp" => continuous_rationalValuationImageProjection H

/-- Invariance of the factor whenever both points lie in the stated region. -/
def RankOneTranslationChart.InvariantOn (chart : RankOneTranslationChart H)
    (D : Set Z) (factor : Z → ℂ) : Prop :=
  ∀ (c : Fin chart.complementRank → ℂˣ) (z : Z), z ∈ D →
    complementParameter chart.coordinates c * z ∈ D →
    factor (complementParameter chart.coordinates c * z) = factor z

variable (hH : IsConnectedReductive H)

local notation "K" => rationalUnramifiedFunctionField H hp hH
local notation "charts" => List (RankOneTranslationChart H)

/-- The regular values of the fraction agree on a dense open locus with a
constant times a list of functions, each invariant on that locus under the
translations of its corresponding chart. -/
def HasDenseRankOneProduct (ds : charts) (f : K) : Prop :=
  ∃ (a b : R) (κ : ℂˣ) (D : Set Z) (factors : List (Z → ℂ)),
    f = algebraMap R K a / algebraMap R K b ∧ Dense D ∧ IsOpen D ∧
    List.Forall₂ (fun d g => d.InvariantOn H D g) ds factors ∧
    ∀ z ∈ D, a.val z ≠ 0 ∧ b.val z ≠ 0 ∧
      a.val z / b.val z = (κ : ℂ) * (factors.map (fun g => g z)).prod

private theorem list_prod_map_div {T : Type*} (s : List T) (a b : T → ℂ) :
    (s.map (fun i => a i / b i)).prod = (s.map a).prod / (s.map b).prod := by
  induction s with
  | nil => simp
  | cons i s ih => simp only [List.map_cons, List.prod_cons, ih, div_mul_div_comm]

private theorem list_prod_map_inv {T : Type*} (s : List T) (a : T → ℂ) :
    (s.map (fun i => (a i)⁻¹)).prod = (s.map a).prod⁻¹ := by
  induction s with
  | nil => simp
  | cons i s ih => simp [ih, mul_inv_rev, mul_comm]

/-- Inverting the rational fraction inverts the constant and the given
pointwise factors on their original dense open locus. -/
theorem HasDenseRankOneProduct.inv {ds : charts} {f : K} (h : HasDenseRankOneProduct H hH ds f) :
    HasDenseRankOneProduct H hH ds f⁻¹ := by
  obtain ⟨a, b, κ, D, factors, hfrac, hd, hopen, hinv, hvalue⟩ := h
  refine ⟨b, a, κ⁻¹, D, factors.map (fun g z => (g z)⁻¹), ?_, hd, hopen, ?_, ?_⟩
  · rw [hfrac, inv_div]
  · rw [List.forall₂_map_right_iff]
    exact hinv.imp (fun d g hg c z hz hz' => congrArg Inv.inv (hg c z hz hz'))
  · intro z hz
    obtain ⟨ha, hb, hv⟩ := hvalue z hz
    refine ⟨hb, ha, ?_⟩
    rw [← inv_div, hv, mul_inv_rev, mul_comm]
    simp only [Units.val_inv_eq_inv_val, List.map_map, Function.comp_def, list_prod_map_inv]

private theorem regular_fraction_eq_constant (D : Set Z) (hd : Dense D) (a b : R) (κ : ℂ)
    (hb : ∀ z ∈ D, b.val z ≠ 0) (h : ∀ z ∈ D, a.val z / b.val z = κ) :
    algebraMap R K a / algebraMap R K b = algebraMap R K (algebraMap ℂ R κ) := by
  obtain ⟨z, hz⟩ := hd.nonempty
  have hb0 : b ≠ 0 := fun h0 => hb z hz (by rw [h0]; rfl)
  have hab : a = (algebraMap ℂ R κ) * b := by
    apply Subtype.ext
    exact Continuous.ext_on hd (continuous_unramifiedRegularFunction ν a)
      (continuous_unramifiedRegularFunction ν (algebraMap ℂ R κ * b))
      (fun z hz => (div_eq_iff (hb z hz)).mp (h z hz))
  rw [hab, map_mul, mul_div_cancel_right₀]
  exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb0

private theorem differences_of_product
    (ds : charts) (a b : R) (κ : ℂˣ) (D : Set Z) (factors : List (Z → ℂ))
    (hD : Dense D) (hopen : IsOpen D) (hκ : ds = [] → κ = 1)
    (hInv : List.Forall₂ (fun d g => d.InvariantOn H D g) ds factors)
    (hvalue : ∀ z ∈ D, a.val z ≠ 0 ∧ b.val z ≠ 0 ∧
      a.val z / b.val z = (κ : ℂ) * (factors.map fun g => g z).prod) :
    MultiplicativeDifferencesVanish (ds.map (RankOneTranslationChart.translations H))
      (algebraMap R K a / algebraMap R K b) := by
  induction ds generalizing a b κ D factors with
  | nil =>
      cases hInv
      change algebraMap R K a / algebraMap R K b = 1
      rw [regular_fraction_eq_constant H hH D hD a b (κ : ℂ) (fun z hz => (hvalue z hz).2.1)
        (fun z hz => by simpa using (hvalue z hz).2.2), hκ rfl]
      simp only [Units.val_one, map_one]
  | cons chart rest ih =>
      cases hInv with
      | @cons _ head _ tail hhead htail =>
        intro σ hσ
        obtain ⟨c, rfl⟩ := hσ
        let t := complementParameter chart.coordinates c
        let e : Z ≃ₜ Z := Homeomorph.mulLeft t
        let D' := D ∩ e ⁻¹' D
        have hpre : IsOpen (e ⁻¹' D) := hopen.preimage e.continuous
        have hD' : Dense D' := hD.inter_of_isOpen_right
          (e.isOpenQuotientMap.dense_preimage_iff.mpr hD) hpre
        let shifted (g : Z → ℂ) (z : Z) := g (t * z) / g z
        have hshift : List.Forall₂ (fun d g => d.InvariantOn H D' g) rest (tail.map shifted) := by
          rw [List.forall₂_map_right_iff]
          refine htail.imp (fun d g hg s z hz hz' => ?_)
          let u := complementParameter d.coordinates s
          have hcomm : t * (u * z) = u * (t * z) := by ac_rfl
          have hu : u * (t * z) ∈ D := hcomm ▸ hz'.2
          change g (t * (u * z)) / g (u * z) = g (t * z) / g z
          rw [hcomm, hg s (t * z) hz.2 hu, hg s z hz.1 hz'.1]
        rw [fractionMultiplicativeDifference_div]
        refine ih _ _ 1 D' (tail.map shifted) hD' (hopen.inter hpre) (fun _ => rfl) hshift ?_
        intro z hz
        have h₀ := hvalue z hz.1
        have h₁ := hvalue (t * z) hz.2
        change a.val (t * z) * b.val z ≠ 0 ∧ b.val (t * z) * a.val z ≠ 0 ∧
          (a.val (t * z) * b.val z) / (b.val (t * z) * a.val z) =
            (↑(1 : ℂˣ) : ℂ) * ((tail.map shifted).map fun g => g z).prod
        refine ⟨mul_ne_zero h₁.1 h₀.2.1, mul_ne_zero h₁.2.1 h₀.1, ?_⟩
        have hn : head z ≠ 0 := by
          intro he
          have h := div_ne_zero h₀.1 h₀.2.1
          rw [h₀.2.2, List.map_cons, List.prod_cons, he, zero_mul, mul_zero] at h
          exact h rfl
        rw [← div_div_div_eq, h₁.2.2, h₀.2.2, List.map_cons, List.map_cons, List.prod_cons,
          List.prod_cons, hhead c z hz.1 hz.2, ← mul_assoc, ← mul_assoc,
          mul_div_mul_left _ _ (mul_ne_zero κ.ne_zero hn)]
        simp only [Units.val_one, one_mul, List.map_map, Function.comp_def, shifted, list_prod_map_div]

/-- For a nonempty list, the constant factor disappears in the first
multiplicative difference, and each succeeding difference removes its
corresponding factor on an intersection of translated dense open sets. -/
theorem multiplicativeDifferencesVanish_of_denseRankOneProduct
    (ds : charts) (f : K) (hne : ds ≠ []) (hf : HasDenseRankOneProduct H hH ds f) :
    MultiplicativeDifferencesVanish (ds.map (RankOneTranslationChart.translations H)) f := by
  obtain ⟨a, b, κ, D, factors, rfl, hd, hopen, hInv, hvalue⟩ := hf
  exact differences_of_product H hH ds a b κ D factors hd hopen
    (fun h => (hne h).elim) hInv hvalue

/-- The pointwise product criterion and a dense norm bound give regularity
even if the gallery has no nontrivial walls. -/
theorem unitaryRegular_of_denseRankOneProduct
    (ds : charts) (f : K) (hf : f ≠ 0)
    (hprod : HasDenseRankOneProduct H hH ds f) (hbound : HasDenseUnitaryNormBound hH f) :
    RationalFunctionUnitaryRegular H hH f := by
  by_cases hds : ds = []
  · subst ds
    obtain ⟨a, b, κ, D, factors, rfl, hd, _, hInv, hvalue⟩ := hprod
    cases hInv
    rw [regular_fraction_eq_constant H hH D hd a b (κ : ℂ) (fun z hz => (hvalue z hz).2.1)
      (fun z hz => by simpa using (hvalue z hz).2.2)]
    exact rationalFunctionUnitaryRegular_algebraMap H hH _
  · exact unitaryRegular_of_rankOne_differences H hH ds f hf
      (multiplicativeDifferencesVanish_of_denseRankOneProduct H hH ds f hds hprod) hbound

end Langlands.Plancherel.ValuationKernelCoordinates
