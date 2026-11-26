import Langlands.Analysis.CosetSpaceShift
import Langlands.Global.AdelicSplitComponentTranslation

/-! # Renormalizing shifts on `P₀(F) U_J(𝔸) \ G(𝔸)`

Let `Λ₀` be the image of `P₀(F)` and `U_J` the unipotent radical of the standard parabolic
`P_J`. On the left coset space of `H_J = Λ₀ ⊔ U_J(𝔸)` in `G(𝔸)`, left translation by a point
`a` that commutes with `L_J(𝔸)` and normalizes `U_J(𝔸)` is well defined. For a weight `W`
invariant under `Λ₀` and `U_J(𝔸)` with `W(g) = κ W(a g)`, the pushforward of the weighted
measure `W · Haar` on the fundamental domain `D₀` of `Λ₀` scales by `κ c(a)` under this
translation, where `c(a)` is the Haar scaling of conjugation by `a` on `U_J(𝔸)`. This is the
renormalizing transformation of Bernstein–Lapid §7.5.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal NNReal

namespace Langlands.Global.StandardConstantTerm

open Langlands.GroupScheme AdelicSubgroupPoints Langlands.Analysis

variable (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local notation "A" => AdelicGroupPoints F G
local notation "Λ₀" => minimalParabolicImage F G i ν
local notation "D₀" => LeftCosetSpace.fundamentalDomain (minimalParabolicImage F G i ν)
  (isDiscrete_minimalParabolicImage F G i ν)

/-- The subgroup `Λ₀ ⊔ U_J(𝔸)` of `G(𝔸)`. -/
def cosetSubgroup (J : Set (characterLattice T)) : Subgroup A :=
  Λ₀ ⊔ adelicPoints F G (standardUnipotent i ν J)

/-- The weighted Haar measure `W · Haar` on the fundamental domain of `Λ₀`. -/
def domainWeightedHaar (W : A → ℝ≥0∞) : Measure A :=
  ((Measure.haar : Measure A).restrict D₀).withDensity W

variable {hG : IsConnectedReductive G} {hi : IsMaximalSplitTorus i} {hν : IsGenericCocharacter i ν}

include hG hi hν in
/-- A point commuting with `L_J(𝔸)` and normalizing `U_J(𝔸)` normalizes `Λ₀ ⊔ U_J(𝔸)`. -/
theorem conj_mem_cosetSubgroup {J : Set (characterLattice T)} (hJ : J ⊆ simpleRelativeRoots i ν)
    (a : A) (hlevi : ∀ x ∈ adelicPoints F G (standardLevi i ν J), a * x = x * a)
    (ha : ∀ w ∈ adelicPoints F G (standardUnipotent i ν J),
      a * w * a⁻¹ ∈ adelicPoints F G (standardUnipotent i ν J))
    {h : A} (hh : h ∈ cosetSubgroup F G i ν J) : a * h * a⁻¹ ∈ cosetSubgroup F G i ν J := by
  have key : ∀ h ∈ (Λ₀ : Set A) ∪ (adelicPoints F G (standardUnipotent i ν J) : Set A),
      a * h * a⁻¹ ∈ cosetSubgroup F G i ν J := by
    rintro l (hl | hw)
    · obtain ⟨x, c, rfl⟩ := exists_leviPart_mul F G i ν (hG := hG) (hi := hi) (hν := hν) hJ hl
      have hx : a * (x : A) = x * a := hlevi _ x.2.2
      have heq : a * ((x : A) * ((c : adelicPoints F G (standardUnipotent i ν J)) : A)) * a⁻¹ =
          (x : A) * (a * ((c : adelicPoints F G (standardUnipotent i ν J)) : A) * a⁻¹) := by
        rw [← mul_assoc, hx]; group
      rw [heq]
      exact (cosetSubgroup F G i ν J).mul_mem (Subgroup.mem_sup_left x.2.1)
        (Subgroup.mem_sup_right (ha _ (c : adelicPoints F G (standardUnipotent i ν J)).2))
    · exact Subgroup.mem_sup_right (ha l hw)
  have hcl : cosetSubgroup F G i ν J =
      Subgroup.closure ((Λ₀ : Set A) ∪ (adelicPoints F G (standardUnipotent i ν J) : Set A)) :=
    Subgroup.sup_eq_closure _ _
  rw [hcl] at hh
  induction hh using Subgroup.closure_induction with
  | mem x hx => exact key x hx
  | one => simp [(cosetSubgroup F G i ν J).one_mem]
  | mul x y _ _ hx hy =>
    have : a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) := by group
    rw [this]
    exact (cosetSubgroup F G i ν J).mul_mem hx hy
  | inv x _ hx =>
    have : a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := by group
    rw [this]
    exact (cosetSubgroup F G i ν J).inv_mem hx

/-- The weighted measure of a set is the integral of the weight over the set in `D₀`. -/
theorem domainWeightedHaar_apply {W : A → ℝ≥0∞} {S : Set A} (hS : MeasurableSet S) :
    domainWeightedHaar F G i ν W S = ∫⁻ g in D₀, S.indicator W g ∂Measure.haar := by
  rw [domainWeightedHaar, withDensity_apply _ hS, lintegral_indicator hS]

include hG hi hν in
/-- Scaling of the weighted measure on `Λ₀ ⊔ U_J(𝔸)`-invariant sets under left translation. -/
theorem domainWeightedHaar_preimage_mul_left {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) (a : A)
    (hlevi : ∀ x ∈ adelicPoints F G (standardLevi i ν J), a * x = x * a)
    (ha : ∀ w ∈ adelicPoints F G (standardUnipotent i ν J),
      a * w * a⁻¹ ∈ adelicPoints F G (standardUnipotent i ν J))
    (ha' : ∀ w ∈ adelicPoints F G (standardUnipotent i ν J),
      a⁻¹ * w * a ∈ adelicPoints F G (standardUnipotent i ν J))
    {W : A → ℝ≥0∞} (hWm : Measurable W) (hWH : ∀ h ∈ cosetSubgroup F G i ν J, ∀ g, W (h * g) = W g)
    (κ : ℝ≥0∞) (hW : ∀ g, W g = κ * W (a * g))
    {B : Set A} (hB : MeasurableSet B) (hBH : CosetSpaceShift.IsInvariantSet (cosetSubgroup F G i ν J) B) :
    haveI hcl := isClosed_adelicPoints_standardUnipotent F G i ν J
    haveI : LocallyCompactSpace (adelicPoints F G (standardUnipotent i ν J)) :=
      hcl.locallyCompactSpace
    domainWeightedHaar F G i ν W ((a * ·) ⁻¹' B) =
      κ * (mulEquivHaarChar (conjPoints F G a ha ha') : ℝ≥0∞) * domainWeightedHaar F G i ν W B := by
  have hB' : MeasurableSet ((a * ·) ⁻¹' B) := (measurable_const_mul a) hB
  rw [domainWeightedHaar_apply F G i ν hB', domainWeightedHaar_apply F G i ν hB]
  let φ : A → ℝ≥0∞ := B.indicator W
  have hφm : Measurable φ := hWm.indicator hB
  have hφH (h : A) (hh : h ∈ cosetSubgroup F G i ν J) (g : A) : φ (h * g) = φ g := by
    simp only [φ]
    by_cases hg : g ∈ B
    · rw [indicator_of_mem hg, indicator_of_mem ((hBH h hh g).mpr hg), hWH h hh g]
    · rw [indicator_of_notMem hg, indicator_of_notMem (fun h' => hg ((hBH h hh g).mp h'))]
  have hpt (g : A) : ((a * ·) ⁻¹' B).indicator W g = κ * φ (a * g) := by
    by_cases hg : a * g ∈ B
    · have hg' : g ∈ (a * ·) ⁻¹' B := hg
      simp only [indicator_of_mem hg', φ, indicator_of_mem hg, hW g]
    · have hg' : g ∉ (a * ·) ⁻¹' B := hg
      simp only [indicator_of_notMem hg', φ, indicator_of_notMem hg, mul_zero]
  simp_rw [hpt]
  have hφa : Measurable fun g => φ (a * g) := hφm.comp (measurable_const_mul a)
  rw [lintegral_const_mul κ hφa, mul_assoc]
  congr 1
  exact setLIntegral_mul_left_eq F G i ν (hG := hG) (hi := hi) (hν := hν) hJ a hlevi ha ha' hφm
    (fun l hl x => hφH l (Subgroup.mem_sup_left hl) x)
    (fun w hw x => hφH w (Subgroup.mem_sup_right hw) x)

include hG hi hν in
/-- The renormalizing shift on `(Λ₀ ⊔ U_J(𝔸)) \ G(𝔸)` given by left translation by `a`, for
the pushforward of `W · Haar|_{D₀}`, with factor `√(κ c(a))`. -/
def standardRenormalizingShift {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) (a : A)
    (hlevi : ∀ x ∈ adelicPoints F G (standardLevi i ν J), a * x = x * a)
    (ha : ∀ w ∈ adelicPoints F G (standardUnipotent i ν J),
      a * w * a⁻¹ ∈ adelicPoints F G (standardUnipotent i ν J))
    (ha' : ∀ w ∈ adelicPoints F G (standardUnipotent i ν J),
      a⁻¹ * w * a ∈ adelicPoints F G (standardUnipotent i ν J))
    {W : A → ℝ≥0∞} (hWm : Measurable W) (hWH : ∀ h ∈ cosetSubgroup F G i ν J, ∀ g, W (h * g) = W g)
    (κ : ℝ≥0) (hκ : 0 < κ) (hW : ∀ g, W g = κ * W (a * g))
    (ht : A → ℝ) (htm : Measurable ht) (htH : ∀ h ∈ cosetSubgroup F G i ν J, ∀ g, ht (h * g) = ht g)
    (hta : ∀ g, ht (a * g) = ht g + 1) :
    L2RenormalizingShift (Measure.map (CosetSpaceShift.mk (cosetSubgroup F G i ν J))
      (domainWeightedHaar F G i ν W)) :=
  haveI hcl := isClosed_adelicPoints_standardUnipotent F G i ν J
  haveI : LocallyCompactSpace (adelicPoints F G (standardUnipotent i ν J)) :=
    hcl.locallyCompactSpace
  CosetSpaceShift.renormalizingShift (cosetSubgroup F G i ν J) (domainWeightedHaar F G i ν W) a
    (fun _ hh => conj_mem_cosetSubgroup F G i ν (hG := hG) (hi := hi) (hν := hν) hJ a hlevi ha hh)
    (NNReal.sqrt (κ * mulEquivHaarChar (conjPoints F G a ha ha')))
    (NNReal.sqrt_pos.mpr (mul_pos hκ (mulEquivHaarChar_pos _)))
    (fun B hB hBH => by
      rw [domainWeightedHaar_preimage_mul_left F G i ν (hG := hG) (hi := hi) (hν := hν) hJ a hlevi
        ha ha' hWm hWH κ hW hB hBH, NNReal.sq_sqrt]
      push_cast
      rfl)
    ht htm htH hta

end Langlands.Global.StandardConstantTerm
