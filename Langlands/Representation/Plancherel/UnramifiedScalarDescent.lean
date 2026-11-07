import Langlands.Representation.Plancherel.UnramifiedScalarTranslation
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Invariant rational scalars on finite unramified character quotients -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u uG uI

section Generic

variable {H : Type uG} [Group H] [TopologicalSpace H]
  {I : Type uI} (ν : I → (H →* ℝ≥0ˣ))
  (S : Subgroup (unramifiedCharacters ν)) [Fintype S]

/-- The product of all translates of one regular denominator by a finite
character subgroup. -/
def unramifiedRegularNorm (b : unramifiedRegularFunctions ν) :
    unramifiedRegularFunctions ν :=
  ∏ τ : S, unramifiedRegularTranslation ν τ.val b

/-- Remove the identity factor from the denominator norm. -/
def unramifiedRegularNormCofactor (b : unramifiedRegularFunctions ν) :
    unramifiedRegularFunctions ν := by
  classical
  exact ∏ τ ∈ (Finset.univ : Finset S).erase 1,
    unramifiedRegularTranslation ν τ.val b

theorem unramifiedRegularNorm_eq_mul (b : unramifiedRegularFunctions ν) :
    unramifiedRegularNorm ν S b = b * unramifiedRegularNormCofactor ν S b := by
  classical
  simpa [unramifiedRegularNorm, unramifiedRegularNormCofactor] using
    (Finset.mul_prod_erase (Finset.univ : Finset S)
      (fun τ => unramifiedRegularTranslation ν τ.val b) (Finset.mem_univ (1 : S))).symm

/-- Translation by a subgroup element permutes every factor of the norm. -/
theorem unramifiedRegularNorm_invariant (b : unramifiedRegularFunctions ν) (σ : S) :
    unramifiedRegularTranslation ν σ.val (unramifiedRegularNorm ν S b) =
      unramifiedRegularNorm ν S b := by
  classical
  unfold unramifiedRegularNorm
  rw [map_prod]
  calc
    (∏ τ : S, unramifiedRegularTranslation ν σ.val
        (unramifiedRegularTranslation ν τ.val b)) =
      ∏ τ : S, unramifiedRegularTranslation ν (τ * σ).val b := by
        apply Finset.prod_congr rfl
        intro τ _
        rw [Subgroup.coe_mul, unramifiedRegularTranslation_mul]
        rfl
    _ = ∏ τ : S, unramifiedRegularTranslation ν τ.val b :=
      Equiv.prod_comp (Equiv.mulRight σ)
        (fun τ : S => unramifiedRegularTranslation ν τ.val b)

end Generic

section QuotientValues

variable {H : Type uG} [Group H] [TopologicalSpace H]
  {I : Type uI} (ν : I → (H →* ℝ≥0ˣ))
  (S : Subgroup (unramifiedCharacters ν))

/-- An invariant regular function descends as a function to the actual
character quotient; no rational function is evaluated here. -/
def unramifiedInvariantRegularDescend (b : unramifiedRegularFunctions ν)
    (hb : ∀ τ : S, unramifiedRegularTranslation ν τ.val b = b) :
    (unramifiedCharacters ν ⧸ S) → ℂ :=
  Quotient.lift b.val (by
    intro χ ψ h
    have he := congrArg (fun c : unramifiedRegularFunctions ν => c.val χ)
      (hb ⟨χ⁻¹ * ψ, QuotientGroup.leftRel_apply.mp h⟩)
    change b.val ((χ⁻¹ * ψ) * χ) = b.val χ at he
    rw [mul_assoc, mul_comm ψ χ, ← mul_assoc, inv_mul_cancel, one_mul] at he
    exact he.symm)

@[simp]
theorem unramifiedInvariantRegularDescend_mk (b : unramifiedRegularFunctions ν)
    (hb : ∀ τ : S, unramifiedRegularTranslation ν τ.val b = b)
    (χ : unramifiedCharacters ν) :
    unramifiedInvariantRegularDescend ν S b hb (QuotientGroup.mk χ) = b.val χ := rfl

theorem continuous_unramifiedInvariantRegularDescend (b : unramifiedRegularFunctions ν)
    (hb : ∀ τ : S, unramifiedRegularTranslation ν τ.val b = b) :
    Continuous (unramifiedInvariantRegularDescend ν S b hb) :=
  (QuotientGroup.isQuotientMap_mk S).continuous_iff.mpr
    (continuous_unramifiedRegularFunction ν b)

end QuotientValues

section ActualCharacters

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints L)]
  (hp : Continuous (rationalValuationImageProjection L))
  (hL : GroupScheme.IsConnectedReductive L)
  (S : Subgroup (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul)))

set_option quotPrecheck false in
local notation "νL" => (fun ψ => (rationalNormCharacters L ψ).toMul)
local notation "R" => unramifiedRegularFunctions νL
local notation "K" => rationalUnramifiedFunctionField L hp hL

/-- A rational scalar with invariant regular numerator and nonzero invariant
regular denominator. It determines values only on the latter's nonzero locus. -/
structure UnramifiedInvariantScalarPresentation (f : K) where
  numerator : R
  denominator : R
  denominator_ne_zero : denominator ≠ 0
  numerator_invariant : ∀ τ : S, unramifiedRegularTranslation νL τ.val numerator = numerator
  denominator_invariant : ∀ τ : S,
    unramifiedRegularTranslation νL τ.val denominator = denominator
  represents : algebraMap R K numerator / algebraMap R K denominator = f

include hp hL

/-- A nonzero denominator stays nonzero after multiplying all its translates. -/
theorem unramifiedRegularNorm_ne_zero [Fintype S] (b : R) (hb : b ≠ 0) :
    unramifiedRegularNorm νL S b ≠ 0 := by
  let := rationalUnramifiedRegularFunctions_isDomain L hp hL
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro τ _ hz
  exact hb ((unramifiedRegularTranslation νL τ.val).injective (by simpa using hz))

/-- Every rational scalar fixed by a finite character subgroup has an
invariant regular presentation. The denominator is a finite norm product. -/
theorem unramifiedInvariantScalarPresentation_exists [Fintype S] (f : K)
    (hf : ∀ τ : S, rationalUnramifiedFunctionFieldTranslation L hp hL τ.val f = f) :
    Nonempty (UnramifiedInvariantScalarPresentation L hp hL S f) := by
  classical
  let := rationalUnramifiedRegularFunctions_isDomain L hp hL
  obtain ⟨a, b, hb, he⟩ := IsFractionRing.div_surjective R f
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  let d := unramifiedRegularNorm νL S b
  let c := unramifiedRegularNormCofactor νL S b
  have hd : d ≠ 0 := unramifiedRegularNorm_ne_zero L hp hL S b hb0
  have hbc : d = b * c := unramifiedRegularNorm_eq_mul νL S b
  have hi := rationalUnramifiedFunctionField_algebraMap_injective L hp hL
  have hbm : algebraMap R K b ≠ 0 := by
    intro h
    exact hb0 (hi (by simpa only [map_zero] using h))
  have hdm : algebraMap R K d ≠ 0 := by
    intro h
    exact hd (hi (by simpa only [map_zero] using h))
  have hmul : algebraMap R K (a * c) = f * algebraMap R K d := by
    rw [← he, hbc, map_mul, map_mul]
    field_simp
  have hn : ∀ τ : S, unramifiedRegularTranslation νL τ.val (a * c) = a * c := by
    intro τ
    apply hi
    let E : K ≃+* K := rationalUnramifiedFunctionFieldTranslation L hp hL τ.val
    have hdE : E (algebraMap R K d) = algebraMap R K d := by
      exact (rationalUnramifiedFunctionFieldTranslation_algebraMap L hp hL τ.val d).trans
        (congrArg (algebraMap R K) (unramifiedRegularNorm_invariant νL S b τ))
    calc
      algebraMap R K (unramifiedRegularTranslation νL τ.val (a * c)) =
          E (algebraMap R K (a * c)) :=
        (rationalUnramifiedFunctionFieldTranslation_algebraMap L hp hL τ.val (a * c)).symm
      _ = E (f * algebraMap R K d) := congrArg E hmul
      _ = E f * E (algebraMap R K d) := map_mul E _ _
      _ = f * algebraMap R K d := congrArg₂ (fun x y : K => x * y) (hf τ) hdE
      _ = algebraMap R K (a * c) := hmul.symm
  exact ⟨⟨a * c, d, hd, hn, unramifiedRegularNorm_invariant νL S b,
    (div_eq_iff hdm).mpr hmul⟩⟩

namespace UnramifiedInvariantScalarPresentation

variable {L hp hL}
variable {S} {f : rationalUnramifiedFunctionField L hp hL}
  (p : UnramifiedInvariantScalarPresentation L hp hL S f)

/-- The quotient locus where the invariant denominator does not vanish. -/
def regularRegion : Set (unramifiedCharacters νL ⧸ S) :=
  {x | unramifiedInvariantRegularDescend νL S p.denominator p.denominator_invariant x ≠ 0}

/-- Values on the quotient are defined only on its regular locus. -/
def value (x : p.regularRegion) : ℂ :=
  unramifiedInvariantRegularDescend νL S p.numerator p.numerator_invariant x.val /
    unramifiedInvariantRegularDescend νL S p.denominator p.denominator_invariant x.val

@[simp]
theorem regularRegion_mk (χ : unramifiedCharacters νL) :
    QuotientGroup.mk χ ∈ p.regularRegion ↔ p.denominator.val χ ≠ 0 := Iff.rfl

@[simp]
theorem value_mk (χ : unramifiedCharacters νL) (hχ : p.denominator.val χ ≠ 0) :
    p.value ⟨QuotientGroup.mk χ, hχ⟩ = p.numerator.val χ / p.denominator.val χ := rfl

theorem regularRegion_isOpen : IsOpen p.regularRegion :=
  (continuous_unramifiedInvariantRegularDescend νL S
    p.denominator p.denominator_invariant).isOpen_support

theorem continuous_value : Continuous p.value :=
  ((continuous_unramifiedInvariantRegularDescend νL S p.numerator
      p.numerator_invariant).comp continuous_subtype_val).div
    ((continuous_unramifiedInvariantRegularDescend νL S p.denominator
      p.denominator_invariant).comp continuous_subtype_val)
    (fun x => x.property)

/-- The pullback of the quotient regular locus is a dense open set of actual
characters. -/
theorem regularRegion_pullback_isOpen :
    IsOpen {χ : unramifiedCharacters νL | QuotientGroup.mk χ ∈ p.regularRegion} :=
  (continuous_unramifiedRegularFunction νL p.denominator).isOpen_support

theorem regularRegion_pullback_dense :
    Dense {χ : unramifiedCharacters νL | QuotientGroup.mk χ ∈ p.regularRegion} :=
  rationalUnramifiedRegular_dense_nonzero L hp hL p.denominator p.denominator_ne_zero

theorem regularRegion_dense : Dense p.regularRegion :=
  QuotientGroup.dense_preimage_mk.mp p.regularRegion_pullback_dense

theorem regularRegion_nonempty : p.regularRegion.Nonempty := by
  obtain ⟨χ, hχ⟩ := p.regularRegion_pullback_dense.nonempty
  exact ⟨QuotientGroup.mk χ, hχ⟩

/-- Equality in the function field gives an equality of regular cross products. -/
theorem cross_mul (q : UnramifiedInvariantScalarPresentation L hp hL S f) :
    p.numerator * q.denominator = q.numerator * p.denominator := by
  have hi := rationalUnramifiedFunctionField_algebraMap_injective L hp hL
  have hp0 : algebraMap R K p.denominator ≠ 0 := by
    intro h
    exact p.denominator_ne_zero (hi (by simpa only [map_zero] using h))
  have hq0 : algebraMap R K q.denominator ≠ 0 := by
    intro h
    exact q.denominator_ne_zero (hi (by simpa only [map_zero] using h))
  apply hi
  simp only [map_mul]
  exact (div_eq_div_iff hp0 hq0).mp (p.represents.trans q.represents.symm)

/-- Quotient values agree wherever both presentations have nonzero
denominators; this statement does not choose values at poles. -/
theorem value_eq (q : UnramifiedInvariantScalarPresentation L hp hL S f)
    (x : unramifiedCharacters νL ⧸ S)
    (hp' : x ∈ p.regularRegion) (hq' : x ∈ q.regularRegion) :
    p.value ⟨x, hp'⟩ = q.value ⟨x, hq'⟩ := by
  obtain ⟨χ, rfl⟩ := QuotientGroup.mk_surjective x
  apply (div_eq_div_iff hp' hq').mpr
  exact congrArg (fun b : R => b.val χ) (p.cross_mul q)

/-- Two presentations have a common dense regular region on the quotient. -/
theorem regularRegion_inter_dense (q : UnramifiedInvariantScalarPresentation L hp hL S f) :
    Dense (p.regularRegion ∩ q.regularRegion) := by
  let := rationalUnramifiedRegularFunctions_isDomain L hp hL
  apply QuotientGroup.dense_preimage_mk.mp
  have hdense := rationalUnramifiedRegular_dense_nonzero L hp hL
    (p.denominator * q.denominator) (mul_ne_zero p.denominator_ne_zero q.denominator_ne_zero)
  change Dense {χ : unramifiedCharacters νL |
    p.denominator.val χ * q.denominator.val χ ≠ 0} at hdense
  change Dense {χ : unramifiedCharacters νL |
    p.denominator.val χ ≠ 0 ∧ q.denominator.val χ ≠ 0}
  simpa only [mul_ne_zero_iff] using hdense

end UnramifiedInvariantScalarPresentation

end ActualCharacters

end Langlands.Plancherel
