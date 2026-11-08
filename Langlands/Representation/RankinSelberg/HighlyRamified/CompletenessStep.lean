import Langlands.Representation.RankinSelberg.HighlyRamified.TargetPairing
import Langlands.Representation.RankinSelberg.HighlyRamified.DualWeight
import Langlands.Representation.RankinSelberg.HighlyRamified.DualShellIntegral
import Langlands.Representation.RankinSelberg.IntegralDeterminant
import Langlands.Representation.RankinSelberg.HighlyRamified.FourierRow
import Langlands.Representation.RankinSelberg.DeterminantSlices
import Langlands.Representation.Whittaker.CompletenessStatement

/-!
# From shell identities to the averaged function: the completeness step

Let `F_A` be a smooth function on `GL_(m+1)` with `F_A(u g) = ψ_N(u) F_A(g)` whose
restriction to every determinant shell is compactly supported modulo `N`. Suppose that for
every generic `π` (for `ψ⁻¹`) and every model vector `w`, the shell integrals of `F_A` against
the inverse `K⁰(f)`-average `w_avg` are `c ∫ t w` on the shell `ord det = 0` and `0` on the other
shells. The completeness lemma of Jacquet and Shalika (1985), Lemma (3.2)
(`WhittakerCompletenessStatement`), then gives: the weighted `K⁰(f)`-average of `F_A` equals
`c t`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration Matrix Langlands.GeneralLinear
open scoped Pointwise

universe uF uV

section Algebra

variable {F : Type uF} [Field F] [ValuativeRel F] {m : ℕ} {ω : Fˣ →* ℂˣ} {f : ℕ} (hf : 0 < f)

/-- The weight is left invariant under the principal congruence subgroup of level `f`. -/
theorem firstColumnWeight_principal_mul (hω : TrivialOnPrincipalUnits ω f)
    (l g : GeneralLinearGroup (Fin (m + 1)) F)
    (hl : l ∈ Conductor.principalCongruenceSubgroup (ValuativeRel.valuation F).integer m
      (IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f)) :
    firstColumnWeight ω hf (l * g) = firstColumnWeight ω hf g := by
  have hlK : InFirstColumn f l :=
    principalCongruenceSubgroup_le_firstColumnCongruence _ m _ hl
  by_cases h : InFirstColumn f g
  · have hlg : InFirstColumn f (l * g) := mul_mem hlK h
    rw [firstColumnWeight_of_mem ω hf h, firstColumnWeight_of_mem ω hf hlg,
      omega_firstEntry_mul hf hω hlK h hlg]
    have hl1 : ω (firstEntryUnit hf l hlK) = 1 := by
      apply hω
      obtain ⟨hl1, -⟩ := (Conductor.principalCongruenceEntry F _ m _ l).1 hl
      obtain ⟨y, hy, hye⟩ := hl1 0 0
      refine ⟨y, hy, ?_⟩
      simp only [firstEntryUnit_val]
      rw [hye]
      simp
    rw [hl1, Units.val_one, one_mul]
  · have hlg : ¬ InFirstColumn f (l * g) := fun h' => h (by
      simpa using mul_mem (inv_mem hlK) h')
    rw [firstColumnWeight_of_not_mem ω hf h, firstColumnWeight_of_not_mem ω hf hlg]

end Algebra

section Model

variable {G : Type*} [Group G] [TopologicalSpace G] {X : Type*} [AddCommGroup X] [Module ℂ X]
  {N : Subgroup G} {θ : N →* ℂˣ}

/-- A model vector of a smooth representation is right invariant under an open subgroup. -/
theorem model_rightInvariant {π : Representation ℂ G X} (hπ : IsSmooth π)
    (ℓ : functionals N θ π) (w : (coefficientModel π ℓ).toSubmodule) :
    ∃ L : OpenSubgroup G, ∀ g l, l ∈ L → w.val.val (g * l) = w.val.val g := by
  obtain ⟨K, hK⟩ := model_isSmooth π hπ ℓ w
  refine ⟨K, fun g l hl => ?_⟩
  have h := congrArg (fun x : (coefficientModel π ℓ).toSubmodule => x.val.val g)
    ((Representation.mem_invariants _ w).mp hK ⟨l, hl⟩)
  exact h

end Model

section Canonical

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance completenessFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance completenessValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance completenessLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance completenessGroupMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance completenessGroupBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance completenessUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance completenessUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance completenessQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftQuotient (upperUnipotent (r + 1) F.Carrier)) := borel _
local instance completenessQuotientBorel (r : ℕ) : BorelSpace
    (LeftQuotient (upperUnipotent (r + 1) F.Carrier)) := ⟨rfl⟩

variable {m : ℕ}

/-- The standard character is trivial on integral unipotents when `ψ` has conductor `O`. -/
theorem standardCharacter_eq_one_of_integral (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hψ : HasIntegerConductorAt F ψ) (n : upperUnipotent (m + 1) F.Carrier)
    (hn : ∀ i j, n.val i j ∈ (ValuativeRel.valuation F.Carrier).integer) :
    standardCharacter ψ m n = 1 := by
  apply Units.ext
  rw [standardCharacter_apply, Units.val_one, UnitaryAdditiveCharacter.complex_apply,
    hψ.trivial _ (Subring.sum_mem _ fun i _ => hn _ _)]
  simp

/-- `ord det` is unchanged by right multiplication by `GL_(m+1)(O)`. -/
theorem ord_det_mul_integral (g k : Langlands.GeneralLinear (m + 1) F.Carrier)
    (hk : IsIntegralMatrix k) :
    F.canonicalTopologicalData.ord (determinant (g * k) : F.Carrier) =
      F.canonicalTopologicalData.ord (determinant g : F.Carrier) := by
  have hk' : k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer m := by
    rw [Conductor.mem_integralSubgroup]; exact hk
  have hne1 : (determinant g : F.Carrier) ≠ 0 := (determinant g).ne_zero
  have hne2 : (determinant k : F.Carrier) ≠ 0 := (determinant k).ne_zero
  rw [map_mul, Units.val_mul, F.canonicalTopologicalData.ord_mul hne1 hne2]
  have h0 : F.canonicalTopologicalData.ord (determinant k : F.Carrier) = 0 := by
    have habs := normalizedAbs_det_of_mem_integralSubgroup F.canonicalTopologicalData hk'
    rw [F.canonicalTopologicalData.normalizedAbs_of_ne_zero (by exact hne2)] at habs
    have hq : (1 : ℝ) < F.canonicalTopologicalData.residueCardinality := by
      exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one
    have := zpow_right_injective₀ (zero_lt_one.trans hq) hq.ne'
      (habs.trans (zpow_zero _).symm)
    simpa using this
  rw [h0, add_zero]

variable {ω : F.Carrierˣ →* ℂˣ} {f : ℕ} (hf : 0 < f)

/-- Left equivariance of the weighted right average. -/
theorem rightAverage_firstColumn_unipotent (hω : TrivialOnPrincipalUnits ω f)
    (ψN : upperUnipotent (m + 1) F.Carrier →* ℂˣ)
    (FA : Langlands.GeneralLinear (m + 1) F.Carrier → ℂ)
    (LA : OpenSubgroup (Langlands.GeneralLinear (m + 1) F.Carrier))
    (hFAL : ∀ g l, l ∈ LA → FA (g * l) = FA g)
    (hFAN : ∀ (u : upperUnipotent (m + 1) F.Carrier) g, FA (u.val * g) = (ψN u : ℂ) * FA g)
    (u : upperUnipotent (m + 1) F.Carrier) (g : Langlands.GeneralLinear (m + 1) F.Carrier) :
    rightAverage (generalLinearHaar F.Carrier m) FA LA hFAL (firstColumnWeight ω hf)
        (firstColumnWeight_isLocallyConstant F hf hω)
        (firstColumnWeight_hasCompactSupport F hf) (u.val * g) =
      (ψN u : ℂ) * rightAverage (generalLinearHaar F.Carrier m) FA LA hFAL
        (firstColumnWeight ω hf) (firstColumnWeight_isLocallyConstant F hf hω)
        (firstColumnWeight_hasCompactSupport F hf) g := by
  rw [rightAverage_apply, rightAverage_apply, ← integral_const_mul]
  congr 1
  funext k
  rw [mul_assoc, hFAN]
  ring

/-- Right invariance of the weighted right average under the principal congruence
subgroup of level `f`. -/
theorem rightAverage_firstColumn_principal (hω : TrivialOnPrincipalUnits ω f)
    (FA : Langlands.GeneralLinear (m + 1) F.Carrier → ℂ)
    (LA : OpenSubgroup (Langlands.GeneralLinear (m + 1) F.Carrier))
    (hFAL : ∀ g l, l ∈ LA → FA (g * l) = FA g)
    (g l : Langlands.GeneralLinear (m + 1) F.Carrier)
    (hl : l ∈ Conductor.principalLevelOpenSubgroup F.Carrier m f) :
    rightAverage (generalLinearHaar F.Carrier m) FA LA hFAL (firstColumnWeight ω hf)
        (firstColumnWeight_isLocallyConstant F hf hω)
        (firstColumnWeight_hasCompactSupport F hf) (g * l) =
      rightAverage (generalLinearHaar F.Carrier m) FA LA hFAL (firstColumnWeight ω hf)
        (firstColumnWeight_isLocallyConstant F hf hω)
        (firstColumnWeight_hasCompactSupport F hf) g := by
  rw [rightAverage_apply, rightAverage_apply,
    ← integral_mul_left_eq_self (fun k => firstColumnWeight ω hf k * FA (g * l * k)) l⁻¹]
  congr 1
  funext k
  have hl' : l⁻¹ ∈ Conductor.principalLevelOpenSubgroup F.Carrier m f := inv_mem hl
  rw [firstColumnWeight_principal_mul hf hω l⁻¹ k hl']
  congr 2
  group

/-- A nonzero weighted average forces a nonzero value of `F_A` on `g K⁰(f)`. -/
theorem rightAverage_firstColumn_support (hω : TrivialOnPrincipalUnits ω f)
    (FA : Langlands.GeneralLinear (m + 1) F.Carrier → ℂ)
    (LA : OpenSubgroup (Langlands.GeneralLinear (m + 1) F.Carrier))
    (hFAL : ∀ g l, l ∈ LA → FA (g * l) = FA g)
    (g : Langlands.GeneralLinear (m + 1) F.Carrier)
    (hg : rightAverage (generalLinearHaar F.Carrier m) FA LA hFAL (firstColumnWeight ω hf)
        (firstColumnWeight_isLocallyConstant F hf hω)
        (firstColumnWeight_hasCompactSupport F hf) g ≠ 0) :
    ∃ k, InFirstColumn f k ∧ FA (g * k) ≠ 0 := by
  by_contra h
  push Not at h
  apply hg
  rw [rightAverage_apply]
  have hz : (fun k => firstColumnWeight ω hf k * FA (g * k)) = fun _ => (0 : ℂ) := by
    funext k
    by_cases hk : InFirstColumn f k
    · rw [h k hk, mul_zero]
    · rw [firstColumnWeight_of_not_mem ω hf hk, zero_mul]
  rw [hz, integral_zero]

/-- The shell restriction `F_A · 1_(ord det = j)`. -/
def shellRestriction (FA : Langlands.GeneralLinear (m + 1) F.Carrier → ℂ) (j : ℤ)
    (g : Langlands.GeneralLinear (m + 1) F.Carrier) : ℂ :=
  if F.canonicalTopologicalData.ord (determinant g : F.Carrier) = j then FA g else 0

theorem shellRestriction_mul_integral (FA : Langlands.GeneralLinear (m + 1) F.Carrier → ℂ)
    (LA : OpenSubgroup (Langlands.GeneralLinear (m + 1) F.Carrier))
    (hFAL : ∀ g l, l ∈ LA → FA (g * l) = FA g) (j : ℤ) :
    ∀ g l, l ∈ LA ⊓ Conductor.levelOpenSubgroup F.Carrier m 0 →
      shellRestriction F FA j (g * l) = shellRestriction F FA j g := by
  intro g l hl
  unfold shellRestriction
  rw [ord_det_mul_integral F g l ((isIntegralMatrix_iff_mem_level F l).2 hl.2), hFAL g l hl.1]

theorem shellRestriction_unipotent (ψN : upperUnipotent (m + 1) F.Carrier →* ℂˣ)
    (FA : Langlands.GeneralLinear (m + 1) F.Carrier → ℂ)
    (hFAN : ∀ (u : upperUnipotent (m + 1) F.Carrier) g, FA (u.val * g) = (ψN u : ℂ) * FA g)
    (j : ℤ) (u : upperUnipotent (m + 1) F.Carrier) (g : Langlands.GeneralLinear (m + 1) F.Carrier) :
    shellRestriction F FA j (u.val * g) = (ψN u : ℂ) * shellRestriction F FA j g := by
  unfold shellRestriction
  rw [determinant_unipotent_mul, hFAN]
  split_ifs <;> simp

/-- The weighted average commutes with restriction to a determinant shell. -/
theorem rightAverage_shellRestriction (hω : TrivialOnPrincipalUnits ω f)
    (FA : Langlands.GeneralLinear (m + 1) F.Carrier → ℂ)
    (LA : OpenSubgroup (Langlands.GeneralLinear (m + 1) F.Carrier))
    (hFAL : ∀ g l, l ∈ LA → FA (g * l) = FA g) (j : ℤ)
    (g : Langlands.GeneralLinear (m + 1) F.Carrier) :
    rightAverage (generalLinearHaar F.Carrier m) (shellRestriction F FA j)
        (LA ⊓ Conductor.levelOpenSubgroup F.Carrier m 0)
        (shellRestriction_mul_integral F FA LA hFAL j) (firstColumnWeight ω hf)
        (firstColumnWeight_isLocallyConstant F hf hω)
        (firstColumnWeight_hasCompactSupport F hf) g =
      if F.canonicalTopologicalData.ord (determinant g : F.Carrier) = j then
        rightAverage (generalLinearHaar F.Carrier m) FA LA hFAL (firstColumnWeight ω hf)
          (firstColumnWeight_isLocallyConstant F hf hω)
          (firstColumnWeight_hasCompactSupport F hf) g
      else 0 := by
  rw [rightAverage_apply]
  split_ifs with hj
  · rw [rightAverage_apply]
    congr 1
    funext k
    by_cases hk : InFirstColumn f k
    · unfold shellRestriction
      rw [ord_det_mul_integral F g k (inFirstColumn_iff k |>.1 hk).1]
      simp only [hj, ↓reduceIte]
    · rw [firstColumnWeight_of_not_mem ω hf hk, zero_mul, zero_mul]
  · have hz : (fun k => firstColumnWeight ω hf k * shellRestriction F FA j (g * k)) =
        fun _ => (0 : ℂ) := by
      funext k
      by_cases hk : InFirstColumn f k
      · unfold shellRestriction
        rw [ord_det_mul_integral F g k (inFirstColumn_iff k |>.1 hk).1]
        simp only [hj, ↓reduceIte, mul_zero]
      · rw [firstColumnWeight_of_not_mem ω hf hk, zero_mul]
    rw [hz, integral_zero]

/-- Support of the shell average: a nonzero value at `g` forces `u g ∈ C K⁰(f)` for some
`u ∈ N`, where `C` contains the support of `F_A` on the shell modulo `N`. -/
theorem rightAverage_shell_support (hω : TrivialOnPrincipalUnits ω f)
    (FA : Langlands.GeneralLinear (m + 1) F.Carrier → ℂ)
    (LA : OpenSubgroup (Langlands.GeneralLinear (m + 1) F.Carrier))
    (hFAL : ∀ g l, l ∈ LA → FA (g * l) = FA g) (j : ℤ)
    (C : Set (Langlands.GeneralLinear (m + 1) F.Carrier))
    (hC : ∀ g, F.canonicalTopologicalData.ord (determinant g : F.Carrier) = j → FA g ≠ 0 →
      ∃ u : upperUnipotent (m + 1) F.Carrier, u.val * g ∈ C)
    (g : Langlands.GeneralLinear (m + 1) F.Carrier)
    (hg : rightAverage (generalLinearHaar F.Carrier m) (shellRestriction F FA j)
        (LA ⊓ Conductor.levelOpenSubgroup F.Carrier m 0)
        (shellRestriction_mul_integral F FA LA hFAL j) (firstColumnWeight ω hf)
        (firstColumnWeight_isLocallyConstant F hf hω)
        (firstColumnWeight_hasCompactSupport F hf) g ≠ 0) :
    ∃ u : upperUnipotent (m + 1) F.Carrier,
      u.val * g ∈ C * (firstColumnOpenSubgroup F.Carrier m f :
        Set (Langlands.GeneralLinear (m + 1) F.Carrier)) := by
  obtain ⟨k, hk, hne⟩ := rightAverage_firstColumn_support F hf hω _ _ _ g hg
  unfold shellRestriction at hne
  split_ifs at hne with hj
  · obtain ⟨u, hu⟩ := hC _ hj hne
    refine ⟨u, u.val * (g * k), hu, k⁻¹, inv_mem hk, ?_⟩
    group
  · exact absurd rfl hne

/-- The completeness step: shell identities against all generic representations force the
weighted `K⁰(f)`-average of `F_A` to be `c` times the target. -/
theorem rightAverage_eq_target_of_shells (hT1 : WhittakerCompletenessStatement.{uF, uV})
    (ψ : UnitaryAdditiveCharacter F.Carrier) (hψ : HasIntegerConductorAt F ψ)
    (hω : TrivialOnPrincipalUnits ω f)
    (FA : Langlands.GeneralLinear (m + 1) F.Carrier → ℂ)
    (LA : OpenSubgroup (Langlands.GeneralLinear (m + 1) F.Carrier))
    (hFAL : ∀ g l, l ∈ LA → FA (g * l) = FA g)
    (hFAN : ∀ (u : upperUnipotent (m + 1) F.Carrier) g,
      FA (u.val * g) = (standardCharacter ψ m u : ℂ) * FA g)
    (hFAsupp : ∀ j : ℤ, ∃ C : Set (Langlands.GeneralLinear (m + 1) F.Carrier), IsCompact C ∧
      ∀ g, F.canonicalTopologicalData.ord (determinant g : F.Carrier) = j → FA g ≠ 0 →
        ∃ u : upperUnipotent (m + 1) F.Carrier, u.val * g ∈ C)
    (c : ℂ)
    (hshell : ∀ (X : Type uV) [AddCommGroup X] [Module ℂ X]
      (π : Representation ℂ (Langlands.GeneralLinear (m + 1) F.Carrier) X),
      IsGeneric (ψ.scale (-1)) m π → ∀ (ℓ : glFunctionals (ψ.scale (-1)) m π)
      (w : (coefficientModel π ℓ).toSubmodule)
      (Lw : OpenSubgroup (Langlands.GeneralLinear (m + 1) F.Carrier))
      (hwL : ∀ g l, l ∈ Lw → w.val.val (g * l) = w.val.val g) (j : ℤ),
      ∫ q, shellRestriction F FA j q.out *
          inverseAverage (generalLinearHaar F.Carrier m) w.val.val Lw hwL
            (firstColumnWeight ω hf) (firstColumnWeight_isLocallyConstant F hf hω)
            (firstColumnWeight_hasCompactSupport F hf) q.out ∂unipotentQuotientHaar F.Carrier m =
        (if j = 0 then c else 0) *
          ∫ q, firstColumnTarget ω hf (standardCharacter ψ m) q.out * w.val.val q.out
            ∂unipotentQuotientHaar F.Carrier m)
    (g : Langlands.GeneralLinear (m + 1) F.Carrier) :
    rightAverage (generalLinearHaar F.Carrier m) FA LA hFAL (firstColumnWeight ω hf)
        (firstColumnWeight_isLocallyConstant F hf hω)
        (firstColumnWeight_hasCompactSupport F hf) g =
      c * firstColumnTarget ω hf (standardCharacter ψ m) g := by
  classical
  set ψN := standardCharacter ψ m with hψNdef
  have hψN : ∀ n : upperUnipotent (m + 1) F.Carrier,
      (∀ i j, n.val i j ∈ (ValuativeRel.valuation F.Carrier).integer) → ψN n = 1 :=
    fun n hn => standardCharacter_eq_one_of_integral F ψ hψ n hn
  have hcompat := unipotentQuotientHaar_isCompatible F.Carrier m
  set K0 : Set (Langlands.GeneralLinear (m + 1) F.Carrier) :=
    (firstColumnOpenSubgroup F.Carrier m f : Set (Langlands.GeneralLinear (m + 1) F.Carrier))
    with hK0
  have hK0c : IsCompact K0 := isCompact_firstColumnOpenSubgroup F.Carrier m f
  have htL : ∀ g l, l ∈ Conductor.principalLevelOpenSubgroup F.Carrier m f →
      firstColumnTarget ω hf ψN (g * l) = firstColumnTarget ω hf ψN g :=
    fun g l hl => firstColumnTarget_mul_principal hf hω ψN hψN g l hl
  have htN : ∀ (u : upperUnipotent (m + 1) F.Carrier) g,
      firstColumnTarget ω hf ψN (u.val * g) = (ψN u : ℂ) * firstColumnTarget ω hf ψN g :=
    fun u g => firstColumnTarget_unipotent_mul hf hω ψN hψN u g
  -- the key claim on every shell
  have hkey : ∀ (j : ℤ) (g' : Langlands.GeneralLinear (m + 1) F.Carrier),
      rightAverage (generalLinearHaar F.Carrier m) (shellRestriction F FA j)
          (LA ⊓ Conductor.levelOpenSubgroup F.Carrier m 0)
          (shellRestriction_mul_integral F FA LA hFAL j) (firstColumnWeight ω hf)
          (firstColumnWeight_isLocallyConstant F hf hω)
          (firstColumnWeight_hasCompactSupport F hf) g' =
        (if j = 0 then c else 0) * firstColumnTarget ω hf ψN g' := by
    intro j g'
    obtain ⟨C, hC, hCsupp⟩ := hFAsupp j
    set A := rightAverage (generalLinearHaar F.Carrier m) (shellRestriction F FA j)
      (LA ⊓ Conductor.levelOpenSubgroup F.Carrier m 0)
      (shellRestriction_mul_integral F FA LA hFAL j) (firstColumnWeight ω hf)
      (firstColumnWeight_isLocallyConstant F hf hω)
      (firstColumnWeight_hasCompactSupport F hf) with hA
    have hAN : ∀ (u : upperUnipotent (m + 1) F.Carrier) g, A (u.val * g) = (ψN u : ℂ) * A g :=
      rightAverage_firstColumn_unipotent F hf hω ψN _ _ _
        (shellRestriction_unipotent F ψN FA hFAN j)
    have hAL : ∀ g l, l ∈ Conductor.principalLevelOpenSubgroup F.Carrier m f → A (g * l) = A g :=
      rightAverage_firstColumn_principal F hf hω _ _ _
    have hAsupp : ∀ g, A g ≠ 0 → ∃ u : upperUnipotent (m + 1) F.Carrier, u.val * g ∈ C * K0 :=
      rightAverage_shell_support F hf hω FA LA hFAL j C hCsupp
    set cj : ℂ := if j = 0 then c else 0 with hcj
    let Hf : Langlands.GeneralLinear (m + 1) F.Carrier → ℂ :=
      fun g => A g - cj * firstColumnTarget ω hf ψN g
    have hHmem : Hf ∈ InverseWhittakerFunctions (ψ.scale (-1)) m := by
      intro u g
      change Hf (u.val * g) = (inverseStandardCharacter (ψ.scale (-1)) m u : ℂ) * Hf g
      rw [inverseStandardCharacter_scale_neg_one]
      simp only [Hf]
      rw [hAN, htN]
      ring
    let H : InverseWhittakerFunctions (ψ.scale (-1)) m := ⟨Hf, hHmem⟩
    have hwN : ∀ {X : Type uV} [AddCommGroup X] [Module ℂ X]
        {π : Representation ℂ (Langlands.GeneralLinear (m + 1) F.Carrier) X}
        {ℓ : glFunctionals (ψ.scale (-1)) m π} (w : (coefficientModel π ℓ).toSubmodule)
        (u : upperUnipotent (m + 1) F.Carrier) g,
        w.val.val (u.val * g) = ((ψN u : ℂ))⁻¹ * w.val.val g := by
      intro X _ _ π ℓ w u g
      rw [w.val.property u g]
      congr 1
      rw [standardCharacter_scale_neg_one, inverseStandardCharacter_apply, hψNdef,
        standardCharacter_apply]
    have hzero := hT1 p F (ψ.scale (-1)) m H
      ⟨Conductor.principalLevelOpenSubgroup F.Carrier m f, fun g l hl => by
        change A (g * l) - cj * firstColumnTarget ω hf ψN (g * l) =
          A g - cj * firstColumnTarget ω hf ψN g
        rw [hAL g l hl, htL g l hl]⟩
      ⟨C * K0 ∪ K0, (hC.mul hK0c).union hK0c, fun g hg => by
        by_cases hAg : A g = 0
        · have ht : firstColumnTarget ω hf ψN g ≠ 0 := by
            intro ht
            apply hg
            change A g - cj * firstColumnTarget ω hf ψN g = 0
            rw [hAg, ht, mul_zero, sub_zero]
          obtain ⟨u, hu⟩ := firstColumnTarget_support hf ψN ht
          exact ⟨u⁻¹, u.val * g, Or.inr hu, by simp⟩
        · obtain ⟨u, hu⟩ := hAsupp g hAg
          exact ⟨u⁻¹, u.val * g, Or.inl hu, by simp⟩⟩
      (fun X _ _ π hπ ℓ w => by
        obtain ⟨Lw, hwL⟩ := model_rightInvariant hπ.2.1.1 ℓ w
        have hrep : (fun x => whittakerProductIntegrand (ψ.scale (-1)) w.val H x) =
            fun q : LeftUnipotentQuotient m F.Carrier =>
              w.val.val q.out * (A q.out - cj * firstColumnTarget ω hf ψN q.out) := by
          funext q
          conv_lhs => rw [← Quotient.out_eq q]
          rfl
        rw [hrep]
        have hint1 : Integrable (fun q : LeftQuotient (upperUnipotent (m + 1) F.Carrier) =>
            w.val.val q.out * A q.out) (unipotentQuotientHaar F.Carrier m) :=
          integrable_out_of_compact_support F (fun g => w.val.val g * A g)
            (Lw ⊓ Conductor.principalLevelOpenSubgroup F.Carrier m f)
            (fun g l hl => by rw [hwL g l hl.1, hAL g l hl.2])
            (fun u g => by rw [hwN w, hAN]; field_simp) (C * K0) (hC.mul hK0c)
            (fun g hg => hAsupp g (right_ne_zero_of_mul hg))
        have hint2 : Integrable (fun q : LeftQuotient (upperUnipotent (m + 1) F.Carrier) =>
            w.val.val q.out * firstColumnTarget ω hf ψN q.out)
            (unipotentQuotientHaar F.Carrier m) :=
          integrable_out_of_compact_support F (fun g => w.val.val g * firstColumnTarget ω hf ψN g)
            (Lw ⊓ Conductor.principalLevelOpenSubgroup F.Carrier m f)
            (fun g l hl => by rw [hwL g l hl.1, htL g l hl.2])
            (fun u g => by rw [hwN w, htN]; field_simp) K0 hK0c
            (fun g hg => firstColumnTarget_support hf ψN (right_ne_zero_of_mul hg))
        have hsplit : (fun q : LeftUnipotentQuotient m F.Carrier =>
            w.val.val q.out * (A q.out - cj * firstColumnTarget ω hf ψN q.out)) =
            fun q => w.val.val q.out * A q.out -
              cj * (w.val.val q.out * firstColumnTarget ω hf ψN q.out) := by
          funext q; ring
        rw [hsplit, integral_sub hint1 (hint2.const_mul cj), integral_const_mul]
        have hpair := integral_rightAverage_pair (unipotentQuotientHaar F.Carrier m)
          hcompat.right_invariant (generalLinearHaar F.Carrier m) (shellRestriction F FA j)
          w.val.val (LA ⊓ Conductor.levelOpenSubgroup F.Carrier m 0) Lw
          (shellRestriction_mul_integral F FA LA hFAL j) hwL (firstColumnWeight ω hf)
          (firstColumnWeight_isLocallyConstant F hf hω)
          (firstColumnWeight_hasCompactSupport F hf)
          (fun h g k => by
            rw [mul_assoc, shellRestriction_unipotent F ψN FA hFAN, hwN w]
            field_simp)
          (fun k => by
            refine integrable_out_of_compact_support F
              (fun g => shellRestriction F FA j g * w.val.val (g * k⁻¹))
              ((LA ⊓ Conductor.levelOpenSubgroup F.Carrier m 0) ⊓
                Lw.comap (MulAut.conj k).toMonoidHom
                  ((continuous_const.mul continuous_id).mul continuous_const)) ?_ ?_ C hC ?_
            · intro g l hl
              have hl2 : k * l * k⁻¹ ∈ Lw := hl.2
              rw [shellRestriction_mul_integral F FA LA hFAL j g l hl.1]
              congr 1
              rw [show g * l * k⁻¹ = g * k⁻¹ * (k * l * k⁻¹) by group, hwL _ _ hl2]
            · intro u g
              rw [shellRestriction_unipotent F ψN FA hFAN,
                show u.val * g * k⁻¹ = u.val * (g * k⁻¹) from mul_assoc _ _ _, hwN w]
              field_simp
            · intro g hg
              have h1 := left_ne_zero_of_mul hg
              unfold shellRestriction at h1
              split_ifs at h1 with hj
              · exact hCsupp g hj h1
              · exact absurd rfl h1)
        rw [hpair, hshell X π hπ ℓ w Lw hwL j, ← hcj]
        have hcomm : ∫ q, firstColumnTarget ω hf ψN q.out * w.val.val q.out
            ∂unipotentQuotientHaar F.Carrier m =
            ∫ q, w.val.val q.out * firstColumnTarget ω hf ψN q.out
              ∂unipotentQuotientHaar F.Carrier m := by
          congr 1; funext q; ring
        rw [hcomm, sub_self])
      g'
    change A g' - cj * firstColumnTarget ω hf ψN g' = 0 at hzero
    exact sub_eq_zero.mp hzero
  -- read off the value at `g`
  set j := F.canonicalTopologicalData.ord (determinant g : F.Carrier) with hj
  have h := hkey j g
  rw [rightAverage_shellRestriction F hf hω FA LA hFAL j g] at h
  rw [ite_eq_left_of_eq_true _ _ (eq_true hj.symm)] at h
  rw [h]
  by_cases h0 : j = 0
  · simp only [h0, ↓reduceIte]
  · simp only [h0, ↓reduceIte, zero_mul]
    have ht : firstColumnTarget ω hf ψN g = 0 := by
      by_contra ht
      obtain ⟨u, hu⟩ := firstColumnTarget_support hf ψN ht
      apply h0
      have h1 := ord_det_mul_integral F 1 (u.val * g) ((inFirstColumn_iff _).1 hu).1
      rw [one_mul, determinant_unipotent_mul] at h1
      rw [hj, h1]
      simp [F.canonicalTopologicalData.ord_one]
    rw [ht, mul_zero]

end Canonical

end Langlands.RankinSelberg.HighlyRamified
