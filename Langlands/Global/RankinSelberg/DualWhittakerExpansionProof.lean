import Langlands.Global.RankinSelberg.DualWhittakerExpansionStatement
import Langlands.Global.RankinSelberg.UnfoldingDual
import Langlands.Global.RankinSelberg.WhittakerExpansionCore.ExpansionRealization
import Langlands.Global.RankinSelberg.DualWhittakerCore.DualCuspidal
import Langlands.Global.RankinSelberg.DualWhittakerCore.DualDecay

/-! # Proof of the Whittaker expansion of the dual cusp forms

Proof of `Langlands.Global.RankinSelbergGlobal.DualCuspidalWhittakerExpansionStatement`
(Cogdell 2004, Theorem 1.1, for the dual cusp form `φ̃` and the character `ψ⁻¹`).

For a vector `v` of an actual cuspidal realization with cusp function `φ`, the dual function
`φ̃ = dualFunction φ` is `φ ∘ ι` with `ι(g) = ᵗg⁻¹`. The dual `W̃` of the `ψ`-Whittaker function
of `φ` is the `ψ⁻¹`-Whittaker function of `φ̃` (`dualCuspWhittaker_eq_whittaker`). The functions
`φ ∘ ι` form a Whittaker decay class (`whittakerDecayClass_iotaSpace`), so the Whittaker terms of
`φ̃` have locally uniform summable majorants. `φ̃` is cuspidal (`isCuspidal_transposeDual`), so the
expansion of the general core (`hasSum_whittaker_of_levelPropsB`) applies to `φ̃` and `ψ⁻¹`. The
majorants give absolute convergence, and the Weierstrass M-test (`tendstoUniformlyOn_tsum`)
gives uniform convergence of the partial sums of the absolute values on compact sets. -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Filter
open scoped CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
  AdelicSubgroupPoints Langlands.Automorphic Langlands.Automorphic.ContinuousRationalFunctions

local instance dualExpansionSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance dualExpansionSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

local instance dualExpansionAddCommGroupRationalInvariant (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance dualExpansionAddCommGroupContinuousRational (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance dualExpansionAddCommGroupFiniteSmoothRational (F : Type u) [Field F]
    [NumberField F] (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance dualExpansionAddCommGroupAutomorphicForms (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance dualExpansionAddCommGroupStableAutomorphic (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r)

section DualCuspFunction

/-- Cusp functions are invariant under left translation by the rational points. -/
theorem cuspFunction_rational_point (v : T.Space)
    (c : RationalGroupPoints F (Scheme F (r + 1))) (x : Points F (r + 1)) :
    cuspFunction F T v (AdelicGroupPoints.rational F (Scheme F (r + 1)) c * x) =
      cuspFunction F T v x :=
  cuspFunction_rational_mul F T v ⟨c, rfl⟩ x

/-- The dual cusp function is the cusp function composed with transpose inverse. -/
theorem dualCuspFunction_eq_iota (v : T.Space) (x : Points F (r + 1)) :
    dualFunction F (r + 1) (cuspFunction F T v) x = cuspFunction F T v (iota F (r + 1) x) :=
  UnequalAnalytic.dualFunction_eq F _ (cuspFunction_rational_point F T v) x

/-- The dual cusp function of `v` is the element of `iotaSpace (cuspSpace T)` attached to `v`. -/
theorem coe_iotaSpaceEquiv_cuspEquiv (v : T.Space) :
    ((iotaSpaceEquiv F (cuspSpace F T) (cuspEquiv F T v) : iotaSpace F (cuspSpace F T)) :
      Points F (r + 1) → ℂ) = dualFunction F (r + 1) (cuspFunction F T v) := by
  funext x
  rw [coe_iotaSpaceEquiv, coe_cuspEquiv, dualCuspFunction_eq_iota]

/-- **Majorants for the dual cusp functions.** The Whittaker terms of `φ̃` have locally uniform
summable majorants at every level, for every standard character. -/
theorem hasWhittakerMajorants_dualCuspFunction (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space) :
    HasWhittakerMajorants F r ψ (dualFunction F (r + 1) (cuspFunction F T v)) := by
  rw [← coe_iotaSpaceEquiv_cuspEquiv]
  exact whittakerMajorantsStatement_proof F r _ _
    (whittakerDecayClass_iotaSpace (whittakerDecayClass_cuspSpace F T)) ψ hψ _

/-- **The dual Whittaker function is a Whittaker function of the dual.** The dual of the
`ψ`-Whittaker function of `φ` is the `ψ⁻¹`-Whittaker function of `φ̃`. -/
theorem dualCuspWhittaker_eq_whittaker (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space) (x : Points F (r + 1)) :
    dualFunction F (r + 1) (cuspWhittaker F T ψ v) x =
      whittaker F r ψ⁻¹ (dualFunction F (r + 1) (cuspFunction F T v)) x := by
  have hψ' := isStandardAdditiveCharacter_inv F ψ hψ
  have h1 := dualCuspWhittaker_eq_setIntegral F T ψ⁻¹ hψ' v x
  rw [inv_inv] at h1
  have h2 := subgroupCharacterCoefficient_eq_setIntegral F (Scheme F (r + 1))
    (upperUnipotent F (r + 1)) (genericCharacter F r ψ⁻¹ fun _ => 1)
    (continuous_genericCharacter F r ψ⁻¹ hψ'.1 _).measurable
    (genericCharacter_rational_mul F r ψ⁻¹ hψ') (dualFunction F (r + 1) (cuspFunction F T v))
    (continuous_dualCuspFunction F T v).measurable
    (fun k y => dualCuspFunction_rational_mul F T v (mem_rationalSubgroup_of_unipotent F k) y) x
  rw [h1]
  change _ = subgroupCharacterCoefficient F _ (upperUnipotent F (r + 1))
    (genericCharacter F r ψ⁻¹ fun _ => 1) (dualFunction F (r + 1) (cuspFunction F T v)) x
  rw [h2, Complex.real_smul]
  congr 1
  refine setIntegral_congr_fun (LeftCosetSpace.measurableSet_fundamentalDomain _ _)
    fun m _ => ?_
  have hl : (genericCharacter F r ψ⁻¹ (fun _ => 1) m)⁻¹ = genericCharacter F r ψ (fun _ => 1) m := by
    rw [genericCharacter_inv_eq_inv, inv_inv]
  have hr : starRingEnd ℂ (genericCharacter F r ψ⁻¹ (fun _ => 1) m) =
      genericCharacter F r ψ (fun _ => 1) m := by
    rw [genericCharacter_inv F r ψ hψ.2.2.2, Complex.conj_conj]
  simp only [hl, hr]

/-- The dual cusp function satisfies the level-`r` properties: it is the transpose-inverse dual
of a cuspidal function, which is cuspidal. -/
theorem levelPropsB_dualCuspFunction (v : T.Space) :
    CuspidalWhittaker.LevelPropsB r (fun g => dualFunction F (r + 1) (cuspFunction F T v)
      ((GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm g)) := by
  have h := (CuspidalWhittaker.levelProps_top (transposeDual (T.realization.toContinuous v))
    (isCuspidal_transposeDual (fun a b h ha hb g =>
      T.realization.constantTerm_eq_zero T.cuspidal h ha hb v g))).levelPropsB
  have e : (fun g => dualFunction F (r + 1) (cuspFunction F T v)
      ((GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm g)) =
      evaluate F (r + 1) (transposeDual (T.realization.toContinuous v)) := by
    funext g
    rw [dualCuspFunction_eq_iota, cuspFunction_apply_eq, evaluate_transposeDual]
    congr 1
    change GeneralLinearGroupPoints.adelicEquiv F (r + 1) (iota F (r + 1) _) = _
    rw [UnequalAnalytic.adelicEquiv_iota]
    congr 1
    exact (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).apply_symm_apply g
  rw [e]
  exact h

end DualCuspFunction

section Expansion

/-- **The Whittaker expansion of the dual cusp forms of an actual cuspidal realization.** -/
theorem dualCuspidalWhittakerExpansion : DualCuspidalWhittakerExpansion F T := by
  intro ψ hψ v
  have hψ' := isStandardAdditiveCharacter_inv F ψ hψ
  have hmaj := hasWhittakerMajorants_dualCuspFunction F T ψ⁻¹ hψ' v
  have hsum : ∀ (k : ℕ) (hk : k ≤ r) (x : Points F (r + 1)),
      Summable fun q : UnipotentRationalCosets F k =>
        ‖whittaker F r ψ⁻¹ (dualFunction F (r + 1) (cuspFunction F T v))
          (padRational F (Nat.le_succ_of_le hk) q.out * x)‖ := by
    intro k hk x
    obtain ⟨b, hb, hle⟩ := hmaj k hk {x} isCompact_singleton
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => hle q x rfl) hb
  have hterm : ∀ (q : UnipotentRationalCosets F r) (x : Points F (r + 1)),
      dualFunction F (r + 1) (cuspWhittaker F T ψ v) (cornerAdelicPoint F r q.out * x) =
        whittaker F r ψ⁻¹ (dualFunction F (r + 1) (cuspFunction F T v))
          (padRational F (Nat.le_succ_of_le le_rfl) q.out * x) := by
    intro q x
    rw [dualCuspWhittaker_eq_whittaker F T ψ hψ, ← padRational_eq_cornerAdelicPoint]
  refine ⟨fun g => ⟨?_, ?_⟩, fun C hC => ?_⟩
  · have e : (fun q : UnipotentRationalCosets F r =>
        ‖dualFunction F (r + 1) (cuspWhittaker F T ψ v) (cornerAdelicPoint F r q.out * g)‖) =
        fun q => ‖whittaker F r ψ⁻¹ (dualFunction F (r + 1) (cuspFunction F T v))
          (padRational F (Nat.le_succ_of_le le_rfl) q.out * g)‖ :=
      funext fun q => by rw [hterm]
    rw [e]
    exact hsum r le_rfl g
  · have h := hasSum_whittaker_of_levelPropsB F ψ⁻¹ (dualFunction F (r + 1) (cuspFunction F T v))
      hψ' (continuous_dualCuspFunction F T v)
      (fun k hk x => dualCuspFunction_rational_mul F T v hk x)
      (levelPropsB_dualCuspFunction F T v) hsum g
    have e : (fun q : UnipotentRationalCosets F r =>
        dualFunction F (r + 1) (cuspWhittaker F T ψ v) (cornerAdelicPoint F r q.out * g)) =
        fun q => whittaker F r ψ⁻¹ (dualFunction F (r + 1) (cuspFunction F T v))
          (cornerAdelicPoint F r q.out * g) :=
      funext fun q => dualCuspWhittaker_eq_whittaker F T ψ hψ v _
    rw [e]
    exact h
  · obtain ⟨b, hb, hle⟩ := hmaj r le_rfl C hC
    refine tendstoUniformlyOn_tsum (f := fun (q : UnipotentRationalCosets F r) g =>
      ‖dualFunction F (r + 1) (cuspWhittaker F T ψ v) (cornerAdelicPoint F r q.out * g)‖)
      hb fun q x hx => ?_
    simp only [norm_norm]
    rw [hterm]
    exact hle q x hx

end Expansion

end Langlands.Global.RankinSelbergGlobal.Unfolding

namespace Langlands.Global.RankinSelbergGlobal

/-- **The Whittaker expansion of the dual cusp forms, with locally uniform convergence.** -/
theorem dualCuspidalWhittakerExpansionStatement_proof :
    DualCuspidalWhittakerExpansionStatement.{u} :=
  fun F _ _ _ _ T => Unfolding.dualCuspidalWhittakerExpansion F T

end Langlands.Global.RankinSelbergGlobal
