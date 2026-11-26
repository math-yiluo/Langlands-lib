import Langlands.Global.AdelicLocalFinitenessGroupData
import Langlands.Global.AdelicSiegelNormOne
import Langlands.Global.AdelicSiegelMeasureReduction
import Langlands.Global.PositiveTorusProductLifting
import Langlands.Global.AdelicPositiveDecompositionReduction
import Langlands.Global.AdelicPositiveTorusSplitComponentProof
import Langlands.Global.RelativeRootChamberLog
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof

/-! # Fundamental split rays in the actual positive Siegel torus -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints AdelicSiegelFactors PositiveRealTorus

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)
  {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (j : T₀ ⟶ fam.T)

local notation "Δ" => simpleRelativeRoots fam.i fam.ν
local notation "aG" => positiveMap F G fam.T fam.i T₀ j
local notation "Torus" => PositiveRealTorus.intrinsicSubgroup F T₀

/-- Every intrinsic positive point of the maximal split torus whose ambient value is
norm one comes from the positive part of the derived factor in the Siegel setup. -/
theorem exists_siegelTorus_lift_of_characterLog_eq_zero
    (hsetup : IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j)
    (t : PositiveRealTorus.intrinsicSubgroup F fam.T)
    (ht : characterLog F G (map F fam.T.toGrp G fam.i t.val) = 0) :
    ∃ a : Torus, map F T₀.toGrp fam.T.toGrp (CommGroupScheme.groupHom j) a.val = t.val := by
  have hNorm := hsetup.positiveMap_mem_normOne F G fam.T fam.i fam.ν T₀ j
  obtain ⟨_, _, _, _, _, _, _, ⟨_, _, _, _, hT₀, _⟩, Z, z, hz, hprod⟩ := hsetup
  obtain ⟨a, b, hab⟩ := hasPositiveProductFactorization_of_surjective_product F fam.T T₀ Z j z
    fam.maximalSplit.isSplitSubtorus.1 hT₀.isSplitSubtorus.1 hz.1.1.1 hprod t
  let c := CommGroupScheme.groupHom z ≫ fam.i
  let x := map F Z.toGrp G c b.val
  have hx : aG a * x = map F fam.T.toGrp G fam.i t.val := by
    rw [← hab, map_mul]
    congr 1
  have hOne : x ∈ normOneSubgroup F G := by
    have he : x = (aG a)⁻¹ * (map F fam.T.toGrp G fam.i t.val) := by
      rw [← hx, inv_mul_cancel_left]
    rw [he]
    exact (normOneSubgroup F G).mul_mem
      ((normOneSubgroup F G).inv_mem (hNorm a))
      ((characterLog_eq_zero_iff F G _).mp ht)
  let E := splitComponentNormOneDecomposition centralSplitTorusCharacter F G fam.connectedReductive Z c hz
  have he : E (b, 1) = E (1, ⟨x, hOne⟩) := by
    simp only [E, splitComponentNormOneDecomposition_apply, positivePointMap_apply,
      map_one, OneMemClass.coe_one, mul_one, one_mul]
    rfl
  have hx1 : x = 1 := (congrArg (fun v => (v.2 : AdelicGroupPoints F G)) (E.injective he)).symm
  rw [hx1, mul_one] at hx
  have : IsAffineHom fam.T.X.hom := fam.maximalSplit.isSplitSubtorus.1.isAffineHom
  have : IsAffine fam.T.X.left := isAffine_of_isAffineHom fam.T.X.hom
  refine ⟨a, (isClosedEmbedding_map_of_isClosedSubgroup F fam.i fam.maximalSplit.isSplitSubtorus.2).injective ?_⟩
  exact hx

/-- Fundamental positive rays can be chosen inside the Siegel torus. Each ray has positive
logarithm at its own simple root, zero logarithm at the other simple roots, and lies in the
positive split component of every standard parabolic whose Levi index omits that root. -/
theorem exists_siegelFundamentalRays
    (hsetup : IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j) :
    ∃ r : Δ → Torus,
      (∀ α β : Δ, β ≠ α → characterLog F T₀.toGrp (r α).val (j ≫ β.val) = 0) ∧
      (∀ α : Δ, 0 < characterLog F T₀.toGrp (r α).val (j ≫ α.val)) ∧
      (∀ (α : Δ) (n : ℕ), (r α) ^ n ∈
        weakSimpleRootChamber F T₀ fam.T j G fam.i fam.ν 1) ∧
      ∀ (J : StandardIndex F G fam.i fam.ν) (α : Δ), α.val ∉ J.val →
        ∃ a : fam.positiveSplitComponent J, map F (fam.P J) G (fam.p J) a.val = aG (r α) := by
  obtain ⟨t, ht, hOthers, hSelf, hLog⟩ :=
    exists_fundamentalCoweightPoints fam.connectedReductive fam.maximalSplit fam.generic
  choose r hr using fun α : Δ =>
    fam.exists_siegelTorus_lift_of_characterLog_eq_zero j hsetup ⟨t α, ht α⟩ (hLog α)
  have hL (α : Δ) (χ : characterLattice fam.T) :
      characterLog F T₀.toGrp (r α).val (j ≫ χ) = characterLog F fam.T.toGrp (t α) χ := by
    have he : Lie.characterValue (j ≫ χ) (r α).val = Lie.characterValue χ (t α) :=
      (Lie.characterValue_comp j χ (r α).val).trans (congrArg (fun x => Lie.characterValue χ x) (hr α))
    change Real.log ((IdeleAbsoluteValue.full F (Lie.characterValue (j ≫ χ) (r α).val) : ℝ≥0) : ℝ) =
      Real.log ((IdeleAbsoluteValue.full F (Lie.characterValue χ (t α)) : ℝ≥0) : ℝ)
    rw [he]
  have hOff (α β : Δ) (hβ : β ≠ α) : characterLog F T₀.toGrp (r α).val (j ≫ β.val) = 0 := by
    rw [hL, characterLog_eq_log_characterValue, hOthers α β hβ, map_one,
      Units.val_one, NNReal.coe_one, Real.log_one]
  have hPos (α : Δ) : 0 < characterLog F T₀.toGrp (r α).val (j ≫ α.val) := by
    obtain ⟨x, hx, he⟩ := hSelf α
    rw [hL, characterLog_eq_log_characterValue, ← he, PositiveRealIdeles.absoluteValue_full,
      Units.val_pow_eq_pow_val, NNReal.coe_pow, Real.log_pow]
    exact mul_pos (Nat.cast_pos.mpr Module.finrank_pos) (Real.log_pos (by exact_mod_cast hx))
  refine ⟨r, hOff, hPos, ?_, ?_⟩
  · intro α n
    refine (mem_weakSimpleRootChamber_iff_log F T₀ fam.T j G fam.i fam.ν 1 _).mpr ?_
    intro χ hχ
    let β : Δ := ⟨χ, hχ⟩
    have h0 : 0 ≤ characterLog F T₀.toGrp (r α).val (j ≫ χ) := by
      change 0 ≤ characterLog F T₀.toGrp (r α).val (j ≫ β.val)
      by_cases he : β = α
      · rw [he]
        exact (hPos α).le
      · rw [hOff α β he]
    have hp : 0 ≤ characterLog F T₀.toGrp ((r α) ^ n).val (j ≫ χ) := by
      induction n with
      | zero =>
        rw [pow_zero, OneMemClass.coe_one, characterLog_one]
        exact le_rfl
      | succ n ih =>
        rw [pow_succ, Subgroup.coe_mul, characterLog_mul]
        exact add_nonneg ih h0
    simpa only [Units.val_one, NNReal.coe_one, Real.log_one] using hp
  · intro J α hα
    have hRoot (β : characterLattice fam.T) (hβ : β ∈ J.val) : Lie.characterValue β (t α) = 1 :=
      hOthers α ⟨β, J.property hβ⟩ (fun he => hα (congrArg Subtype.val he ▸ hβ))
    obtain ⟨a, ha, hVal⟩ := positiveTorusSplitComponent F G fam J (t α) (ht α) hRoot
    refine ⟨⟨a, ha⟩, hVal.trans ?_⟩
    change map F fam.T.toGrp G fam.i (t α) =
      map F T₀.toGrp G (CommGroupScheme.groupHom j ≫ fam.i) (r α).val
    rw [map_comp_apply_of_hom, show _ = t α from hr α]

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open GroupScheme AdelicGroupPoints AdelicSiegelFactors PositiveRealTorus

/-- The fundamental split rays of a compatible family exist in its chosen positive
Siegel torus, and have representatives in each corresponding split component. -/
def AdelicSiegelSplitRaysStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    ∀ (fam : StandardParabolicFamily F G)
      (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ fam.T),
      IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j →
    let Δ := simpleRelativeRoots fam.i fam.ν
    ∃ r : Δ → intrinsicSubgroup F T₀,
      (∀ α β : Δ, β ≠ α → characterLog F T₀.toGrp (r α).val (j ≫ β.val) = 0) ∧
      (∀ α : Δ, 0 < characterLog F T₀.toGrp (r α).val (j ≫ α.val)) ∧
      (∀ (α : Δ) (n : ℕ), (r α) ^ n ∈ weakSimpleRootChamber F T₀ fam.T j G fam.i fam.ν 1) ∧
      ∀ (J : StandardIndex F G fam.i fam.ν) (α : Δ), α.val ∉ J.val →
        ∃ a : fam.positiveSplitComponent J,
          map F (fam.P J) G (fam.p J) a.val = positiveMap F G fam.T fam.i T₀ j (r α)

theorem adelicSiegelSplitRays : AdelicSiegelSplitRaysStatement := by
  intro F _ _ G _ _ _ fam T₀ j hsetup
  exact fam.exists_siegelFundamentalRays j hsetup

end Langlands.Global
