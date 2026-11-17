import Langlands.Automorphic.CuspidalOperatorMultiplicityOneReduction
import Langlands.Global.AdelicLeviFiniteVolume

/-! # Compact domination of actual Whittaker coefficients

A compact set meeting every rational unipotent orbit supplies a compact
set of evaluation points, uniformly over all rational-invariant functions.
-/

noncomputable section

universe u

open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
  AdelicSubgroupPoints Langlands.Automorphic

local instance dominationSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance dominationSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

local instance dominationUnipotentLocallyCompact (n : ℕ) :
    LocallyCompactSpace (unipotentAdelic F n) :=
  (isClosed_upperUnipotent_adelicPoints F n).locallyCompactSpace

/-- A compact set of group points determines one compact set on which a
pointwise bound controls all its actual Whittaker coefficients. The compact
set is chosen before the character, function, or bound. -/
theorem exists_isCompact_whittaker_domination {r : ℕ}
    (Q : Set (Points F (r + 1))) (hQ : IsCompact Q) :
    ∃ K : Set (Points F (r + 1)), IsCompact K ∧
      ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
      ∀ (f : Points F (r + 1) → ℂ),
        (∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)),
          ∀ x, f (k * x) = f x) →
      ∀ B : ℝ, (∀ x ∈ K, ‖f x‖ ≤ B) →
        ∀ g ∈ Q, ‖whittaker F r ψ f g‖ ≤ B := by
  have := compactSpace_unipotentRationalQuotient F (r + 1)
  obtain ⟨K, hK, hcover⟩ := LeftCosetSpace.exists_isCompact_cover
    (AdelicSubgroupPoints.rationalSubgroup F (Scheme F (r + 1))
      (upperUnipotent F (r + 1)))
  let m : unipotentAdelic F (r + 1) × Points F (r + 1) → Points F (r + 1) :=
    fun p => (p.1 : Points F (r + 1)) * p.2
  have hm : Continuous m :=
    (continuous_subtype_val.comp continuous_fst).mul continuous_snd
  refine ⟨m '' (K ×ˢ Q), (hK.prod hQ).image hm, ?_⟩
  intro ψ hψ f hfΓ B hB g hg
  apply norm_whittaker_le F ψ hψ f g B
  intro v
  obtain ⟨a₀, ha₀, ha₀v⟩ := hcover v
  have hb := hB (((a₀ * v : unipotentAdelic F (r + 1)) : Points F (r + 1)) * g)
    ⟨(a₀ * v, g), ⟨ha₀v, hg⟩, rfl⟩
  rw [Subgroup.coe_mul, mul_assoc,
    hfΓ _ (mem_rationalSubgroup_of_unipotent F ⟨a₀, ha₀⟩)] at hb
  exact hb

/-- The compact domination set for actual cusp Whittaker coefficients can
be chosen in the adelic matrix group used by the operator realization,
uniformly over all cuspidal realizations, characters and vectors. -/
theorem exists_isCompact_cuspWhittaker_domination [CompactSpace (AdeleQuotient F)]
    {r : ℕ} (Q : Set (Points F (r + 1))) (hQ : IsCompact Q) :
    ∃ K : Set (AdelicGL F (r + 1)), IsCompact K ∧
      ∀ (T : CuspidalOperatorRealization F r)
        (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
      ∀ (v : T.Space) (B : ℝ),
        (∀ x ∈ K, ‖ContinuousRationalFunctions.evaluate F (r + 1)
          (T.realization.toContinuous v) x‖ ≤ B) →
        ∀ g ∈ Q, ‖cuspWhittaker F T ψ v g‖ ≤ B := by
  obtain ⟨K, hK, hdom⟩ := exists_isCompact_whittaker_domination F Q hQ
  refine ⟨GeneralLinearGroupPoints.adelicHomeomorph F (r + 1) '' K,
    hK.image (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).continuous, ?_⟩
  intro T ψ hψ v B hB g hg
  apply hdom ψ hψ (cuspFunction F T v)
    (fun k hk x => cuspFunction_rational_mul F T v hk x) B ?_ g hg
  intro x hx
  rw [cuspFunction_apply_eq]
  exact hB _ ⟨x, hx, rfl⟩

end Langlands.Global.RankinSelbergGlobal.Unfolding
