import Langlands.Representation.Jacquet.NormalizedCharacterTwistEquiv
import Langlands.Representation.Parabolic.RefinementCharacter
import Langlands.Representation.Geometric.RefinementFunctors
import Langlands.Representation.Filtration.GeneralizedEigencharacterProof
import Langlands.Representation.Twist.LeviRealPower

/-! Actual upper refined real-twist quotients and exact-power spectrum transport. -/

noncomputable section

namespace Langlands

universe uA uF uV

section Generic

variable {A : Type uA} [Group A] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A scalar character twist preserves each supplied uniform power after the
same twist of the eigencharacter. -/
theorem characterSpace_twist_mul (ρ : Representation ℂ A V)
    (η ψ : A →* ℂˣ) (k : ℕ) :
    characterSpace (twist η ρ) (ψ * η) k = characterSpace ρ ψ k := by
  ext v
  simp only [mem_characterSpace]
  have hsub (a : A) : twist η ρ a - ((ψ * η) a : ℂ) • 1 =
      (η a : ℂ) • (ρ a - (ψ a : ℂ) • 1) := by
    change (η a : ℂ) • ρ a - _ = _
    simp only [MonoidHom.mul_apply, Units.val_mul, smul_sub, smul_smul]
    rw [mul_comm (ψ a : ℂ) (η a : ℂ)]
  simp only [hsub, smul_pow, LinearMap.smul_apply, smul_eq_zero,
    pow_ne_zero _ (Units.ne_zero _), false_or]

/-- Removing a character twist shifts the generalized character by its inverse;
there is no fixed-power loss and no semisimplicity premise. -/
theorem isGeneralizedEigencharacter_twist_iff (ρ : Representation ℂ A V)
    (η χ : A →* ℂˣ) :
    IsGeneralizedEigencharacter (twist η ρ) χ ↔
      IsGeneralizedEigencharacter ρ (χ * η⁻¹) := by
  have hχ : χ = (χ * η⁻¹) * η := by
    ext a
    simp [mul_assoc]
  conv_lhs => rw [hχ]
  simp only [IsGeneralizedEigencharacter, characterSpace_twist_mul]

end Generic

namespace PadicField.TopologicalData

open GeneralLinear Geometric

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The actual upper normalized refined Jacquet quotient commutes with the
actual coarse real determinant twist, using the same actual inner modulus. -/
def normalizedRefinedJacquetRealTwistEquiv (ρ : Representation ℂ (B.Levi F.Carrier) V)
    (t : Fin B.length → ℝ) :
    (T.normalizedRefinedJacquet B S (T.leviRealPowerTwist B t ρ)).Equiv
      (twist ((T.leviRealPowerCharacter B t).comp (refinedLevi F.Carrier B S).subtype)
        (T.normalizedRefinedJacquet B S ρ)) :=
  Jacquet.normalizedActionOfModulusTwistEquiv ρ (refinedUnipotent F.Carrier B S)
    (refinedLevi F.Carrier B S) (refinedLevi_le_normalizer B S)
    (T.leviRealPowerCharacter B t)
    ((T.refinedUnipotent_le_normOneLevi B S).trans
      (T.normOneLevi_le_ker_leviRealPowerCharacter B t))
    (T.refinedLeviModulus B S)

@[simp]
theorem normalizedRefinedJacquetRealTwistEquiv_mk
    (ρ : Representation ℂ (B.Levi F.Carrier) V) (t : Fin B.length → ℝ) (v : V) :
    T.normalizedRefinedJacquetRealTwistEquiv B S ρ t
      (refinedJacquetMk B S (T.leviRealPowerTwist B t ρ) v) =
      refinedJacquetMk B S ρ v := rfl

@[simp]
theorem normalizedRefinedJacquetRealTwistEquiv_symm_mk
    (ρ : Representation ℂ (B.Levi F.Carrier) V) (t : Fin B.length → ℝ) (v : V) :
    (T.normalizedRefinedJacquetRealTwistEquiv B S ρ t).symm
      (refinedJacquetMk B S ρ v) =
      refinedJacquetMk B S (T.leviRealPowerTwist B t ρ) v := rfl

/-- The equivalence and inverse character shift on any supplied restriction of
the actual refined Levi, without any centrality assumption on the restriction. -/
theorem normalizedRefinedJacquetRealTwist_isGeneralizedEigencharacter_iff
    {A : Type uA} [Group A] (ρ : Representation ℂ (B.Levi F.Carrier) V)
    (t : Fin B.length → ℝ) (ι : A →* refinedLevi F.Carrier B S) (χ : A →* ℂˣ) :
    IsGeneralizedEigencharacter
      ((T.normalizedRefinedJacquet B S (T.leviRealPowerTwist B t ρ)).comp ι) χ ↔
    IsGeneralizedEigencharacter ((T.normalizedRefinedJacquet B S ρ).comp ι)
      (χ * ((T.leviRealPowerCharacter B t).comp
        ((refinedLevi F.Carrier B S).subtype.comp ι))⁻¹) := by
  let e := T.normalizedRefinedJacquetRealTwistEquiv B S ρ t
  let ec : Representation.Equiv
      ((T.normalizedRefinedJacquet B S (T.leviRealPowerTwist B t ρ)).comp ι)
      (twist ((T.leviRealPowerCharacter B t).comp
          ((refinedLevi F.Carrier B S).subtype.comp ι))
        ((T.normalizedRefinedJacquet B S ρ).comp ι)) :=
    Representation.Equiv.mk e.toLinearEquiv (fun a => e.isIntertwining' (ι a))
  exact (isGeneralizedEigencharacter_iff_of_equiv ec χ).trans
    (isGeneralizedEigencharacter_twist_iff _ _ _)

end PadicField.TopologicalData

end Langlands
