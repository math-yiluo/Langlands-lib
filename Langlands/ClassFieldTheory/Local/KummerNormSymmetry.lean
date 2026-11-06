import Langlands.ClassFieldTheory.Local.KummerCarrySkew
import Langlands.ClassFieldTheory.Local.RelativeH2InflationProof
import Mathlib.FieldTheory.KummerExtension

/-! # Kummer characters and finite-extension norm symmetry -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u

namespace KummerNorm

open Polynomial

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {n : ℕ} [NeZero n] {a : K}

/-- The positive Kummer character attached to a primitive root and an
irreducible radical splitting field. -/
def character (H : Irreducible (X ^ n - C a))
    [IsSplittingField K L (X ^ n - C a)] {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    Gal(L/K) →* Multiplicative (ZMod n) :=
  (autEquivZmod H L hζ).toMonoidHom

theorem character_injective (H : Irreducible (X ^ n - C a))
    [IsSplittingField K L (X ^ n - C a)] {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    Function.Injective (character (L := L) H hζ) :=
  (autEquivZmod H L hζ).injective

theorem character_action (H : Irreducible (X ^ n - C a))
    [IsSplittingField K L (X ^ n - C a)] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    {α : L} (hα : α ^ n = algebraMap K L a) (g : Gal(L/K)) :
    g α = ζ ^ (character (L := L) H hζ g).toAdd.val • α := by
  have h := autEquivZmod_symm_apply_natCast H L hα hζ
    (character (L := L) H hζ g).toAdd.val
  change (autEquivZmod H L hζ).symm
      (Multiplicative.ofAdd (((autEquivZmod H L hζ) g).toAdd.val : ZMod n)) α =
    ζ ^ ((autEquivZmod H L hζ) g).toAdd.val • α at h
  rw [ZMod.natCast_zmod_val, ofAdd_toAdd, MulEquiv.symm_apply_apply] at h
  exact h

section CommonExtension

variable (K L R M : Type u) [Field K] [Field L] [Field R] [Field M]
  [Algebra K L] [Algebra K R] [Algebra K M]
  [Algebra L M] [Algebra R M] [IsScalarTower K L M] [IsScalarTower K R M]
  [FiniteDimensional K L] [FiniteDimensional K R] [FiniteDimensional K M]
  [IsGalois K L] [IsGalois K R] [IsGalois K M]

/-- Root actions in a common finite Galois extension identify the two norm
conditions. All root-action hypotheses are explicit. -/
theorem norm_iff_of_root_actions
    (χ : Gal(L/K) →* Multiplicative (ZMod n))
    (ψ : Gal(R/K) →* Multiplicative (ZMod n))
    (hχ : Function.Injective χ) (hψ : Function.Injective ψ)
    (a b : Kˣ) (α β ζ : unitsRepresentation K M)
    (hα : (n : ℤ) • α = baseUnit K M a)
    (hβ : (n : ℤ) • β = baseUnit K M b)
    (hζ : (n : ℤ) • ζ = 0)
    (hfix : ∀ g, (unitsRepresentation K M).ρ g ζ = ζ)
    (haction : ∀ g, (unitsRepresentation K M).ρ g α =
      ((χ (AlgEquiv.restrictNormalHom L g)).toAdd.val : ℤ) • ζ + α)
    (hbction : ∀ g, (unitsRepresentation K M).ρ g β =
      ((ψ (AlgEquiv.restrictNormalHom R g)).toAdd.val : ℤ) • ζ + β) :
    b ∈ Langlands.LocalClassField.normSubgroup K L ↔
      a ∈ Langlands.LocalClassField.normSubgroup K R := by
  have hsum := KummerCarry.cyclicClass_add_eq_zero
    (χ.comp (AlgEquiv.restrictNormalHom L))
    (ψ.comp (AlgEquiv.restrictNormalHom R)) a b α β ζ
    hα hβ hζ hfix haction hbction
  rw [← CyclicClassAlgebra.relativeInflation_cyclicClass K L M,
    ← CyclicClassAlgebra.relativeInflation_cyclicClass K R M] at hsum
  rw [← CyclicClassAlgebra.cyclicClass_eq_zero_iff_of_injective χ hχ,
    ← CyclicClassAlgebra.cyclicClass_eq_zero_iff_of_injective ψ hψ]
  obtain ⟨hLi, _⟩ := finiteRelativeH2InflationExactness K L M
  obtain ⟨hRi, _⟩ := finiteRelativeH2InflationExactness K R M
  constructor
  · intro h
    apply hRi
    rw [map_zero]
    rw [h, map_zero, zero_add] at hsum
    exact hsum
  · intro h
    apply hLi
    rw [map_zero]
    rw [h, map_zero, add_zero] at hsum
    exact hsum

end CommonExtension

section RadicalFields

variable (K L R M : Type u) [Field K] [Field L] [Field R] [Field M]
  [Algebra K L] [Algebra K R] [Algebra K M]
  [Algebra L M] [Algebra R M] [IsScalarTower K L M] [IsScalarTower K R M]

omit [NeZero n] in
theorem included_root_power (a : Kˣ) (α : Lˣ)
    (hα : α ^ n = Units.map (algebraMap K L).toMonoidHom a) :
    (n : ℤ) • unitInclusion L M (Additive.ofMul α) = baseUnit K M a := by
  rw [natCast_zsmul]
  apply Units.ext
  change (algebraMap L M (α : L)) ^ n = algebraMap K M (a : K)
  rw [← map_pow, IsScalarTower.algebraMap_apply K L M]
  exact congrArg (algebraMap L M) (congrArg Units.val hα)

theorem included_root_action (a ζ : Kˣ)
    (H : Irreducible (X ^ n - C (a : K)))
    [IsSplittingField K L (X ^ n - C (a : K))] [Normal K L]
    (hζ : IsPrimitiveRoot (ζ : K) n) (α : Lˣ)
    (hα : α ^ n = Units.map (algebraMap K L).toMonoidHom a) (g : Gal(M/K)) :
    let αM : unitsRepresentation K M := unitInclusion L M (Additive.ofMul α)
    let ζM : unitsRepresentation K M := baseUnit K M ζ
    (unitsRepresentation K M).ρ g αM =
      ((character (L := L) H hζ (AlgEquiv.restrictNormalHom L g)).toAdd.val : ℤ) •
        ζM + αM := by
  dsimp only
  rw [natCast_zsmul]
  apply Units.ext
  change g (algebraMap L M (α : L)) =
    (algebraMap K M (ζ : K)) ^
      (character (L := L) H hζ (AlgEquiv.restrictNormalHom L g)).toAdd.val *
        algebraMap L M (α : L)
  rw [← AlgEquiv.restrictNormal_commutes g L]
  have h := character_action H hζ (congrArg Units.val hα)
    (AlgEquiv.restrictNormalHom L g)
  simpa only [AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply,
    Algebra.smul_def, map_mul, map_pow,
    ← IsScalarTower.algebraMap_apply K L M] using congrArg (algebraMap L M) h

/-- Kummer norm symmetry for two irreducible radical fields embedded in a
common finite Galois extension. -/
theorem norm_iff_of_irreducible_radicals
    [FiniteDimensional K L] [FiniteDimensional K R] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K R] [IsGalois K M]
    (a b ζ : Kˣ)
    (Ha : Irreducible (X ^ n - C (a : K)))
    (Hb : Irreducible (X ^ n - C (b : K)))
    [IsSplittingField K L (X ^ n - C (a : K))]
    [IsSplittingField K R (X ^ n - C (b : K))]
    (hζ : IsPrimitiveRoot (ζ : K) n) (α : Lˣ) (β : Rˣ)
    (hα : α ^ n = Units.map (algebraMap K L).toMonoidHom a)
    (hβ : β ^ n = Units.map (algebraMap K R).toMonoidHom b) :
    b ∈ Langlands.LocalClassField.normSubgroup K L ↔
      a ∈ Langlands.LocalClassField.normSubgroup K R := by
  refine norm_iff_of_root_actions K L R M
    (character Ha hζ) (character Hb hζ)
    (character_injective Ha hζ) (character_injective Hb hζ) a b
    (unitInclusion L M (Additive.ofMul α))
    (unitInclusion R M (Additive.ofMul β)) (baseUnit K M ζ)
    (included_root_power K L M a α hα)
    (included_root_power K R M b β hβ) ?_ (baseUnit_fixed K M ζ)
    (included_root_action K L M a ζ Ha hζ α hα)
    (included_root_action K R M b ζ Hb hζ β hβ)
  rw [natCast_zsmul]
  apply Units.ext
  change (algebraMap K M (ζ : K)) ^ n = 1
  rw [← map_pow, hζ.pow_eq_one, map_one]

end RadicalFields

end KummerNorm

end Langlands.ClassFieldTheory.Local
