import Langlands.ClassFieldTheory.Local.UniversalNormPrimePower
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Removing roots of unity using a universal-norm lift -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local.KummerNorm

universe u

open Polynomial Langlands.LocalClassField

variable (K : Type u) [Field K] [CharZero K] (n : ℕ) [NeZero n]

/-- The actual finite root-of-unity field contains a primitive unit. -/
theorem exists_primitive_radicalUnit :
    ∃ ζ : (radicalField K n (1 : K))ˣ,
      IsPrimitiveRoot (ζ : radicalField K n (1 : K)) n := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) n
  have hmem : ζ ∈ radicalField K n (1 : K) := by
    apply IntermediateField.subset_adjoin
    rw [(monic_X_pow_sub_C (1 : K) (NeZero.ne n)).mem_rootSet]
    simp only [map_sub, map_pow, aeval_X, map_one, hζ.pow_eq_one, sub_self]
  let z : radicalField K n (1 : K) := ⟨ζ, hmem⟩
  have hz : IsPrimitiveRoot z n :=
    hζ.of_map_of_injective (IntermediateField.val (radicalField K n (1 : K))).injective
  exact ⟨Units.mk0 z (hz.ne_zero (NeZero.ne n)), hz⟩

/-- A chosen primitive unit in the actual finite root-of-unity intermediate field. -/
def rootOfUnityUnit : (radicalField K n (1 : K))ˣ :=
  (exists_primitive_radicalUnit K n).choose

theorem rootOfUnityUnit_primitive :
    IsPrimitiveRoot (rootOfUnityUnit K n : radicalField K n (1 : K)) n :=
  (exists_primitive_radicalUnit K n).choose_spec

/-- A universal-norm lift to each actual finite intermediate field makes prime
roots descend by the determinant norm, without assuming roots of unity in K. -/
theorem prime_power_of_universal_lift
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    {q : ℕ} (hq : q.Prime) (a : F.Carrierˣ)
    (hLift : ∀ (E : IntermediateField F.Carrier (AlgebraicClosure F.Carrier))
      [FiniteDimensional F.Carrier E],
      ∃ b : Eˣ, normUnits F.Carrier E b = a ∧
        ∀ (R : IntermediateField E (AlgebraicClosure E))
          [FiniteDimensional E R] [IsAbelianGalois E R], b ∈ normSubgroup E R) :
    ∃ c : F.Carrierˣ, c ^ q = a := by
  let : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let : NeZero q := ⟨hq.ne_zero⟩
  let S := radicalField F.Carrier q (1 : F.Carrier)
  let E : FiniteIntermediateExtension F.Carrier := ⟨S, inferInstance⟩
  let F' : PadicField.{u} p := E.asPadicField
  obtain ⟨b, hb, hbU⟩ := hLift S
  obtain ⟨c, hc⟩ := universalNorm_is_prime_power F' hq
    (rootOfUnityUnit F.Carrier q) (rootOfUnityUnit_primitive F.Carrier q) b hbU
  refine ⟨normUnits F.Carrier S c, ?_⟩
  rw [← map_pow, hc, hb]

end Langlands.ClassFieldTheory.Local.KummerNorm
