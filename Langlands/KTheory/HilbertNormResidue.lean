import Langlands.ClassFieldTheory.Local.Artin.FiniteArtinNormalization
import Langlands.KTheory.KummerCharacter

/-!
# The arithmetic Hilbert norm-residue pairing

For a nonarchimedean local field `F` containing a primitive `n`-th root of
unity, `hilbertNormResidue hζ a b` evaluates the Kummer character of `b` at
the arithmetic Artin symbol of `a`. It has values in `rootsOfUnity n F`.
The comparison `algebraMap_hilbertNormResidue` evaluates it on any `n`-th
root of `b` in a finite abelian extension of `F`.

The order of the arguments and the arithmetic normalization follow Milnor,
*Introduction to Algebraic K-Theory* (1971), §15, Remarks 15.9–15.10,
pp. 151–152 (`milnor-1971-introduction-algebraic-k-theory`).
-/

noncomputable section

namespace Langlands.KTheory

open Polynomial
open Langlands.ClassFieldTheory.Local.Artin Langlands.ClassFieldTheory.Local.KummerNorm

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ} [NeZero n]

/-- The `n`-th Hilbert norm-residue symbol of the units `a` and `b`, with the
arithmetic Artin map acting on an `n`-th root of `b` in its splitting field. -/
def hilbertNormResidue (hζ : (primitiveRoots n F).Nonempty) (a b : Fˣ) :
    rootsOfUnity n F :=
  let R := radicalField F n (b : F)
  letI : IsAbelianGalois F R := isAbelianGalois_radicalField hζ b
  kummerCharacter hζ (rootOfSplitsXPowSubC_pow (n := n) (b : F) R)
    (arithmeticFiniteArtin F R a)

/-- The defining quotient on any chosen root in the radical splitting field. -/
theorem algebraMap_hilbertNormResidue_radicalField
    (hζ : (primitiveRoots n F).Nonempty) (a b : Fˣ)
    {β : radicalField F n (b : F)}
    (hβ : β ^ n = algebraMap F (radicalField F n (b : F)) (b : F)) :
    let R := radicalField F n (b : F)
    letI : IsAbelianGalois F R := isAbelianGalois_radicalField hζ b
    algebraMap F R (hilbertNormResidue hζ a b : Fˣ) = arithmeticFiniteArtin F R a β / β := by
  dsimp only
  rw [hilbertNormResidue, kummerCharacter_eq hζ _ hβ, algebraMap_kummerCharacter]

section FiniteAbelian

variable {E : Type v} [Field E] [Algebra F E] [FiniteDimensional F E] [IsAbelianGalois F E]

/-- In any finite abelian extension containing an `n`-th root of `b`, the one
arithmetic Artin automorphism of `a` computes the symbol by its action on that root. -/
theorem hilbertNormResidue_eq_kummerCharacter (hζ : (primitiveRoots n F).Nonempty)
    (a : Fˣ) {b : Fˣ} {β : E} (hβ : β ^ n = algebraMap F E (b : F)) :
    hilbertNormResidue hζ a b = kummerCharacter hζ hβ (arithmeticFiniteArtin F E a) := by
  let R := radicalField F n (b : F)
  let ρ := rootOfSplitsXPowSubC (NeZero.pos n) (b : F) R
  have hρ : ρ ^ n = algebraMap F R (b : F) := rootOfSplitsXPowSubC_pow (b : F) R
  let : IsAbelianGalois F R := isAbelianGalois_radicalField hζ b
  have hsplits : ((X ^ n - C (b : F)).map (algebraMap F E)).Splits := by
    obtain ⟨ζ, hprim⟩ := hζ
    have hprimE := ((mem_primitiveRoots (NeZero.pos n)).mp hprim).map_of_injective
      (algebraMap F E).injective
    rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
    exact X_pow_sub_C_splits_of_isPrimitiveRoot hprimE hβ
  let ι : R →ₐ[F] E := IsSplittingField.lift R _ hsplits
  let : Algebra R E := ι.toRingHom.toAlgebra
  have : IsScalarTower F R E := IsScalarTower.of_algHom ι
  have hρE : (algebraMap R E ρ) ^ n = algebraMap F E (b : F) := by
    rw [← map_pow, hρ, ← IsScalarTower.algebraMap_apply]
  have hcomp := DFunLike.congr_fun (kummerCharacter_comp_restrictNormalHom (L := E) hζ hρ)
    (arithmeticFiniteArtin F E a)
  change kummerCharacter hζ hρ
      (AlgEquiv.restrictNormalHom R (arithmeticFiniteArtin F E a)) =
    kummerCharacter hζ hρE (arithmeticFiniteArtin F E a) at hcomp
  rw [restrictNormalHom_arithmeticFiniteArtin F R E a] at hcomp
  change kummerCharacter hζ hρ (arithmeticFiniteArtin F R a) = _
  rw [hcomp, kummerCharacter_eq hζ hρE hβ]

/-- The image of the Hilbert symbol in a finite abelian extension containing
`β` with `β ^ n = b` is the quotient of the Artin conjugate of `β` by `β`. -/
theorem algebraMap_hilbertNormResidue (hζ : (primitiveRoots n F).Nonempty)
    (a : Fˣ) {b : Fˣ} {β : E} (hβ : β ^ n = algebraMap F E (b : F)) :
    algebraMap F E (hilbertNormResidue hζ a b : Fˣ) = arithmeticFiniteArtin F E a β / β := by
  rw [hilbertNormResidue_eq_kummerCharacter hζ a hβ, algebraMap_kummerCharacter]

open Langlands.ClassFieldTheory.Local LocalFieldTheory
  LocalFieldTheory.IsNonarchimedeanLocalField in
/-- In an unramified extension containing the root, a uniformizer acts in
the quotient formula by arithmetic Frobenius. -/
theorem algebraMap_hilbertNormResidue_uniformizer [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E]
    [Valuation.HasExtension (ValuativeRel.valuation F) (ValuativeRel.valuation E)]
    [IsUnramifiedValuedExtension F E]
    (hζ : (primitiveRoots n F).Nonempty) (π : Fˣ)
    (hπ : normalizedUnitOrder F (.ofMul π) = 1)
    {b : Fˣ} {β : E} (hβ : β ^ n = algebraMap F E (b : F)) :
    algebraMap F E (hilbertNormResidue hζ π b : Fˣ) =
      arithmeticFrobeniusOfUnramifiedValuation F E β / β := by
  rw [algebraMap_hilbertNormResidue hζ π hβ,
    arithmeticFiniteArtin_of_normalizedUnitOrder_eq_one F E π hπ]

end FiniteAbelian

end Langlands.KTheory
