import Langlands.Representation.Exponents.JacquetEigenvectorProof
import Langlands.AllField.Representation.Parabolic.NormalizedJacquetAdmissibilityProof
/-!
# Ordinary eigenvectors for generalized normalized Jacquet exponents

A nonzero generalized-character vector of a commutative action, lying in a
finite-dimensional stable subspace, yields an ordinary eigenvector with the same
character. For the split centre of the normalized Jacquet module the stable
subspace is the space of vectors fixed by an open Levi subgroup, which is
finite-dimensional by normalized Jacquet admissibility.
-/

noncomputable section

namespace Langlands.AllField

universe uF uV uK uA uW

section Generic

variable {K : Type uK} [Field K] {A : Type uA} [CommMonoid A]
variable {W : Type uW} [AddCommGroup W] [Module K W]

end Generic

namespace Parabolic
open Langlands.Parabolic hiding NormalizedJacquetAdmissibilityClause exists_iwahori_levi_subset isAdmissible_leviCoinvariants isSmooth_leviCoinvariants jacquetModuleEquiv_leviCoinvariants normalizedJacquetAdmissibility twist_inverseHalfCharacter_leviCoinvariants twist_inverseHalfCharacter_leviCoinvariants_apply
open Langlands.AllField.Parabolic

variable (F : Type uF) [Field F] (T : LocalFieldData F)
    {n : ℕ} (B : GeneralLinear.BlockShape n) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- On every quotient class, the inverse-half twist of the product-Levi
coinvariants acts as the normalized Jacquet action. -/
theorem twist_inverseHalfCharacter_leviCoinvariants_apply
    (ρ : Representation ℂ (GeneralLinear n F) V) (m : B.Levi F)
    (x : B.JacquetModule ρ) :
    twist (Jacquet.inverseHalfCharacter (T.leviModulus B))
        (leviCoinvariants B (ρ.comp (B.parabolic F).subtype)) m x =
      T.normalizedJacquet B ρ m x := by
  obtain ⟨v, rfl⟩ := B.jacquetMk_surjective ρ x
  rw [T.normalizedJacquet_mk]
  change (Jacquet.inverseHalfCharacter (T.leviModulus B) m : ℂ) •
      leviCoinvariants B (ρ.comp (B.parabolic F).subtype) m (B.jacquetMk ρ v) = _
  rw [Jacquet.inverseHalfCharacter_apply, leviCoinvariants_mk]
  rfl

/-- The inverse-half twist of the product-Levi coinvariants is the normalized
Jacquet representation. -/
theorem twist_inverseHalfCharacter_leviCoinvariants
    (ρ : Representation ℂ (GeneralLinear n F) V) :
    twist (Jacquet.inverseHalfCharacter (T.leviModulus B))
        (leviCoinvariants B (ρ.comp (B.parabolic F).subtype)) =
      T.normalizedJacquet B ρ :=
  MonoidHom.ext fun m => LinearMap.ext fun x =>
    twist_inverseHalfCharacter_leviCoinvariants_apply F T B ρ m x

end Parabolic

end Langlands.AllField
