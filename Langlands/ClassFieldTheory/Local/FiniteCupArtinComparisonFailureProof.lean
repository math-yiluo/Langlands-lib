import Langlands.ClassFieldTheory.Local.FiniteGeometricCupArtinComparisonProof
import Langlands.ClassFieldTheory.Local.FiniteCupArtinComparisonFailureStatement
import Langlands.ClassFieldTheory.Local.UnramifiedExtensionDegreeProof
import Mathlib.Algebra.Field.ULift

/-!
# The arithmetic inverse-cup character comparison is false
-/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u

open Langlands.LocalClassField

namespace FiniteCupArtinComparisonRefutation

/-- If both the arithmetic comparison and the proved geometric comparison hold
for one extension, every character into `ℤ/[D : F]` squares to one. -/
theorem character_sq_eq_one
    (H : FiniteCupArtinCharacterComparison.{u})
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (D : Type u) [Field D] [Algebra F.Carrier D]
    [FiniteDimensional F.Carrier D] [IsGalois F.Carrier D]
    (ψ : Gal(D/F.Carrier) →* Multiplicative (ZMod (Module.finrank F.Carrier D)))
    (g : Gal(D/F.Carrier)) : ψ g ^ 2 = 1 := by
  let c := FiniteArtinTransferReduction.fundamentalClass F D
  have hc := FiniteArtinTransferReduction.fundamentalClass_spec F D
  have h := FiniteArtinTransferReduction.cup_bijective F D c hc
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (normSubgroup F.Carrier D)
    (abelianizationCupEquiv F.Carrier D c h (Abelianization.of g))
  change normQuotientProjection F.Carrier D a = _ at ha
  have hy : arithmeticReciprocityOfCup F.Carrier D c h
      (normQuotientProjection F.Carrier D a) = Abelianization.of g := by
    rw [ha]
    exact (abelianizationCupEquiv F.Carrier D c h).symm_apply_apply _
  have harith := H p F D c hc h ψ a
  have hgeom := finiteGeometricCupArtinCharacterComparison p F D c hc h ψ a
  rw [geometricReciprocityOfCup_eq_inv, map_inv, hy, Abelianization.lift_apply_of] at hgeom
  rw [hy, Abelianization.lift_apply_of] at harith
  rw [sq, ← inv_mul_cancel (ψ g)]
  congr 1
  exact (hgeom.trans harith.symm).symm

/-- A group of order three has a character into `ℤ/3` whose square is not one. -/
theorem exists_character_sq_ne_one {G : Type*} [Group G] {n : ℕ}
    (hn : Nat.card G = n) (h3 : n = 3) :
    ∃ (ψ : G →* Multiplicative (ZMod n)) (g : G), ψ g ^ 2 ≠ 1 := by
  subst h3
  have : Fact (Nat.card G).Prime := ⟨by rw [hn]; norm_num⟩
  have hcyc : IsCyclic G := isCyclic_of_prime_card rfl
  let e := zmodCyclicMulEquiv hcyc
  let r : ZMod (Nat.card G) ≃+* ZMod 3 := ZMod.ringEquivCongr hn
  refine ⟨(AddMonoidHom.toMultiplicative r.toAddMonoidHom).comp e.symm.toMonoidHom,
    e (Multiplicative.ofAdd 1), ?_⟩
  change Multiplicative.ofAdd (r (Multiplicative.toAdd (e.symm (e (Multiplicative.ofAdd 1))))) ^ 2 ≠ 1
  rw [MulEquiv.symm_apply_apply, toAdd_ofAdd, map_one]
  decide

end FiniteCupArtinComparisonRefutation

open FiniteCupArtinComparisonRefutation in
/-- The arithmetic inverse-cup character comparison fails in every universe:
an unramified cubic extension of the `2`-adic numbers violates it. -/
theorem finiteCupArtinCharacterComparisonFails :
    FiniteCupArtinCharacterComparisonFails.{u} := by
  intro H
  let F : PadicField.{u} 2 := PadicField.ofField (ULift.{u} (Padic 2))
  obtain ⟨E, hgal, -, hdeg⟩ := unramifiedExtensionDegreeExistence.{u} 2 F 3 (by norm_num)
  obtain ⟨ψ, g, hψ⟩ := exists_character_sq_ne_one (G := Gal(E.field/F.Carrier))
    (IsGalois.card_aut_eq_finrank F.Carrier E.field) hdeg
  exact hψ (character_sq_eq_one H F E.field ψ g)

end Langlands.ClassFieldTheory.Local
