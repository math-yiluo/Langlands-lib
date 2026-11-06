import Langlands.ClassFieldTheory.Local.ClassFormationAbsoluteCorestrictionProof
import Langlands.ClassFieldTheory.Local.TateAbelianization
import Langlands.ClassFieldTheory.Local.NormStatement

/-! # Finite norm quotients used in the norm-subgroup existence proof -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u

variable {p : ℕ} [Fact p.Prime]

/-- An auxiliary equivalence between the actual Galois abelianization and norm
quotient, chosen from the unconditional local class formation. No transfer or
normalization law is asserted for this choice. -/
def finiteNormAbelianizationEquiv (F : PadicField.{u} p) (L : Type u)
    [Field L] [Algebra F.Carrier L] [FiniteDimensional F.Carrier L]
    [IsGalois F.Carrier L] :
    Abelianization Gal(L/F.Carrier) ≃*
      Langlands.LocalClassField.NormQuotient F.Carrier L :=
  Classical.choice (show Nonempty (Abelianization Gal(L/F.Carrier) ≃*
      Langlands.LocalClassField.NormQuotient F.Carrier L) from by
    obtain ⟨I, _, _, _, _, _, hFund, _, _, _, _, hTate, _⟩ :=
      localAbsoluteCorestrictionCompatibleClassFormation p
    obtain ⟨c, hc, _⟩ := (hFund F L).1
    exact ⟨abelianizationCupEquiv F.Carrier L c (hTate F L c hc (-2))⟩)

/-- A finite Galois extension has a finite actual norm quotient. -/
theorem finite_normQuotient (F : PadicField.{u} p) (L : Type u)
    [Field L] [Algebra F.Carrier L] [FiniteDimensional F.Carrier L]
    [IsGalois F.Carrier L] :
    Finite (Langlands.LocalClassField.NormQuotient F.Carrier L) := by
  let e := finiteNormAbelianizationEquiv F L
  exact Finite.of_injective e.symm e.symm.injective

/-- The actual determinant-norm subgroup has finite index. -/
theorem finiteIndex_normSubgroup (F : PadicField.{u} p) (L : Type u)
    [Field L] [Algebra F.Carrier L] [FiniteDimensional F.Carrier L]
    [IsGalois F.Carrier L] :
    (Langlands.LocalClassField.normSubgroup F.Carrier L).FiniteIndex := by
  let := finite_normQuotient F L
  exact Subgroup.finiteIndex_of_finite_quotient

open scoped IsMulCommutative in
/-- The norm index of a finite abelian extension is exactly its field degree. -/
theorem normSubgroup_index_eq_finrank (F : PadicField.{u} p) (L : Type u)
    [Field L] [Algebra F.Carrier L] [FiniteDimensional F.Carrier L]
    [IsAbelianGalois F.Carrier L] :
    (Langlands.LocalClassField.normSubgroup F.Carrier L).index =
      Module.finrank F.Carrier L := by
  let e := finiteNormAbelianizationEquiv F L
  calc
    (Langlands.LocalClassField.normSubgroup F.Carrier L).index =
        Nat.card (Langlands.LocalClassField.NormQuotient F.Carrier L) := rfl
    _ = Nat.card (Abelianization Gal(L/F.Carrier)) := Nat.card_congr e.toEquiv.symm
    _ = Nat.card Gal(L/F.Carrier) :=
      Nat.card_congr (Abelianization.equivOfComm (H := Gal(L/F.Carrier))).toEquiv.symm
    _ = Module.finrank F.Carrier L := IsGalois.card_aut_eq_finrank _ _

end Langlands.ClassFieldTheory.Local
