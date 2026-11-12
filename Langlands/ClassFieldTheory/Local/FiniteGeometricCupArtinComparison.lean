import Langlands.ClassFieldTheory.Local.FiniteArtinTransferReduction
import Langlands.ClassFieldTheory.Local.FiniteGeometricCupArtinComparisonStatement

/-!
# Geometric inverse-cup comparison and finite Artin transfer
-/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u

namespace FiniteArtinTransferReduction

variable {p : ℕ} [Fact p.Prime]

section Field

variable (F : PadicField.{u} p) (D : Type u) [Field D] [Algebra F.Carrier D]
  [FiniteDimensional F.Carrier D] [IsGalois F.Carrier D]

/-- Finite character separation turns the geometric inverse-cup character
comparison into equality with the concrete arithmetic carry symbol. -/
theorem geometricReciprocityOfCup_eq_symbol
    (hcompare : FiniteGeometricCupArtinCharacterComparison.{u})
    (c : relativeCohomology F.Carrier D 2)
    (hc : IsFundamentalClass F.Carrier D (FiniteArtinSymbol.relInv F D) c)
    (h : Function.Bijective (relativeTateCup F.Carrier D (-2) c))
    (a : F.Carrierˣ) :
    geometricReciprocityOfCup F.Carrier D c h
        (Langlands.LocalClassField.normQuotientProjection F.Carrier D a) =
      FiniteArtinSymbol.abelianizedArtinSymbol F D a := by
  let : NeZero (Module.finrank F.Carrier D) := ⟨Module.finrank_pos.ne'⟩
  apply FiniteArtinSymbol.eq_of_forall_character
    (FiniteArtinSymbol.card_abelianized_galois_dvd F D)
  intro ψ
  have hp : Abelianization.lift (ψ.comp Abelianization.of) = ψ :=
    Abelianization.lift.apply_symm_apply ψ
  have h₁ := hcompare p F D c hc h (ψ.comp Abelianization.of) a
  have h₂ := FiniteArtinSymbol.character_abelianizedArtinSymbol F D
    (ψ.comp Abelianization.of) a
  rw [hp] at h₁ h₂
  exact h₁.trans h₂.symm

end Field

section Tower

variable (F E : PadicField.{u} p) (D : Type u) [Field D]
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  [Algebra F.Carrier D] [Algebra E.Carrier D] [IsScalarTower F.Carrier E.Carrier D]
  [FiniteDimensional F.Carrier E.Carrier]
  [FiniteDimensional F.Carrier D] [FiniteDimensional E.Carrier D]
  [IsGalois F.Carrier D] [IsGalois E.Carrier D]

/-- A geometric inverse-cup comparison also proves actual transfer for
the arithmetic carry symbols, with no normality assumption on the middle field. -/
theorem arithmeticTransfer_of_geometricCupComparison
    (hcompare : FiniteGeometricCupArtinCharacterComparison.{u}) (a : F.Carrierˣ) :
    FiniteArtinSymbol.abelianizedArtinSymbol E D
        (Units.map (algebraMap F.Carrier E.Carrier).toMonoidHom a) =
      relativeGaloisAbelianTransfer F.Carrier E.Carrier D
        (FiniteArtinSymbol.abelianizedArtinSymbol F D a) := by
  have hF := fundamentalClass_spec F D
  have hE : IsFundamentalClass E.Carrier D (FiniteArtinSymbol.relInv E D)
      (relativeRestriction F.Carrier E.Carrier D 2 (fundamentalClass F D)) := by
    rw [fundamentalClass_restriction]
    exact fundamentalClass_spec E D
  have hbF := cup_bijective F D _ hF
  have hbE := cup_bijective E D _ hE
  have hsq := geometricReciprocityOfCup_restriction F.Carrier E.Carrier D
    (fundamentalClass F D) hbF hbE
    (Langlands.LocalClassField.normQuotientProjection F.Carrier D a)
  rw [normQuotientTowerInclusion_projection,
    geometricReciprocityOfCup_eq_symbol E D hcompare _ hE hbE,
    geometricReciprocityOfCup_eq_symbol F D hcompare _ hF hbF] at hsq
  exact hsq

/-- Precomposition by unit inversion gives transfer for the geometric
carry symbols under the same comparison premise. -/
theorem geometricTransfer_of_geometricCupComparison
    (hcompare : FiniteGeometricCupArtinCharacterComparison.{u}) (a : F.Carrierˣ) :
    geometricSymbol E D (Units.map (algebraMap F.Carrier E.Carrier).toMonoidHom a) =
      relativeGaloisAbelianTransfer F.Carrier E.Carrier D (geometricSymbol F D a) := by
  change FiniteArtinSymbol.abelianizedArtinSymbol E D
      ((Units.map (algebraMap F.Carrier E.Carrier).toMonoidHom a)⁻¹) =
    relativeGaloisAbelianTransfer F.Carrier E.Carrier D
      (FiniteArtinSymbol.abelianizedArtinSymbol F D a⁻¹)
  rw [← map_inv]
  exact arithmeticTransfer_of_geometricCupComparison F E D hcompare a⁻¹

end Tower

end FiniteArtinTransferReduction

end Langlands.ClassFieldTheory.Local
