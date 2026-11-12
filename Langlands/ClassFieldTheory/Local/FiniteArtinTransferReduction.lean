import Langlands.ClassFieldTheory.Local.FiniteCupTransfer
import Langlands.ClassFieldTheory.Local.FiniteAbelianizedArtin
import Langlands.ClassFieldTheory.Local.FiniteCupArtinComparisonStatement
import Langlands.ClassFieldTheory.Local.ClassFormationAbsoluteCorestrictionProof

/-!
# Finite Artin transfer reduced to the inverse-cup character comparison
-/

noncomputable section

namespace Langlands.ClassFieldTheory.Local.FiniteArtinTransferReduction

universe u

variable {p : ℕ} [Fact p.Prime]

/-- The exact invariant family used by the carry symbols satisfies the proved
finite class-formation axioms. -/
theorem canonicalClassFormation :
    (localInvariantFamily unramifiedH2Exhaustion.{u} p).RelativeClassFormation :=
  ⟨fun F D _ _ _ _ => finiteRelativeH1Vanishing F.Carrier D,
    localInvariantFamilyRelativeImages unramifiedH2Exhaustion p,
    localInvariantFamilyInflation unramifiedH2Exhaustion p,
    localInvariantFamilyRestriction unramifiedH2Exhaustion p⟩

section Field

variable (F : PadicField.{u} p) (D : Type u) [Field D] [Algebra F.Carrier D]
  [FiniteDimensional F.Carrier D] [IsGalois F.Carrier D]

/-- A positive fundamental class for the actual canonical relative invariant,
chosen using its proved exact invariant image. -/
def fundamentalClass : relativeCohomology F.Carrier D 2 :=
  Classical.choose
    (((localInvariantFamily unramifiedH2Exhaustion p).fundamentalClasses_of_relativeImages
      (localInvariantFamilyRelativeImages unramifiedH2Exhaustion p) F D).1)

theorem fundamentalClass_spec :
    IsFundamentalClass F.Carrier D (FiniteArtinSymbol.relInv F D)
      (fundamentalClass F D) :=
  (Classical.choose_spec
    (((localInvariantFamily unramifiedH2Exhaustion p).fundamentalClasses_of_relativeImages
      (localInvariantFamilyRelativeImages unramifiedH2Exhaustion p) F D).1)).1

/-- Minus-two cup bijectivity for every positive canonical fundamental class
is a consequence of the published Tate theorem and local class formation. -/
theorem cup_bijective (c : relativeCohomology F.Carrier D 2)
    (hc : IsFundamentalClass F.Carrier D (FiniteArtinSymbol.relInv F D) c) :
    Function.Bijective (relativeTateCup F.Carrier D (-2) c) :=
  classFormationTateIsomorphisms Langlands.Tate.tateCupIsomorphism p
    (localInvariantFamily unramifiedH2Exhaustion p) canonicalClassFormation
    F D c hc (-2)

/-- The exact character-comparison target identifies inverse-cup reciprocity
with the concrete abelianized carry-symbol map by finite character separation. -/
theorem arithmeticReciprocityOfCup_eq_symbol
    (hcompare : FiniteCupArtinCharacterComparison.{u})
    (c : relativeCohomology F.Carrier D 2)
    (hc : IsFundamentalClass F.Carrier D (FiniteArtinSymbol.relInv F D) c)
    (h : Function.Bijective (relativeTateCup F.Carrier D (-2) c))
    (a : F.Carrierˣ) :
    arithmeticReciprocityOfCup F.Carrier D c h
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

/-- The geometric finite abelianized symbol uses the same inverse-unit convention
as the published geometric finite Artin family. -/
def geometricSymbol : F.Carrierˣ →* Abelianization Gal(D/F.Carrier) :=
  (FiniteArtinSymbol.abelianizedArtinSymbol F D).comp invMonoidHom

end Field

section Tower

variable (F E : PadicField.{u} p) (D : Type u) [Field D]
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  [Algebra F.Carrier D] [Algebra E.Carrier D] [IsScalarTower F.Carrier E.Carrier D]
  [FiniteDimensional F.Carrier E.Carrier]
  [FiniteDimensional F.Carrier D] [FiniteDimensional E.Carrier D]
  [IsGalois F.Carrier D] [IsGalois E.Carrier D]

/-- The selected classes are compatible with actual base-field restriction.
The middle field is not assumed normal over the base. -/
theorem fundamentalClass_restriction :
    relativeRestriction F.Carrier E.Carrier D 2 (fundamentalClass F D) =
      fundamentalClass E D :=
  (localInvariantFamily unramifiedH2Exhaustion p).fundamentalRestriction_of_relativeClassFormation
    canonicalClassFormation F E D _ _
    (fundamentalClass_spec F D) (fundamentalClass_spec E D)

/-- Conditional only on the exact inverse-cup character comparison, the concrete
arithmetic finite symbols carry field inclusion to genuine finite-coset transfer. -/
theorem arithmeticTransfer (hcompare : FiniteCupArtinCharacterComparison.{u})
    (a : F.Carrierˣ) :
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
  have hsq := arithmeticReciprocityOfCup_restriction F.Carrier E.Carrier D
    (fundamentalClass F D) hbF hbE
    (Langlands.LocalClassField.normQuotientProjection F.Carrier D a)
  rw [normQuotientTowerInclusion_projection,
    arithmeticReciprocityOfCup_eq_symbol E D hcompare _ hE hbE,
    arithmeticReciprocityOfCup_eq_symbol F D hcompare _ hF hbF] at hsq
  exact hsq

/-- The same genuine transfer square holds for the geometric finite symbols,
under the same exact character-comparison premise. -/
theorem geometricTransfer (hcompare : FiniteCupArtinCharacterComparison.{u})
    (a : F.Carrierˣ) :
    geometricSymbol E D (Units.map (algebraMap F.Carrier E.Carrier).toMonoidHom a) =
      relativeGaloisAbelianTransfer F.Carrier E.Carrier D (geometricSymbol F D a) := by
  change FiniteArtinSymbol.abelianizedArtinSymbol E D
      ((Units.map (algebraMap F.Carrier E.Carrier).toMonoidHom a)⁻¹) =
    relativeGaloisAbelianTransfer F.Carrier E.Carrier D
      (FiniteArtinSymbol.abelianizedArtinSymbol F D a⁻¹)
  rw [← map_inv]
  exact arithmeticTransfer F E D hcompare a⁻¹

end Tower

end Langlands.ClassFieldTheory.Local.FiniteArtinTransferReduction
