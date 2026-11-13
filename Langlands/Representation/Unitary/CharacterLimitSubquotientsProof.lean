import Langlands.Representation.Unitary.CharacterLimitSubquotientsStatement
import Langlands.Representation.Unitary.CharacterLimitLevelInput
import Langlands.Representation.Unitary.CornerFormGluingStatement
import Langlands.Representation.Unitary.CornerFormGluingProof
import Langlands.LinearAlgebra.PositiveTraceForms
import Langlands.Representation.CompactCoefficient.FixedLevelFiniteness
import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.Hecke.CommonInvarianceProof
import Langlands.Representation.Smooth.FixedVectors.OrderProof
import Langlands.Group.GL.LeviCentralQuotientMeasure

/-!
# Unitarity of the irreducible constituents of a character limit
-/

noncomputable section

namespace Langlands

open MeasureTheory HarmonicAnalysis Hecke Filter
open scoped Topology ComplexOrder

universe uG uV

/-- Assembly: the gluing step reduces the statement to level-wise forms. -/
theorem unitaryCharacterLimitSubquotients_of_cornerFormGluing
    (hglue : CornerFormGluingStatement.{uG, uV}) :
    UnitaryCharacterLimitSubquotientsStatement.{uG, uV} := by
  intro G _ _ _ _ _ _ _ _ _ μ _ _ _ π hπ ρ hρ _hirr hunit _hfin hlim τ hτ hsub
  have : μ.IsInvInvariant := isInvInvariant_of_isMulRightInvariant μ
  have hpos : Character.IsPositiveType μ (Character.distribution μ ρ.representation hρ) :=
    Character.IsPositiveType.of_tendsto μ
      (fun k => Character.distribution_isPositiveType μ (hπ k) (hunit k)) hlim
  obtain ⟨C, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hsub
  have := CharacterSeparation.nontrivial_of_isIrreducible hτ
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : τ)
  obtain ⟨U, hU⟩ := τ.isSmooth v₀
  obtain ⟨K₀, hK₀U, hK₀c, -⟩ := TestFunction.commonCompactOpenBiInvariance.{uG} G ∅ U
  have hmem : ∀ K : OpenSubgroup G, K ≤ K₀ →
      v₀ ∈ fixedVectors τ.representation K.toSubgroup := fun K hK =>
    fixedVectors_antitone τ.representation
      (OpenSubgroup.toSubgroup_le.mpr (hK.trans hK₀U)) hU
  -- finite dimension of the fixed spaces of `ρ`, `C` and `τ`
  have hfinρ : ∀ K : OpenSubgroup G,
      FiniteDimensional ℂ (fixedVectors ρ.representation K.toSubgroup) := fun K => hρ.2 K
  have hfinC : ∀ K : OpenSubgroup G,
      FiniteDimensional ℂ (fixedVectors C.representation K.toSubgroup) := fun K =>
    haveI := hfinρ K
    Module.Finite.of_injective (fixedVectorsMap (SmoothRep.hom i) K.toSubgroup)
      (fixedVectorsMap_injective _ hi _)
  have hfinτ : ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
      FiniteDimensional ℂ (fixedVectors τ.representation K.toSubgroup) := fun K hK =>
    haveI := hfinC K
    Module.Finite.of_surjective (fixedVectorsMap (SmoothRep.hom q) K.toSubgroup)
      (fixedVectorsMap_surjective_of_complexAlgebra _ hq C.isSmooth K hK)
  have hsimple : ∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)), K ≤ K₀ →
      letI := cornerModule μ τ.representation τ.isSmooth K hK
      IsSimpleModule (HeckeAlgebra.Corner μ K hK)
        (fixedVectors τ.representation K.toSubgroup) := by
    intro K hK hKK₀
    refine CompactCoefficientClass.isSimpleModule_fixedVectors μ τ.representation τ.isSmooth
      K hK hτ ?_
    intro hbot
    apply hv₀
    have := hmem K hKK₀
    rw [hbot] at this
    exact (Submodule.mem_bot ℂ).mp this
  refine hglue μ τ.representation τ.isSmooth K₀ hK₀c ⟨v₀, hmem K₀ le_rfl, hv₀⟩
    (fun K hK _ => hfinτ K hK) hsimple ?_
  intro K hK hKK₀
  let _ := cornerModule μ ρ.representation hρ.1 K hK
  let _ := cornerModule μ C.representation C.isSmooth K hK
  let _ := cornerModule μ τ.representation τ.isSmooth K hK
  have := cornerModule_isScalarTower μ ρ.representation hρ.1 K hK
  have := cornerModule_isScalarTower μ τ.representation τ.isSmooth K hK
  have := hfinρ K
  have := hsimple K hK hKK₀
  obtain ⟨b⟩ := PositiveTraceForms.exists_starInvariantForm_of_subquotient
    (A := HeckeAlgebra.Corner μ K hK) (fixedVectors ρ.representation K.toSubgroup)
    (fun a => CharacterLimitLevel.trace_cornerAction_star_mul_self_nonneg μ
      ρ.representation hρ hpos K hK a)
    (CharacterLimitLevel.cornerLinearMap μ K hK C.isSmooth hρ.1 (SmoothRep.hom i))
    (CharacterLimitLevel.cornerLinearMap_injective μ K hK C.isSmooth hρ.1 _ hi)
    (CharacterLimitLevel.cornerLinearMap μ K hK C.isSmooth τ.isSmooth (SmoothRep.hom q))
    (CharacterLimitLevel.cornerLinearMap_surjective μ K hK C.isSmooth τ.isSmooth _ hq)
  exact ⟨b.toInnerProductCore, fun f x y => b.adjoint f x y⟩

/-- **Unitarity of the irreducible constituents of a character limit.** If the characters of
irreducible admissible unitarizable `π k` converge on every test function to the character of
an admissible finite-length `ρ`, every irreducible actual subquotient of `ρ` is unitarizable. -/
theorem unitaryCharacterLimitSubquotients :
    UnitaryCharacterLimitSubquotientsStatement.{uG, uV} :=
  unitaryCharacterLimitSubquotients_of_cornerFormGluing CornerFormGluing.cornerFormGluing

end Langlands
