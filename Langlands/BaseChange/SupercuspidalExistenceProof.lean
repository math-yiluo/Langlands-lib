import Langlands.BaseChange.SupercuspidalExistenceStatement
import Langlands.Representation.LevelZero.Existence
import Langlands.Representation.Smooth.SmallRealizationProof
import Langlands.Representation.Smooth.RenardCentralCharacterProof

/-!
# Proof of the existence of supercuspidal representations of `GL_n(F)`

The level-zero construction gives an irreducible admissible representation of `GL_n(F)` with
vanishing Jacquet coinvariants on a carrier in the universe of `F`. It has an equivalent
realization in every carrier universe, and its centre acts by a character. See the paired
Markdown.
-/

namespace Langlands.BaseChange

universe u uV

/-- **Existence of supercuspidal representations.** Every positive-rank general linear group
over a nonarchimedean local field has an irreducible supercuspidal representation with a
central character, on a carrier in any universe. -/
theorem supercuspidalExistence : SupercuspidalExistenceStatement.{u, uV} := by
  intro F _ _ _ _ n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := LocalFieldTopology.generalLinear_t2Space F (m + 1)
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F (m + 1)
  have := LocalFieldTopology.generalLinear_secondCountableTopology F (m + 1)
  have := LocalFieldTopology.generalLinear_sigmaCompactSpace F (m + 1)
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F (m + 1)
  obtain ⟨τ, hτ, hadm, hjac⟩ := LevelZero.exists_irreducible_supercuspidal_smoothRep F m
  obtain ⟨σ, hσ, ⟨e⟩⟩ : ∃ σ : SmoothRep.{0, u, uV} ℂ (GeneralLinear (m + 1) F),
      σ.IsIrreducible ∧ Nonempty (τ.representation.Equiv σ.representation) :=
    exists_irreducible_smoothRep_equiv_of_separable τ hτ
  obtain ⟨χ, hχ⟩ := (Renard.Smooth.centralCharacter.{u, uV, uV} (GeneralLinear (m + 1) F)
    (Subgroup.center _) le_rfl).1 σ σ.representation σ.isSmooth hσ
  exact ⟨σ, inferInstance, inferInstance, σ.representation, χ, hσ,
    ⟨isAdmissible_of_equiv e hadm, fun B hB g =>
      (Jacquet.coinvariants_subsingleton_iff e _).mp (hjac B hB g)⟩, fun z v => hχ z v⟩

end Langlands.BaseChange
