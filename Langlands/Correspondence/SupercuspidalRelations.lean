import Langlands.Correspondence.AutomorphicRelations
import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Classification.SupercuspidalTwist

/-!
# The concrete supercuspidal subspace of the automorphic correspondence domain

The class space is the published Jacquet-vanishing supercuspidal class space.
No preservation of supercuspidality under the smooth dual is assumed.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- The actual Jacquet-vanishing supercuspidal class space at positive rank.
The carrier universe remains independent of the field universe. -/
abbrev SupercuspidalAutomorphicClass (n : ℕ+) :=
  PadicField.SupercuspidalClass.{uV, uF} F (n : ℕ) n.pos

/-- Forget supercuspidality through the actual full-subcategory quotient map. -/
def supercuspidalToAutomorphic {n : ℕ+}
    (π : SupercuspidalAutomorphicClass.{uF, uV} F n) :
    AutomorphicClass.{uF, uV} F n :=
  GeneralLinear.SupercuspidalClass.toSmoothDualClass π

/-- Forgetting this property introduces no new identifications of classes. -/
theorem supercuspidalToAutomorphic_injective {n : ℕ+} :
    Function.Injective (supercuspidalToAutomorphic.{uF, uV} F (n := n)) :=
  GeneralLinear.SupercuspidalClass.toSmoothDualClass_injective

/-- Supercuspidality as the image of the genuine injective class map. -/
def IsSupercuspidalClass {n : ℕ+} (π : AutomorphicClass.{uF, uV} F n) : Prop :=
  ∃ σ : SupercuspidalAutomorphicClass.{uF, uV} F n,
    supercuspidalToAutomorphic F σ = π

/-- Membership in this image has a unique preimage, by the proved injection. -/
theorem isSupercuspidalClass_iff_existsUnique {n : ℕ+}
    (π : AutomorphicClass.{uF, uV} F n) :
    IsSupercuspidalClass F π ↔
      ∃! σ : SupercuspidalAutomorphicClass.{uF, uV} F n,
        supercuspidalToAutomorphic F σ = π := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, hσ, ?_⟩
    intro τ hτ
    exact supercuspidalToAutomorphic_injective F (hτ.trans hσ.symm)
  · rintro ⟨σ, hσ, _⟩
    exact ⟨σ, hσ⟩

/-- Scalar action on a supercuspidal class uses the same full class relation. -/
def SupercuspidalCentralActsBy {n : ℕ+}
    (π : SupercuspidalAutomorphicClass.{uF, uV} F n)
    (a : F.Carrierˣ) (z : ℂˣ) : Prop :=
  CentralActsBy F (supercuspidalToAutomorphic F π) a z

/-- Actual character twist restricted to the two supercuspidal inputs.
Existence of an output for every character remains a separate theorem. -/
def IsSupercuspidalCharacterTwist {n : ℕ+} (χ : QuasiCharacter F)
    (π π' : SupercuspidalAutomorphicClass.{uF, uV} F n) : Prop :=
  IsCharacterTwist F χ
    (supercuspidalToAutomorphic F π) (supercuspidalToAutomorphic F π')

/-- When `χ ∘ det` has open kernel, the restricted twist relation is exactly
the published supercuspidal class twist. -/
theorem isSupercuspidalCharacterTwist_iff_eq_twist {n : ℕ+}
    (χ : QuasiCharacter F)
    (hχ : IsOpen ((determinantQuasiCharacter F n χ).ker :
      Set (GeneralLinear (n : ℕ) F.Carrier)))
    (π π' : SupercuspidalAutomorphicClass.{uF, uV} F n) :
    IsSupercuspidalCharacterTwist F χ π π' ↔
      π' = GeneralLinear.SupercuspidalClass.twist
        (determinantQuasiCharacter F n χ) hχ
        (GeneralLinear.ker_determinant_le_ker_comp χ.toMonoidHom) π := by
  unfold IsSupercuspidalCharacterTwist
  rw [isCharacterTwist_iff_eq_twist F χ hχ]
  unfold supercuspidalToAutomorphic
  rw [← GeneralLinear.SupercuspidalClass.toSmoothDualClass_twist]
  exact GeneralLinear.SupercuspidalClass.toSmoothDualClass_injective.eq_iff

/-- Actual smooth contragredient restricted to supercuspidal inputs.
Existence of a supercuspidal dual is not built into this definition. -/
def IsSupercuspidalSmoothDual {n : ℕ+}
    (π π' : SupercuspidalAutomorphicClass.{uF, uV} F n) : Prop :=
  IsSmoothDual F (supercuspidalToAutomorphic F π) (supercuspidalToAutomorphic F π')

/-- The same actual rank-one character equivalence, on supercuspidal classes. -/
def IsSupercuspidalRankOneCharacter (χ : QuasiCharacter F)
    (π : SupercuspidalAutomorphicClass.{uF, uV} F 1) : Prop :=
  IsRankOneCharacter F χ (supercuspidalToAutomorphic F π)

end Langlands.Correspondence
