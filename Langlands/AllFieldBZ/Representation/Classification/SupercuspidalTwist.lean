import Langlands.AllFieldBZ.Group.GL.NormalizedCharacter
import Langlands.Representation.Classification.SupercuspidalTwist

/-!
# All-field port of `Langlands.Representation.Classification.SupercuspidalTwist`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Classification.SupercuspidalTwist` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ
universe uR uG uV uF

namespace Jacquet
open Langlands.Jacquet
variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V]

end Jacquet
namespace GeneralLinear
open Langlands.GeneralLinear
section Ring
variable {R : Type uR} [CommRing R] {n : ℕ}

end Ring
variable {F : Type uF} [Field F] {n : ℕ}

variable [TopologicalSpace F]

namespace SupercuspidalRep
open Langlands.GeneralLinear.SupercuspidalRep
end SupercuspidalRep
namespace SupercuspidalClass
open Langlands.GeneralLinear.SupercuspidalClass
end SupercuspidalClass
end GeneralLinear
namespace LocalFieldPackage
namespace TopologicalData
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- The complex character `g ↦ |det g|^s` with the residue-normalized absolute value. -/
abbrev determinantPowerCharacter (n : ℕ) (s : ℝ) : GeneralLinear n F.Carrier →* ℂˣ :=
  realPowerCharacter (T.determinantNorm n) s

theorem isOpen_ker_determinantPowerCharacter (n : ℕ) (s : ℝ) :
    letI := T.topology
    IsOpen ((T.determinantPowerCharacter n s).ker : Set (GeneralLinear n F.Carrier)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  exact isOpen_ker_realPowerCharacter _ (T.isOpen_ker_determinantNorm n) s

theorem ker_determinant_le_ker_determinantPowerCharacter (n : ℕ) (s : ℝ) :
    (GeneralLinear.determinant : GeneralLinear n F.Carrier →* F.Carrierˣ).ker ≤
      (T.determinantPowerCharacter n s).ker :=
  (GeneralLinear.ker_determinant_le_ker_comp T.normalizedAbsUnits).trans
    (ker_le_realPowerCharacter_ker (T.determinantNorm n) s)

/-- The twist `A ↦ A ⊗ |det|^s` of supercuspidal classes for the topology of `T`. -/
def supercuspidalClassRealPowerTwist (n : ℕ) (s : ℝ) :
    letI := T.topology
    GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := n) →
      GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := n) :=
  letI := T.topology
  GeneralLinear.SupercuspidalClass.twist (T.determinantPowerCharacter n s)
    (T.isOpen_ker_determinantPowerCharacter n s)
    (T.ker_determinant_le_ker_determinantPowerCharacter n s)

end TopologicalData
end LocalFieldPackage
end Langlands.AllFieldBZ
