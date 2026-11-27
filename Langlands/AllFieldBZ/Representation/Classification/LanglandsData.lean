import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalTwist
import Langlands.AllFieldBZ.Representation.Induction.BlockFactors
import Langlands.Representation.Classification.LanglandsData

/-!
# All-field port of the twisted products of `Langlands.Representation.Classification.LanglandsData`

The determinant-power twist `ν^s A = A ⊗ |det|^s` of a smooth representation of
`GL_r(F)` and the normalized product `i(ν^(u_1) σ_1, …, ν^(u_r) σ_r)` of twisted
blocks, over an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`), with `ν = |det|` for the
residue-normalized absolute value. The original module calls the twist
`segmentFactor`; here it is `determinantPowerTwist`, because the all-field name
`segmentFactor` denotes the twisted members of a segment. See the paired Markdown.
-/

noncomputable section

open CategoryTheory

namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData

universe uV uF

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- The block factor `ν^s A = A ⊗ |det|^s`. -/
abbrev determinantPowerTwist {r : ℕ}
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) (s : ℝ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier) :=
  letI := T.topology
  A.twist (T.determinantPowerCharacter r s) (T.isOpen_ker_determinantPowerCharacter r s)

section Twisted

variable {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- The block family `(ν^(u_1) σ_1, …, ν^(u_r) σ_r)`, with `ν = |det|`. -/
def twistedBlocks
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (u : Fin B.length → ℝ) :
    letI := T.topology
    ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier) :=
  fun i => T.determinantPowerTwist (σ i) (u i)

/-- `i(ν^(u_1) σ_1, …, ν^(u_r) σ_r)`: normalized parabolic induction from the
standard upper block parabolic of `B` of the twisted block family. -/
def twistedProductInduced
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (u : Fin B.length → ℝ) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  (T.normalizedProductInductionFunctor B).obj (T.twistedBlocks B σ u)

theorem twistedProductInduced_representation
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (u : Fin B.length → ℝ) :
    letI := T.topology
    (T.twistedProductInduced B σ u).representation =
      T.normalizedProductInduced B (fun i => (T.twistedBlocks B σ u i).representation) :=
  rfl

/-- Isomorphic block families induce isomorphic representations. -/
def twistedProductInducedIso
    {σ σ' : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)}
    (e : ∀ i, σ i ≅ σ' i) (u : Fin B.length → ℝ) :
    T.twistedProductInduced B σ u ≅ T.twistedProductInduced B σ' u :=
  letI := T.topology
  (T.normalizedProductInductionFunctor B).mapIso
    (Pi.isoMk fun i => SmoothRep.twistIso _
      (T.isOpen_ker_determinantPowerCharacter (B.size i) (u i)) (e i))

end Twisted

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
