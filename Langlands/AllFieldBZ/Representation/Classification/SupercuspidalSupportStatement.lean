import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.Classification.SupercuspidalSupportStatement

/-!
# All-field port of `Langlands.Representation.Classification.SupercuspidalSupportStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Classification.SupercuspidalSupportStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ
open Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
universe uV uF

/-- Every irreducible smooth representation `π` of `GL_n(F)`, `n > 0`, embeds into
`ρ_1 × ⋯ × ρ_k` for some cuspidal data `ρ_1, …, ρ_k`. -/
def GLSupercuspidalEmbeddingStatement : Prop :=
  ∀ (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) (n : ℕ),
    0 < n →
    letI := T.topology
    ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier), π.IsIrreducible →
      ∃ (k : ℕ) (ρ : Fin k → Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.{uV, uF} T), T.IsCuspidalSubrepresentation ρ π

/-- Any two supercuspidal supports of an irreducible smooth representation `π` of
`GL_n(F)`, `n > 0`, are equal. -/
def GLSupercuspidalSupportUniquenessStatement : Prop :=
  ∀ (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) (n : ℕ),
    0 < n →
    letI := T.topology
    ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier), π.IsIrreducible →
      ∀ s s' : Multiset (Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.{uV, uF} T),
        T.IsSupercuspidalSupport π s → T.IsSupercuspidalSupport π s' → s = s'

end Langlands.AllFieldBZ
