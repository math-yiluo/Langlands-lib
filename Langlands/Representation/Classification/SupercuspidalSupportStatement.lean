import Langlands.Representation.Classification.SupercuspidalSupport

/-!
# Existence and uniqueness of the supercuspidal support

Zelevinsky 1980, Proposition 1.10, for `GL_n` over every p-adic field: every
irreducible smooth representation embeds into a product of supercuspidal
representations, and its supercuspidal support is unique. These are proposition
definitions; nothing is proved here.
-/

namespace Langlands

open PadicField.TopologicalData

universe uV uF

/-- Every irreducible smooth representation `π` of `GL_n(F)`, `n > 0`, embeds into
`ρ_1 × ⋯ × ρ_k` for some cuspidal data `ρ_1, …, ρ_k`. -/
def GLSupercuspidalEmbeddingStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ),
    0 < n →
    letI := T.topology
    ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier), π.IsIrreducible →
      ∃ (k : ℕ) (ρ : Fin k → CuspidalDatum.{uV, uF} T), T.IsCuspidalSubrepresentation ρ π

/-- Any two supercuspidal supports of an irreducible smooth representation `π` of
`GL_n(F)`, `n > 0`, are equal. -/
def GLSupercuspidalSupportUniquenessStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ),
    0 < n →
    letI := T.topology
    ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier), π.IsIrreducible →
      ∀ s s' : Multiset (CuspidalDatum.{uV, uF} T),
        T.IsSupercuspidalSupport π s → T.IsSupercuspidalSupport π s' → s = s'

/-- Zelevinsky's Proposition 1.10: both the embedding and the uniqueness of the
support. -/
def GLSupercuspidalSupportStatement : Prop :=
  GLSupercuspidalEmbeddingStatement.{uV, uF} ∧
    GLSupercuspidalSupportUniquenessStatement.{uV, uF}

end Langlands
