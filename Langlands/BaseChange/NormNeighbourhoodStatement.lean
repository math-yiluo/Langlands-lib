import Langlands.BaseChange.Norm
import Langlands.JacquetLanglands.RegularElliptic
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Statement: norms and regular elliptic elements near `1`

For a nonarchimedean local field `F` of characteristic zero: (b) if `0 < n`, every
neighbourhood of `1` in `GL_n(F)` contains a regular elliptic element; and for every cyclic
`F`-algebra `E` of group `⟨σ⟩` of order `l`: (a) every element of some neighbourhood of `1` in
`GL_n(F)` is a norm, and (c) the regular semisimple norms form an open subset of `GL_n(F)`
(Henniart–Lemaire 2011, II.6.7, printed p. 123, and II.2.10, printed p. 71). The statement is
not proved here. See the paired Markdown.
-/

namespace Langlands.BaseChange

universe u v

/-- Norms near `1` (Henniart–Lemaire, II.6.7 and II.2.10): (b) if `0 < n`, every neighbourhood
of `1` in `GL_n(F)` contains a regular elliptic element; and for every cyclic `F`-algebra `E`
of group `⟨σ⟩` of order `l`, (a) some neighbourhood of `1` consists of norms and (c) the set of
regular semisimple norms is open. -/
def NormNeighbourhoodStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (n : ℕ),
    (0 < n → ∀ U ∈ nhds (1 : GeneralLinear n F), ∃ γ ∈ U, JacquetLanglands.IsRegularElliptic γ) ∧
    ∀ (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
      [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l : ℕ),
      IsCyclicAlgebra σ l →
      (∃ V ∈ nhds (1 : GeneralLinear n F), ∀ γ ∈ V, IsNorm σ l γ) ∧
      IsOpen {γ : GeneralLinear n F | JacquetLanglands.IsRegularSemisimple γ ∧ IsNorm σ l γ}

end Langlands.BaseChange
