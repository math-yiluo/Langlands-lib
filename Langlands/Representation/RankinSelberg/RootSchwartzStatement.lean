import Langlands.Representation.RankinSelberg.QuotientIntegrals

/-! Assembly of the Schwartz factor in the full root-coordinate space. -/

namespace Langlands.RankinSelberg

open HarmonicAnalysis

universe uF

/-- Two tests in the simple-root coordinates and a row test along the final
coordinate combine into a Schwartz test on all root coordinates. -/
def RootSchwartzAssemblyStatement (F : Type uF) [Field F] [TopologicalSpace F]
    [IsTopologicalRing F] [T2Space F] (n : ℕ) : Prop :=
  ∀ (φ φ' : SchwartzBruhat (Fin n → F))
    (Φ : SchwartzBruhat (Fin (n + 1) → F))
    (k : Langlands.GeneralLinear (n + 1) F),
  ∃ Ψ : SchwartzBruhat (Fin (n + 1) → F),
    ∀ x : Fin (n + 1) → F,
      Ψ x = φ (fun i : Fin n => x i.castSucc) *
        φ' (fun i : Fin n => x i.castSucc) * Φ (x (Fin.last n) • lastRow k)

end Langlands.RankinSelberg
