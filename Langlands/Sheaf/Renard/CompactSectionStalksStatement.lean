import Langlands.Sheaf.Renard.CompactSectionStalks

/-!
# Statement: stalks are quotients of compact sections

Renard (9 July 2026), II.2.5, Remarque, printed p.42 / PDF p.48.
-/

namespace Langlands.Sheaf.Renard.CompactSectionStalks

open Langlands.Sheaf.Renard.VectorSheafScalars

/-- Renard II.2.5 Remarque: on a t.d. space, the canonical germ map induces a bijection
`F_c(X) / ⟨f · φ, f(x) = 0⟩ ≃ F_x` for every complex vector sheaf `F` and point `x`. -/
def StalkQuotientComparison : Prop :=
  ∀ (X : Type) [TopologicalSpace X], Langlands.Topology.IsLocallyProfinite X →
    ∀ (F : VectorSheaf X) (x : X), Function.Bijective (stalkQuotientMap F x)

end Langlands.Sheaf.Renard.CompactSectionStalks
