import Langlands.Automorphic.Unramified.RelativeWeilAssociation

noncomputable section

namespace Langlands.ClassField.Global.RelativeWeilGroup

open Langlands.Global Langlands.Unramified

universe u uV

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E] {c : FundamentalClass.ClassFamily.{u}}

/-- Weak association depends only on Euler polynomials outside a finite set. -/
theorem IsWeaklyAssociated.of_sameEulerPolynomials {n : ℕ}
    {A : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    {s t : SpectralSystem (FinitePlace F) n} (hA : IsWeaklyAssociated A s)
    (hst : s.SameEulerPolynomials t) : IsWeaklyAssociated A t := by
  rcases hA with ⟨hc, hn, hA⟩
  refine ⟨hc, hn, ?_⟩
  filter_upwards [hA, hst, t.exceptional.eventually_cofinite_notMem] with v hv hvst ht
  obtain ⟨hs, hm⟩ := hv
  exact ⟨ht, hvst hs ht ▸ hm⟩

end Langlands.ClassField.Global.RelativeWeilGroup
