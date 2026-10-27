import Langlands.HarmonicAnalysis.Conductor

/-! A focused single-level lattice-coset expansion target for scalar p-adic test functions. -/

namespace Langlands.HarmonicAnalysis

universe u

/-- Every Schwartz–Bruhat function on a supplied p-adic field is, at every point,
a finite complex linear combination of indicators of cosets `a i + π^(-m) O`
of one common valuation lattice. All finite data are chosen before the point. -/
def PadicLatticeSchwartzExpansionStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  ∀ f : SchwartzBruhat F.Carrier,
    ∃ (m : ℤ) (N : ℕ) (c : Fin N → ℂ) (a : Fin N → F.Carrier),
      ∀ x : F.Carrier,
        f x = ∑ i : Fin N, c i *
          ({z : F.Carrier | z - a i ∈ T.additiveLattice m}.indicator
            (fun _ => (1 : ℂ))) x

end Langlands.HarmonicAnalysis
