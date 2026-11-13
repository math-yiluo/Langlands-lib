import Langlands.HarmonicAnalysis.PadicLatticeSchwartzExpansionStatement
import Langlands.AllField.HarmonicAnalysis.Conductor
/-! A focused single-level lattice-coset expansion target for scalar local-field test functions. -/

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicLatticeSchwartzExpansionStatement
open Langlands.AllField.HarmonicAnalysis

universe u

/-- Every Schwartz–Bruhat function on a supplied nonarchimedean local field is, at every point,
a finite complex linear combination of indicators of cosets `a i + π^(-m) O`
of one common valuation lattice. All finite data are chosen before the point. -/
def PadicLatticeSchwartzExpansionStatement 
    (F : Type u) [Field F] (T : LocalFieldData F) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  ∀ f : SchwartzBruhat F,
    ∃ (m : ℤ) (N : ℕ) (c : Fin N → ℂ) (a : Fin N → F),
      ∀ x : F,
        f x = ∑ i : Fin N, c i *
          ({z : F | z - a i ∈ T.additiveLattice m}.indicator
            (fun _ => (1 : ℂ))) x

end Langlands.AllField.HarmonicAnalysis
