import Langlands.Cohomology.LocalMinimalPerfectStatement
import Langlands.Cohomology.PrimeMinimalPerfectProof
import Langlands.Cohomology.PrimeFreeHomotopyDescentProof
import Langlands.Cohomology.PerfectModuleComplexHomotopy

/-! # Local finite free representatives with minimal residue-field ranks -/

universe u

open CategoryTheory

noncomputable section

namespace Langlands.Cohomology.ModuleComplex

attribute [local instance] HasDerivedCategory.standard

/-- A bounded finite projective complex has, near every prime, a finite free
representative with term ranks equal to its residue-field homology dimensions. -/
theorem localMinimalPerfect : LocalMinimalPerfectStatement.{u} := by
  intro R _ K hK p _
  obtain ⟨hfinite, L, hL, hE, hRank⟩ := primeMinimalPerfect R K hK p
  refine ⟨hfinite, ?_⟩
  obtain ⟨r, hr, P, hP, ⟨eP⟩, hPRank⟩ := primeFreeHomotopyDescent R K hK p
    (fun i ↦ Module.finrank p.ResidueField
      (((baseChange (algebraMap R p.ResidueField)).obj K).homology i))
    L hL hE hRank
  exact ⟨r, hr, P, hP, ⟨derivedIsoOfHomotopyEquiv eP⟩, hPRank⟩

end Langlands.Cohomology.ModuleComplex
