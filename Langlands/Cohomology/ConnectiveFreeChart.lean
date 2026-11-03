import Langlands.Cohomology.PrimeMinimalPerfectProof
import Langlands.Cohomology.PrimeFreeHomotopyDescentProof

/-! # Connective finite free charts for perfect module complexes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology.ModuleComplex

variable {R : Type u} [CommRing R]

/-- A principal-neighborhood finite free model with actual homotopy comparison,
zero negative terms, and the original residue-field homology ranks. -/
structure ConnectiveFreeChart (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (p : Ideal R) [p.IsPrime] where
  parameter : R
  not_mem : parameter ∉ p
  complex : CochainComplex (ModuleCat.{u} (Localization.Away parameter)) ℤ
  finite_free : IsFiniteFree complex
  connective : complex.IsStrictlyGE 0
  equivalence : HomotopyEquiv complex
    ((baseChange (algebraMap R (Localization.Away parameter))).obj K)
  coordinates : ∀ i : ℤ, complex.X i ≃ₗ[Localization.Away parameter]
    (Fin (Module.finrank p.ResidueField
      (((baseChange (algebraMap R p.ResidueField)).obj K).homology i)) →
        Localization.Away parameter)

/-- Negative residue-field homology vanishing forces the minimal local model
and its descended principal-neighborhood model to have zero negative terms. -/
lemma nonempty_connectiveFreeChart (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsStrictlyPerfect K) (p : Ideal R) [p.IsPrime]
    (hnegative : ∀ i : ℤ, i < 0 →
      IsZero (((baseChange (algebraMap R p.ResidueField)).obj K).homology i)) :
    Nonempty (ConnectiveFreeChart K p) := by
  obtain ⟨_, L, hL, hE, hRank⟩ := primeMinimalPerfect R K hK p
  obtain ⟨r, hr, P, hP, ⟨eP⟩, hPRank⟩ := primeFreeHomotopyDescent R K hK p
    (fun i ↦ Module.finrank p.ResidueField
      (((baseChange (algebraMap R p.ResidueField)).obj K).homology i))
    L hL hE hRank
  have hconnective : P.IsStrictlyGE 0 := (P.isStrictlyGE_iff 0).2 (by
    intro i hi
    have := ModuleCat.subsingleton_of_isZero (hnegative i hi)
    have hzero : Module.finrank p.ResidueField
        (((baseChange (algebraMap R p.ResidueField)).obj K).homology i) = 0 :=
      Module.finrank_zero_of_subsingleton
    have : IsEmpty (Fin (Module.finrank p.ResidueField
        (((baseChange (algebraMap R p.ResidueField)).obj K).homology i))) := by
      rw [hzero]
      infer_instance
    have := (hPRank i).some.toEquiv.subsingleton
    exact ModuleCat.isZero_of_subsingleton _)
  exact ⟨⟨r, hr, P, hP, hconnective, eP, fun i ↦ (hPRank i).some⟩⟩

/-- Choose the actual connective finite free chart supplied by residue connectivity. -/
def connectiveFreeChart (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsStrictlyPerfect K) (p : Ideal R) [p.IsPrime]
    (hnegative : ∀ i : ℤ, i < 0 →
      IsZero (((baseChange (algebraMap R p.ResidueField)).obj K).homology i)) :
    ConnectiveFreeChart K p :=
  Classical.choice (nonempty_connectiveFreeChart K hK p hnegative)

/-- The incoming differential used by degree-zero matrix extraction is zero. -/
lemma ConnectiveFreeChart.d_neg_one_zero
    {K : CochainComplex (ModuleCat.{u} R) ℤ} {p : Ideal R} [p.IsPrime]
    (c : ConnectiveFreeChart K p) : c.complex.d (-1) 0 = 0 := by
  have := c.connective
  exact (c.complex.isZero_of_isStrictlyGE 0 (-1) (by decide)).eq_zero_of_src _

end Langlands.Cohomology.ModuleComplex
