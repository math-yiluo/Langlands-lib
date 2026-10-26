import Langlands.GroupScheme.MultiplicativeGeometry
import Langlands.Shimura.Unitary.CocharacterReflexConjugator

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E K A : Type} [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K] [Ring A] [Algebra K A] [Algebra E A]
  [IsScalarTower E K A] [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n)

omit [IsScalarTower E K A] in
/-- Actual Harris cocharacters are determined by their rational-model scalar values. -/
theorem complexCocharacter_ext_values
    {χ ψ : (GroupScheme.Gm (Spec (CommRingCat.of ℂ))).toGrp ⟶
      D.complexRationalGroupScheme}
    (h : ∀ u : ℂˣ, D.complexCocharacterValue χ u = D.complexCocharacterValue ψ u) :
    χ = ψ := by
  let : IsSeparated D.complexRationalGroupScheme.X.hom := by
    change IsSeparated (Limits.pullback.snd
      (D.rationalBaseChange (AlgebraInvolution.SchemeModel.scalarBaseMap ℚ ℝ)).X.hom
      DeligneTorus.complexBaseMap)
    infer_instance
  apply GroupScheme.Gm.cocharacter_ext_scalarUnits
  intro u
  apply D.complexRationalPointsEquiv.injective
  exact (D.complexCocharacterValue_eq_points χ u).symm.trans
    ((h u).trans (D.complexCocharacterValue_eq_points ψ u))

variable {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- The actual Kottwitz cocharacter has exactly the real Hodge-function stabilizer. -/
theorem complexCocharacterReflexStabilizer :
    D.ComplexCocharacterReflexStabilizer C := by
  intro hΦ s
  constructor
  · exact D.mem_hodgeStabilizer_of_galois_cocharacter_conjugate C hΦ s
  · intro hs
    obtain ⟨g, _, hg⟩ := D.exists_galois_kottwitz_point_conjugator C hΦ s hs
    let q := D.complexRationalPointsEquiv.symm g
    refine ⟨q, ?_⟩
    apply D.complexCocharacter_ext_values
    intro u
    rw [D.complexCocharacterValue_inner]
    simpa only [q, MulEquiv.apply_symm_apply] using hg u

end Langlands.Shimura.CentralSimpleUnitaryData
