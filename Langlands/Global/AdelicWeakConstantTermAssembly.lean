import Langlands.Global.AdelicAutomorphicConstantTermStatements
import Langlands.Global.AdelicWeakConstantTermExpansionReduction
import Langlands.Global.AdelicWeakConstantTermHalfModulusProof

/-! # Weak terms from ordinary constant-term automorphy and exponent decompositions -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions

/-- Ordinary constant-term automorphy and finite exponent decompositions give existence of
all weak constant terms of a logarithmically square-integrable automorphic form. -/
def AdelicWeakConstantTermAssemblyStatement : Prop :=
  AdelicStandardConstantTermAutomorphyStatement →
    AdelicAutomorphicExponentDecompositionStatement →
      LogSquareIntegrableWeakConstantTermExistenceStatement

/-- Ordinary constant-term automorphy and finite exponent decompositions give every weak
term required in the logarithmic vanishing argument. -/
theorem logSquareIntegrableWeakConstantTermExistence_of_automorphy
    (hAut : AdelicStandardConstantTermAutomorphyStatement)
    (hDec : AdelicAutomorphicExponentDecompositionStatement) :
    LogSquareIntegrableWeakConstantTermExistenceStatement := by
  intro F _ _ G _ _ _ hG K N d rho hsmooth hcalc hKmax hrho fam hK Φ hΦ J
  let Kinf := K.comap (ofInfinite F G).toMonoidHom
  have hTop : fam.IsAutomorphicOn hsmooth Kinf rho fam.top Φ :=
    StandardParabolicFamily.IsWeakConstantTerm.isAutomorphicOn (fam.isWeakConstantTerm_top hΦ)
  have hJ := hAut F G hG K rho hsmooth hKmax hrho fam hK J fam.top (fam.le_top J) Φ hTop
  obtain ⟨s, c, h⟩ := hDec F G hG K rho hsmooth hKmax hrho fam hK J (fam.constantTerm J Φ) hJ
  exact ⟨fam.unitaryExponentSum J s c, s, c, h, rfl⟩

/-- Under ordinary constant-term automorphy and the finite decomposition,
weak constant terms of a logarithmically square-integrable form are transitive. -/
theorem isWeakConstantTerm_of_nested_automorphy
    (hAut : AdelicStandardConstantTermAutomorphyStatement)
    (hDec : AdelicAutomorphicExponentDecompositionStatement)
    {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    {K : Subgroup (AdelicGroupPoints F G)} {N d : ℕ}
    {rho : MatrixRepresentation G (Fin N)} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {hcalc : AdelicDifferentialCommutator F G hsmooth}
    (hKmax : IsMaximalCompactSubgroup F G K) (hrho : IsClosedSubgroup rho)
    (fam : StandardParabolicFamily F G) (hK : IsIwasawaCompact (fam.p fam.bot) K)
    {Q P : StandardIndex F G fam.i fam.ν} (hQP : Q ≤ P)
    {Φ ψ χ : AdelicGroupPoints F G → ℂ} (hΦ : IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ)
    (hψ : fam.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho P Φ ψ)
    (hχ : fam.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho Q Φ χ) :
    fam.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho Q ψ χ := by
  obtain ⟨s, c, hs, heq⟩ := hψ
  refine fam.isWeakConstantTerm_of_nested_decompositions hsmooth
    (K.comap (ofInfinite F G).toMonoidHom) rho hQP standardNestedHalfModulusCompatibility
      hΦ.1.2.1.1 hΦ.1.1 hs heq hχ ?_
  intro lam hlam
  have hJ := hAut F G fam.connectedReductive K rho hsmooth hKmax hrho fam hK Q P hQP
    (c lam) (hs.automorphic lam hlam)
  exact hDec F G fam.connectedReductive K rho hsmooth hKmax hrho fam hK Q (fam.constantTerm Q (c lam)) hJ

end Langlands.Global
