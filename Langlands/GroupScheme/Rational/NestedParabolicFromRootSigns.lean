import Langlands.GroupScheme.Dynamic.NestedDecomposition
import Langlands.GroupScheme.Rational.DynamicNestedParabolicDecompositionStatement
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsStatement
import Langlands.GroupScheme.Rational.RelativeRootNegationStatement

/-! # Nested dynamic decompositions from the actual-root structural targets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic

/-- Root-sign detection of parabolic inclusion and negation stability give
reverse containment of the dynamic radicals for a common maximal split torus. -/
theorem unipotent_le_of_parabolic_le_of_rootSigns
    (hSigns : RelativeRootSignInclusionsStatement.{u})
    (hNeg : RelativeRootNegationStatement.{u})
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (zeta eta : cocharacterLattice T)
    (hP : parabolic (CommGroupScheme.groupHom zeta ≫ i) ≤
      parabolic (CommGroupScheme.groupHom eta ≫ i)) :
    unipotent (CommGroupScheme.groupHom eta ≫ i) ≤
      unipotent (CommGroupScheme.groupHom zeta ≫ i) := by
  have := hG.isAffineHom
  apply (hSigns k G hG T i hi eta zeta).2
  intro α hα hαeta
  by_contra! hαzeta
  have hz : 0 ≤ latticePairing T (-α) zeta := by
    simpa using (neg_nonneg.mpr hαzeta)
  have he := (hSigns k G hG T i hi zeta eta).1.mp hP
    (-α) (hNeg k G hG T i hi α hα) hz
  have hne : 0 ≤ -(latticePairing T α eta) := by
    simpa using he
  omega

end Dynamic

/-- The two structural actual-root targets suffice for the exact nested
parabolic decomposition target. Both remain explicit premises. -/
def DynamicNestedParabolicDecompositionFromRootSigns : Prop :=
  RelativeRootSignInclusionsStatement.{u} →
    RelativeRootNegationStatement.{u} →
      DynamicNestedParabolicDecompositionStatement.{u}

/-- Conditional assembly using the common maximal split torus supplied by
compatibility. This theorem does not discharge the two structural targets. -/
theorem dynamicNestedParabolicDecomposition_of_rootSigns :
    DynamicNestedParabolicDecompositionFromRootSigns.{u} := by
  intro hSigns hNeg k _ G hG χ ψ hCompat
  have := hG.isAffineHom
  obtain ⟨hP, hM, T, i, zeta, eta, hi, rfl, rfl⟩ := hCompat
  exact Dynamic.nestedLeviDecomposition_of_inclusions _ _ hP hM
    (Dynamic.unipotent_le_of_parabolic_le_of_rootSigns hSigns hNeg hG T i hi
      zeta eta hP)

end Langlands.GroupScheme
