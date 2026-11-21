import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionFiniteProductTopologyProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitSectionFiniteProductTopology

/-! # Finite-product topology comparison on rational orbit sections -/

noncomputable section

universe u uV uB

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ)
    (G := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))

/-- The finite-product topology comparison for the actual rational orbit sections. -/
theorem rationalOrbitSectionFiniteProductTopologyStatement_holds :
    RationalOrbitSectionFiniteProductTopologyStatement.{u, uV, uB} hG hi hν I hKc hPK π := by
  obtain ⟨_, hLevel, hTotal⟩ :=
    orbitSectionFiniteProductTopologyStatement_holds.{u, u, uV, 0, uB}
      (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
      K π (RationalPointFamily.leviRationalNormCharacters i ν I)
      (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv
      (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
      (isClosed_standardParabolicPoints_rootSet hG hi hν I) hKc
      (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
      (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
      (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
      (compactOpenCofinal_standardLevi I hKc)
  exact ⟨fun H => finiteDimensional_rationalOrbitSectionFixedCoefficients
    hG hi hν I hKc π H.1 H.2, hLevel, hTotal⟩

end Langlands.HarishChandraSchwartz
