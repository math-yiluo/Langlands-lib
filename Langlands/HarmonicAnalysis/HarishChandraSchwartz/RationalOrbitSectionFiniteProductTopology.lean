import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionFiniteProductTopology
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalFourierOrbitContinuity

/-! # Finite-product topology targets on actual rational orbit sections -/

noncomputable section

universe u uV uB

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

local instance instRationalOrbitSectionFiniteProductTopology1
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (RationalPointFamily.rootSet i ν I)
local instance instRationalOrbitSectionFiniteProductTopology2
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    IsAffine (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I)).hom.hom.left
local instance instRationalOrbitSectionFiniteProductTopology3
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    TopologicalSpace
      (rationalPoints (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I))) :=
  rationalPointTopology F (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)).X

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))

/-- The actual fixed coefficient submodule for the standard parabolic on
rational points, with the original product compact-picture action. -/
abbrev rationalOrbitSectionFixedCoefficients (H : OpenSubgroup (rationalPoints G)) :=
  orbitSectionFixedCoefficients
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    K π H

include hKc in
/-- Finiteness follows from the published standard-Levi cofinality and the
actual product fixed-space adapter; it is not an extra hypothesis. -/
theorem finiteDimensional_rationalOrbitSectionFixedCoefficients
    (H : OpenSubgroup (rationalPoints G)) (hHK : H ≤ K) :
    FiniteDimensional ℂ (rationalOrbitSectionFixedCoefficients (K := K) hG hi hν I π H) :=
  finiteDimensional_orbitSectionFixedCoefficients
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    K π hKc (compactOpenCofinal_standardLevi I hKc) H hHK

/-- The fixed-level comparison for the actual standard parabolic and its
canonical unitary character coordinates, for any finite coefficient basis. -/
def RationalOrbitSectionLevelFiniteProductTopologyStatement
    (H : OpenSubgroup (rationalPoints G)) (hHK : H ≤ K)
    {B : Type uB} [Fintype B] [DecidableEq B]
    (b : Module.Basis B ℂ (rationalOrbitSectionFixedCoefficients (K := K) hG hi hν I π H)) : Prop :=
  haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  OrbitSectionLevelFiniteProductTopologyStatement
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    K π (RationalPointFamily.leviRationalNormCharacters i ν I)
    (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) hKc
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
    H hHK b

section Total

variable (d : ∀ H : {H : OpenSubgroup (rationalPoints G) // H ≤ K},
  FiniteDimensional ℂ (rationalOrbitSectionFixedCoefficients (K := K) hG hi hν I π H.1))

/-- The independently constructed finite-product inductive-limit topology on
the existing actual rational orbit section space. -/
@[instance_reducible]
def rationalOrbitSectionFiniteProductTopology :
    TopologicalSpace (rationalInducedOrbitSectionSpace hG hi hν I hKc hPK π) :=
  haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  orbitSectionFiniteProductTopology
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    K π (RationalPointFamily.leviRationalNormCharacters i ν I)
    (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) hKc
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)) d

/-- Equality with the existing topology on the same actual rational section
space. The right side is constructed from the independent finite-product levels. -/
def RationalOrbitSectionTotalFiniteProductTopologyStatement : Prop :=
  (inferInstance : TopologicalSpace (rationalInducedOrbitSectionSpace hG hi hν I hKc hPK π)) =
    rationalOrbitSectionFiniteProductTopology hG hi hν I hKc hPK π d

end Total

/-- Principal actual-point target: finiteness for every fixed level, the level
comparison for every finite basis, and the total inductive-limit comparison.
Only the actual rational structural data are hypotheses. -/
def RationalOrbitSectionFiniteProductTopologyStatement : Prop :=
  ∃ d : ∀ H : {H : OpenSubgroup (rationalPoints G) // H ≤ K},
      FiniteDimensional ℂ (rationalOrbitSectionFixedCoefficients (K := K) hG hi hν I π H.1),
    (∀ (H : {H : OpenSubgroup (rationalPoints G) // H ≤ K})
      (B : Type uB) [Fintype B] [DecidableEq B]
      (b : Module.Basis B ℂ (rationalOrbitSectionFixedCoefficients (K := K) hG hi hν I π H.1)),
      RationalOrbitSectionLevelFiniteProductTopologyStatement
        hG hi hν I hKc hPK π H.1 H.2 b) ∧
    RationalOrbitSectionTotalFiniteProductTopologyStatement hG hi hν I hKc hPK π d

end Langlands.HarishChandraSchwartz
