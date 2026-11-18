import Langlands.BruhatTits.SpecialCompact.StandardLeviBasisTransport
import Langlands.BruhatTits.SpecialCompact.StandardLeviWeakChamberTransport

/-! # Complete simultaneous standard bases inherited by a standard Levi -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.SpecialCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] Langlands.HarishChandraSchwartz.rationalWeightsIsAffine
  Langlands.HarishChandraSchwartz.rationalWeightsTopology
  Langlands.HarishChandraSchwartz.rationalWeightsTopologicalGroup

variable (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) (J : Set (characterLattice S))

local instance basisInheritanceLeviAffineHom : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
local instance basisInheritanceLeviFiniteType : LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  Langlands.HarishChandraSchwartz.leviScheme_locallyOfFiniteType i ν J

/-- Literal preimages of the single original simultaneous basis, selected
before every intrinsic face and member. -/
def standardLeviInheritedBasis {K0 : Subgroup (rationalPoints G)}
    (hBasis : SimultaneousStandardBasisAt i ν K0) :
    Set (Subgroup (rationalPoints (Standard.leviScheme i ν J))) :=
  leviSchemeBasis i ν J hBasis.choose

/-- The same selected inherited family satisfies every clause, including
all actual compatible-component and full contraction/cofinality clauses. -/
theorem standardLeviInheritedBasis_spec
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
    {K0 : Subgroup (rationalPoints G)} (hBasis : SimultaneousStandardBasisAt i ν K0) :
    CompactOpenNormalBasis (Langlands.HarishChandraSchwartz.leviSchemeCompact K0 i ν J)
        (standardLeviInheritedBasis i ν J hBasis) ∧
    ∀ R : Set (characterLattice S), R ⊆ simpleRelativeRoots (Standard.leviTorusHom i ν J) ν →
      InheritedCompactOpenNormalBasis (Langlands.HarishChandraSchwartz.leviSchemeCompact K0 i ν J)
        (standardLeviPoints (Standard.leviTorusHom i ν J) ν R)
        (standardLeviInheritedBasis i ν J hBasis) ∧
      ∃ (A : CommGroupScheme (Spec (CommRingCat.of F))) (q : A.toGrp ⟶ S.toGrp),
        IsCompatibleStandardSplitComponent (Standard.leviTorusHom i ν J) ν R A q ∧
        ∀ K ∈ standardLeviInheritedBasis i ν J hBasis,
          StandardParabolicBasisMember (Standard.leviTorusHom i ν J) ν R q K := by
  dsimp only [standardLeviInheritedBasis]
  obtain ⟨hB, hBR⟩ := hBasis.choose_spec
  obtain ⟨hLB, hLBR⟩ := leviSchemeBasis_basisClauses hG hi hν hJ (fun R hR => (hBR R hR).1)
  refine ⟨hLB, fun R hR => ⟨hLBR R hR, ?_⟩⟩
  have hRJ : R ⊆ J := by rw [simpleRelativeRoots_leviTorusHom_eq hG hi hν hJ] at hR; exact hR
  obtain ⟨-, A, q, hA, hmembers⟩ := hBR R (hRJ.trans hJ)
  refine ⟨A, q, hA.leviScheme i ν hG hi hν J hJ hRJ, ?_⟩
  intro L hL
  obtain ⟨K, hK, rfl⟩ := (mem_leviSchemeBasis i ν J).mp hL
  exact (hmembers K hK).leviScheme i ν J hG hi hν hJ hRJ hA
    (hB.1 K hK).2.2.1 (hB.1 K hK).2.2.2

/-- The full simultaneous standard basis property passes to every actual
canonical standard Levi at the exact inherited original compact subgroup. -/
theorem SimultaneousStandardBasisAt.leviScheme
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
    {K0 : Subgroup (rationalPoints G)} (hBasis : SimultaneousStandardBasisAt i ν K0) :
    SimultaneousStandardBasisAt (Standard.leviTorusHom i ν J) ν
      (Langlands.HarishChandraSchwartz.leviSchemeCompact K0 i ν J) :=
  ⟨standardLeviInheritedBasis i ν J hBasis,
    standardLeviInheritedBasis_spec i ν J hG hi hν hJ hBasis⟩

end Langlands.BruhatTits.SpecialCompact
