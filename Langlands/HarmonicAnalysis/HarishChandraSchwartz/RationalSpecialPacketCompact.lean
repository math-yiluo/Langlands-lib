import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionTargets
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSpecialCompactConstantTermPremises
import Langlands.BruhatTits.SpecialCompact.AvailableBasisProof
import Langlands.BruhatTits.SpecialCompact.JointBasisFinalAssembly

/-! # The common special compact for the source-normalized packet proof -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.SpecialCompact
open Langlands.Plancherel Langlands.Plancherel.RenardCartan Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

universe u

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)

/-- One compact at the prescribed torus serves the weighted expansion, the
simultaneous normal basis, and the ambient and Levi Cartan arguments. -/
def HasSpecialPacketCompact : Prop :=
  ∃ L : OpenSubgroup (rationalPoints G), IsCompact (L : Set (rationalPoints G)) ∧
    WeakExpansion.IsSpecialVertexCompact ν hi L ∧
    BruhatTits.Iwasawa.ParabolicPointProductFamily i ν (L : Subgroup (rationalPoints G)) ∧
    SimultaneousStandardBasisAt i ν (L : Subgroup (rationalPoints G)) ∧
    RationalPointFamily.FiniteCartanCovering F i ν (L : Subgroup (rationalPoints G)) ∧
    ∀ J ⊆ simpleRelativeRoots i ν, StandardLeviCartanCovering F i ν J (L : Subgroup (rationalPoints G))

private theorem hasSpecialPacketCompact_of_based
    (V : ValuationBuildingData G) (hS : V.S = S) (hVi : HEq V.i i)
    (hV : ∀ v : cocharacterLattice V.S, IsGenericCocharacter V.i v →
      HasSpecialPacketCompact V.isMaximalSplitTorus v)
    (hν : IsGenericCocharacter i ν) : HasSpecialPacketCompact hi ν := by
  obtain ⟨_, SV, iV, hiV, AV, CV, _⟩ := V
  subst hS
  obtain rfl := eq_of_heq hVi
  have he : hiV = hi := Subsingleton.elim _ _
  exact he ▸ hV ν hν

set_option maxHeartbeats 1800000 in
/-- Keep the validity data of the corrected assignment at the common compact.
All structural data use the same special vertex of its rebased apartment. -/
theorem hasSpecialPacketCompact_of_availability
    (hAvail : BruhatTitsAvailabilityStatement.{u}) (hG : IsConnectedReductive G)
    (hν : IsGenericCocharacter i ν) : HasSpecialPacketCompact hi ν := by
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨B₀, hB₀⟩ := hAvail
  obtain ⟨B, hB, hS, hiB⟩ := validAssignmentTorusRebasing B₀ hB₀ F G hG S i hi
  let V := (B.datum F G hG).base.toValuationBuildingData
  refine hasSpecialPacketCompact_of_based hi ν V hS hiB ?_ hν
  intro v hv
  have hA : B.IsAvailableFor F G hG := hB.isAvailableFor
  obtain ⟨x, hx⟩ := availableSpecialVertexExistence F G hG B hA
  obtain ⟨hP, _, hBasis⟩ := availableSimultaneousStandardBasis F G hG B hB v hv x hx
  obtain ⟨hC, hL⟩ := validSpecialCompactRenardCartanComparison F G hG B hB v hv x hx
  let L : OpenSubgroup (rationalPoints G) := ⟨V.apartment.specialCompactSubgroup x, hP.2.1.2.1⟩
  have hspecial : WeakExpansion.IsSpecialVertexCompact v V.isMaximalSplitTorus L :=
    ⟨V.centralizer, V.apartment, hA.affineRootSystem.apartmentAxioms,
      hA.boundedSubgroups, x, hx, hP, rfl⟩
  exact ⟨L, hP.2.1.1, hspecial,
    ((BruhatTits.Iwasawa.availableIwasawa F G hG B hA v hv).1 x hx).2.2.1,
    hBasis, RationalPointFamily.rationalPositiveCartanCover F G V.S V.i v V.apartment x
      V.centralizer.Z V.centralizer.j V.centralizer.s V.centralizer.bijective
      V.centralizer.isRepresentedBy V.centralizer.comp_eq hC,
    fun J hJ => standardLeviCartanCovering_of_compatibility V.apartment x v
      V.centralizer.isRepresentedBy V.centralizer.comp_eq hL hJ⟩

end Langlands.HarishChandraSchwartz
