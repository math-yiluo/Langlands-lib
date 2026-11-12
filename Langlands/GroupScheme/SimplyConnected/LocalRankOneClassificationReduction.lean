import Langlands.GroupScheme.SimplyConnected.LocalRankOneWeilReduction
import Langlands.GroupScheme.SimplyConnected.LocalRankOneClassificationStatement
import Langlands.GroupScheme.Quaternionic.LocalSymplecticKneserTitsStatement
import Langlands.GroupScheme.Quaternionic.LocalSpinKneserTitsStatement
import Langlands.GroupScheme.CentralSimpleBinaryRadicalGeneration
import Langlands.GroupScheme.Examples.HermitianRootModelRadicalGeneration
import Langlands.Algebra.LocalDivisionSK1Proof

/-!
# Rank-one local Kneser–Tits from the classification of rank-one groups

This module proves local Kneser–Tits for `SL₂(D)` over a nonarchimedean local
field. It bundles the classification of absolutely almost-simple simply
connected groups of split rank one with the Kneser–Tits statements for the
quaternionic families, and derives from this bundle local Kneser–Tits for all
such groups, family by family as in Prasad–Raghunathan (1985), §2. It also
derives `LocalKneserTitsStatement` from all the open inputs of the published
route.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace CentralSimpleUnits.BinaryRoot

/-- Over a nonarchimedean local field `K`, a connected reductive group isomorphic
to `SL₂(D)` for a finite-dimensional central division `K`-algebra `D` is generated
by the rational points of the unipotent radicals of its parabolic subgroups. -/
theorem parabolicElementarySubgroup_eq_top_of_local_of_iso
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {D : Type u} [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
    [Algebra.IsCentral K D]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (hG : IsConnectedReductive G) (e : G ≅ groupScheme K D) :
    parabolicElementarySubgroup G = ⊤ := by
  have h := rationalPoints_range_le_parabolicElementarySubgroup_of_iso K hG e (𝟙 G)
    (Langlands.CentralDivision.localSK1 K D)
  apply top_unique
  intro x _
  exact h ⟨x, Category.comp_id x⟩

end CentralSimpleUnits.BinaryRoot

/-- The classification of absolutely almost-simple simply connected groups of
split rank one over nonarchimedean local fields, together with the Kneser–Tits
statements for the quaternionic symplectic and spin groups of rank one. -/
def LocalRankOneClassificationStatements : Prop :=
  LocalRankOneClassificationStatement.{u} ∧
    Quaternionic.LocalSymplecticKneserTitsStatement.{u} ∧
      Quaternionic.LocalSpinKneserTitsStatement.{u}

/-- The classification of absolutely almost-simple simply connected groups of
split rank one over nonarchimedean local fields and the Kneser–Tits statements
for the quaternionic symplectic and spin groups give local Kneser–Tits for all
absolutely almost-simple simply connected groups of split rank one. -/
theorem localAbsolutelyAlmostSimpleRankOneKneserTits_of_classification
    (h : LocalRankOneClassificationStatements.{u}) :
    LocalAbsolutelyAlmostSimpleRankOneKneserTitsStatement.{u} := by
  obtain ⟨hcl, hsp, hspin⟩ := h
  intro K _ _ _ _ G _ hsc habs h1
  have hred : IsConnectedReductive G := hsc.isSemisimple.isConnectedReductive
  rcases hcl K G hsc habs h1 with
    ⟨D, _, _, _, _, ⟨e⟩⟩ |
    ⟨L, _, _, _, _, m, -, H, w, hw, hH, ⟨e⟩⟩ |
    ⟨D, _, _, _, _, hD, σ, hσ,
      ⟨m, _, hm, H, hH, hu, hwitt, ⟨e⟩⟩ | ⟨m, hm, q, hq, hwitt, π, hπ⟩⟩
  · exact CentralSimpleUnits.BinaryRoot.parabolicElementarySubgroup_eq_top_of_local_of_iso
      K hred e
  · exact HermitianRoot.SchemeModel.parabolicElementarySubgroup_eq_top_of_iso
      K L H w hw hH hred e
  · exact (parabolicElementarySubgroup_eq_top_iff_iso e).mpr
      (hsp K D hD σ hσ m hm H hH hu hwitt)
  · exact hspin K D hD σ hσ m hm q hq hwitt G π hπ

/-- Local Kneser–Tits from the open inputs of the published route, with the
absolutely almost-simple rank-one case supplied by the classification and the
quaternionic Kneser–Tits statements. -/
theorem localKneserTits_of_rankOneLeviFactors_of_classification
    (hfac : RankOneLeviFactorStatements.{u})
    (hloc : LocalSimplyConnectedCocycleVanishingStatement.{u})
    (hW : SimplyConnectedAlmostSimpleWeilRestrictionStatement.{u})
    (hrank : AffineWeilSplitRankStatement.{u})
    (hpar : AffineWeilParabolicElementarySubgroupStatement.{u})
    (hcl : LocalRankOneClassificationStatements.{u}) :
    LocalKneserTitsStatement.{u} :=
  localKneserTits_of_rankOneLeviFactors_of_absolutelyAlmostSimple hfac hloc hW hrank hpar
    (localAbsolutelyAlmostSimpleRankOneKneserTits_of_classification hcl)

end Langlands.GroupScheme
