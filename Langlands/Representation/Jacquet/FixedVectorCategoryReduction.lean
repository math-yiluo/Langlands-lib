import Langlands.Representation.Jacquet.FixedVectorCategoryStatements
import Langlands.Representation.Jacquet.FixedVectorDualityReduction
import Langlands.Representation.Jacquet.FixedVectorHeckeNoetherianReduction
import Langlands.Representation.Jacquet.FixedVectorHeckeReduction
import Langlands.Representation.Exponents.SmoothRepNoetherianCategoryStatement
import Langlands.Representation.Plancherel.RationalTwistStabilizer
import Langlands.Shimura.LevelHeckeInversion
import Langlands.Topology.CompactOpen.OpenSubgroup

/-! # The remaining global inputs for the fixed-vector category proposition -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe uF uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.Jacquet

/-- The objectwise splitting used in Renard VI.10.6(iii), with exactly the published
geometric telescope. Its existence remains a separate prerequisite. -/
def StandardFixedVectorSplittingStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : Smooth G.X.hom := hG.smooth
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
      (_hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)
      (_hν : IsGenericCocharacter i ν)
      (_hstandard : ∀ J ⊆ simpleRelativeRoots i ν, ∃ zeta, IsStandardCocharacter i ν J zeta)
      (K₀ : Subgroup (rationalPoints G)) (_hK₀ : IsCompact (K₀ : Set (rationalPoints G)))
      (_hIwasawa : ∀ g : rationalPoints G, ∃ m ∈ standardLeviPoints i ν ∅,
        ∃ n ∈ standardUnipotentPoints i ν ∅, ∃ k ∈ K₀, g = m * n * k)
      (K : OpenSubgroup (rationalPoints G)) (_hK : IsCompact (K : Set (rationalPoints G)))
      (_hKK₀ : K.toSubgroup ≤ K₀) (_hnormal : K₀ ≤ Subgroup.normalizer K.toSubgroup)
      (_hIwahori : ∀ J ⊆ simpleRelativeRoots i ν,
        ∃ (A : CommGroupScheme (Spec (CommRingCat.of F))) (q : A.toGrp ⟶ S.toGrp),
          IsCompatibleStandardSplitComponent i ν J A q ∧
            StandardParabolicBasisMember i ν J q K.toSubgroup),
      fixedVectorSplitting.{uF,uV} K

/-- The exact published fixed-vector category proposition follows from VI.9.4 subquotient
closure, VI.7.5 Noetherianity and the objectwise splitting used in VI.10.6. -/
theorem fixedVectorCategoryStatements_of_inputs
    (hGeneration : StandardFixedVectorSubquotientGenerationStatement.{uF,uV})
    (hNoetherian : Aubert.General.RepresentedParabolic.SmoothRepNoetherianCategoryStatement.{uF,uV})
    (hSplitting : StandardFixedVectorSplittingStatement.{uF,uV}) :
    FixedVectorCategoryStatements.{uF,uV} := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  intro S i hi ν hν hstandard K₀ hK₀ hIwasawa K hK hKK₀ hnormal hIwahori
  let : T2Space F := BruhatTits.localField_t2Space F
  let : LocallyCompactSpace (rationalPoints G) := rationalPoint_locallyCompactSpace F G
  let : NonarchimedeanGroup (rationalPoints G) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  let : SecondCountableTopology (rationalPoints G) := rationalPoint_secondCountableTopology F G
  let : Small.{uV} (rationalPoints G ⧸ K.toSubgroup) := secondCountable_openQuotient_small K
  let : (fixedVectorGenerated.{uF,uV} K.toSubgroup).IsClosedUnderSubobjects :=
    fixedVectorGenerated_subobjectClosure K.toSubgroup
      (fun V hV D hD => hGeneration F G hG S i hi ν hν hstandard
        K₀ hK₀ hIwasawa K hK hKK₀ hnormal hIwahori V hV D hD)
  have hsplit := hSplitting F G hG S i hi ν hν hstandard
    K₀ hK₀ hIwasawa K hK hKK₀ hnormal hIwahori
  have hcat := hNoetherian F G hG
  have hleft := levelHecke_isNoetherianRing_of_smoothCategory K hK hcat
  exact ⟨fun V => fixedVectorGenerated_iff_contragredient_of_splitting K hK
    (openSubgroupContainsCompactOpen (rationalPoints G)) hsplit V,
    hleft, (Shimura.LevelHecke.hecke_isNoetherianRing_op_iff ℂ ⟨K, hK⟩).mpr hleft⟩

end Langlands.Jacquet
