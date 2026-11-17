import Langlands.Representation.Jacquet.StandardIwahoriFixedVectorCategoryStatements
import Langlands.Representation.Jacquet.StandardIwahoriDecompositionStatements

/-! # Iwahori-form reduction of the fixed-vector category proposition

Internal derived content: the conditional assembly for Renard VI.10.6 (iii)–(iv),
with the source's Iwahori hypothesis on the compact open subgroup.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe uF uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact Langlands.CuspidalSupport

namespace Langlands.Jacquet

/-- Fixed-vector visibility for the actual standard Bernstein family under precisely
the Iwahori hypotheses of `StandardIwahoriFixedVectorCategoryStatement`.
This is an explicit input to the reduction below, not a proved visibility assertion. -/
def StandardIwahoriBernsteinFixedVectorVisibilityStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : Smooth G.X.hom := hG.smooth
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
      (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)
      (hν : IsGenericCocharacter i ν)
      (_hstandard : ∀ J ⊆ simpleRelativeRoots i ν, ∃ zeta, IsStandardCocharacter i ν J zeta)
      (K₀ : Subgroup (rationalPoints G)) (_hK₀ : IsCompact (K₀ : Set (rationalPoints G)))
      (_hIwasawa : ∀ g : rationalPoints G, ∃ m ∈ standardLeviPoints i ν ∅,
        ∃ n ∈ standardUnipotentPoints i ν ∅, ∃ k ∈ K₀, g = m * n * k)
      (K : OpenSubgroup (rationalPoints G)) (_hK : IsCompact (K : Set (rationalPoints G)))
      (_hKK₀ : K.toSubgroup ≤ K₀) (_hnormal : K₀ ≤ Subgroup.normalizer K.toSubgroup)
      (_hIwahori : ∀ J ⊆ simpleRelativeRoots i ν,
        HasIwahoriIntersectionDecomposition K.toSubgroup (standardLeviPoints i ν J)
          (standardUnipotentPoints i ν J) (standardOppositeUnipotentPoints i ν J)),
      letI : T2Space F := BruhatTits.localField_t2Space F
      letI : LocallyCompactSpace (rationalPoints G) := rationalPoint_locallyCompactSpace F G
      letI : NonarchimedeanGroup (rationalPoints G) :=
        Plancherel.rationalPoints_nonarchimedeanGroup G
      bernsteinFixedVectorVisibility.{uF, uV} i ν
        (standardBernsteinFamily i ν hG hi hν) K

/-- The Iwahori-form category proposition follows from subquotient generation,
Noetherianity of the smooth category, Bernstein decomposition and Iwahori visibility.
The four global statements remain explicit hypotheses. -/
theorem standardIwahoriFixedVectorCategory_of_inputs
    (hGeneration : StandardIwahoriFixedVectorSubquotientGenerationStatement.{uF, uV})
    (hNoetherian :
      Aubert.General.RepresentedParabolic.SmoothRepNoetherianCategoryStatement.{uF, uV})
    (hBernstein : BernsteinDecompositionStatement.{uF, uV})
    (hVisibility : StandardIwahoriBernsteinFixedVectorVisibilityStatement.{uF, uV}) :
    StandardIwahoriFixedVectorCategoryStatement.{uF, uV} := by
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
  let : (fixedVectorGenerated.{uF, uV} K.toSubgroup).IsClosedUnderSubobjects :=
    fixedVectorGenerated_subobjectClosure K.toSubgroup
      (fun V hV D hD => hGeneration F G hG S i hi ν hν hstandard
        K₀ hK₀ hIwasawa K hK hKK₀ hnormal hIwahori V hV D hD)
  have hsplit : fixedVectorSplitting.{uF, uV} K :=
    fixedVectorSplitting_of_bernsteinDecomposition i ν
      (standardBernsteinFamily i ν hG hi hν) K hBernstein hK
      (hVisibility F G hG S i hi ν hν hstandard
        K₀ hK₀ hIwasawa K hK hKK₀ hnormal hIwahori)
  have hleft := levelHecke_isNoetherianRing_of_smoothCategory K hK (hNoetherian F G hG)
  exact ⟨fun V => fixedVectorGenerated_iff_contragredient_of_splitting K hK
    (openSubgroupContainsCompactOpen (rationalPoints G)) hsplit V,
    hleft, (Shimura.LevelHecke.hecke_isNoetherianRing_op_iff ℂ ⟨K, hK⟩).mpr hleft⟩

end Langlands.Jacquet
