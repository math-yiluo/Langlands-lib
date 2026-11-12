import Langlands.Representation.Jacquet.FixedVectorCategoryReduction
import Langlands.Representation.Jacquet.BernsteinFixedVectorSplitting
import Langlands.Representation.Aubert.General.StandardFamilyStructure
import Langlands.Representation.Aubert.General.RationalLeviDecomposition
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.StandardLeviIntersectionProof

/-! # Geometric specialization of the Bernstein fixed-vector reduction -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.CuspidalSupport Langlands.Aubert.General.RationalPointFamily
open Langlands.BruhatTits.SpecialCompact
open scoped CategoryTheory.MonObj

universe uF uV

namespace Langlands.Jacquet

section Family

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance standardBernsteinReductionAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance standardBernsteinReductionTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology

/-- The actual Bernstein standard family follows from the published structural
theorems for a maximal split torus of a connected reductive group. -/
theorem standardBernsteinFamily (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν) :
    BernsteinStandardFamily i ν where
  connectedReductive := hG
  maximalSplitTorus := hi
  genericCocharacter := hν
  finiteSimpleRoots := finite_simpleRoot hG hi ν
  decomposition := isSemidirectDecomposition standardCocharacter hG i hi ν hν
  closedUnipotent := isClosed_unipotent_of_isNonarchimedeanLocalField i ν
  closedLevi := isClosed_levi_of_isNonarchimedeanLocalField i ν
  leviDecomposition := isSemidirectDecomposition_in_levi i ν standardLeviIntersection hG hi hν

end Family

/-- The remaining irreducible fixed-level comparison at exactly the geometry
of the published fixed-vector category target. The standard family and its
topological instances are constructed, not supplied as extra hypotheses. -/
def StandardBernsteinFixedVectorVisibilityStatement : Prop :=
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
        ∃ (A : CommGroupScheme (Spec (CommRingCat.of F))) (q : A.toGrp ⟶ S.toGrp),
          IsCompatibleStandardSplitComponent i ν J A q ∧
            StandardParabolicBasisMember i ν J q K.toSubgroup),
      letI : T2Space F := BruhatTits.localField_t2Space F
      letI : LocallyCompactSpace (rationalPoints G) := rationalPoint_locallyCompactSpace F G
      letI : NonarchimedeanGroup (rationalPoints G) :=
        Plancherel.rationalPoints_nonarchimedeanGroup G
      bernsteinFixedVectorVisibility.{uF,uV} i ν
        (standardBernsteinFamily i ν hG hi hν) K

/-- The fixed-vector splitting reduces to the actual Bernstein decomposition
and the one remaining special-level irreducible comparison. -/
theorem standardFixedVectorSplitting_of_bernstein_inputs
    (hBernstein : BernsteinDecompositionStatement.{uF,uV})
    (hVisibility : StandardBernsteinFixedVectorVisibilityStatement.{uF,uV}) :
    StandardFixedVectorSplittingStatement.{uF,uV} := by
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
  exact fixedVectorSplitting_of_bernsteinDecomposition i ν
    (standardBernsteinFamily i ν hG hi hν) K hBernstein hK
    (hVisibility F G hG S i hi ν hν hstandard K₀ hK₀ hIwasawa K hK hKK₀ hnormal hIwahori)

/-- Exact global assembly, with every standard-family and topology obligation
discharged and the four remaining mathematical propositions explicit. -/
theorem fixedVectorCategoryStatements_of_bernstein_inputs
    (hGeneration : StandardFixedVectorSubquotientGenerationStatement.{uF,uV})
    (hNoetherian : Aubert.General.RepresentedParabolic.SmoothRepNoetherianCategoryStatement.{uF,uV})
    (hBernstein : BernsteinDecompositionStatement.{uF,uV})
    (hVisibility : StandardBernsteinFixedVectorVisibilityStatement.{uF,uV}) :
    FixedVectorCategoryStatements.{uF,uV} :=
  fixedVectorCategoryStatements_of_inputs hGeneration hNoetherian
    (standardFixedVectorSplitting_of_bernstein_inputs hBernstein hVisibility)

end Langlands.Jacquet
