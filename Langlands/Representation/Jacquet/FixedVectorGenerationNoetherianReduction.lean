import Langlands.Representation.Jacquet.FixedVectorCategoryReduction
import Langlands.Representation.Jacquet.FixedVectorSplittingProof

/-! # The fixed-vector category proposition from VI.9.4 and VI.7.5 alone -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe uF uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.Jacquet

/-- The objectwise splitting used in Renard VI.10.6(iii) follows from VI.9.4 subquotient
closure and VI.7.5 Noetherianity, without the Bernstein decomposition. -/
theorem standardFixedVectorSplitting_of_generation_noetherian
    (hGeneration : StandardFixedVectorSubquotientGenerationStatement.{uF,uV})
    (hNoetherian : Aubert.General.RepresentedParabolic.SmoothRepNoetherianCategoryStatement.{uF,uV}) :
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
  let : SecondCountableTopology (rationalPoints G) := rationalPoint_secondCountableTopology F G
  let : (fixedVectorGenerated.{uF,uV} K.toSubgroup).IsClosedUnderSubobjects :=
    fixedVectorGenerated_subobjectClosure K.toSubgroup
      (fun V hV D hD => hGeneration F G hG S i hi ν hν hstandard
        K₀ hK₀ hIwasawa K hK hKK₀ hnormal hIwahori V hV D hD)
  exact FixedVectorSplitting.fixedVectorSplitting_of_noetherian K hK (hNoetherian F G hG)
    (fun L => secondCountable_openQuotient_small L)

/-- Renard VI.10.6, Proposition (iii)–(iv), reduced to VI.9.4 and VI.7.5: if being generated
by fixed vectors passes to subquotients and the smooth category is Noetherian, then the
published fixed-vector category proposition holds. -/
def FixedVectorCategoryGenerationNoetherianReductionStatement : Prop :=
  StandardFixedVectorSubquotientGenerationStatement.{uF,uV} →
    Aubert.General.RepresentedParabolic.SmoothRepNoetherianCategoryStatement.{uF,uV} →
      FixedVectorCategoryStatements.{uF,uV}

/-- The reduction of Renard VI.10.6 (iii)–(iv) to VI.9.4 and VI.7.5. -/
theorem fixedVectorCategoryGenerationNoetherianReduction :
    FixedVectorCategoryGenerationNoetherianReductionStatement.{uF,uV} :=
  fun hGeneration hNoetherian =>
    fixedVectorCategoryStatements_of_inputs hGeneration hNoetherian
      (standardFixedVectorSplitting_of_generation_noetherian hGeneration hNoetherian)

end Langlands.Jacquet
