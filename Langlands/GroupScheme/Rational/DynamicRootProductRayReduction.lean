import Langlands.GroupScheme.Rational.DynamicRootProductAssembly
import Langlands.GroupScheme.Rational.SemigroupFieldReduction
import Langlands.GroupScheme.Rational.UnipotentSemigroupProductProof
import Langlands.GroupScheme.Rational.SemigroupRealizationProof
import Langlands.GroupScheme.Rational.CyclicRootFunctorComparisonProof
import Langlands.GroupScheme.Rational.DynamicSemigroupProof
import Langlands.GroupScheme.Unipotent.BaseChange

/-! # Dynamic ordered root products from actual root-ray decomposition -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

/-- Smooth connected affine unipotent groups over arbitrary fields have the
exact ordered semigroup-product property for every split-torus action. -/
theorem hasOrderedSemigroupProducts_of_unipotent
    {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (a : AutomorphicAction S.toGrp G) (hS : IsSplitTorus S.toGrp)
    (hG : IsUnipotent G) : HasOrderedSemigroupProducts a := by
  apply HasOrderedSemigroupProducts.of_fieldExtension (K := AlgebraicClosure k) a hS
  let b := algebraBaseMap k (AlgebraicClosure k)
  let G' := (GroupScheme.baseChange b).obj G
  let S' := (CommGroupScheme.baseChange b).obj S
  have haff : IsAffineHom G'.X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  have hsmooth : Smooth G'.X.hom := by
    change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  have hconn : ConnectedSpace G'.X.left :=
    G.connectedSpace_baseChange_of_smooth_affine b
  exact unipotentSemigroupOrderedProduct (AlgebraicClosure k) G' hsmooth haff hconn
    (hG.baseChange (K := AlgebraicClosure k)) S' (hS.baseChange b) (a.baseChange b)

/-- The full Dynamic product follows from actual root-ray decomposition;
no general solvable ordered-product premise remains. -/
def DynamicRootOrderedProductFromRays : Prop :=
  RelativeRootRayDecompositionStatement.{u} → DynamicRootOrderedProductStatement.{u}

/-- Apply arbitrary-field unipotent products inside the actual positive
semigroup realization and discharge the other comparisons by public proofs. -/
theorem dynamicRootOrderedProduct_of_rayDecomposition :
    DynamicRootOrderedProductFromRays.{u} := by
  intro hRays
  apply dynamicRootOrderedProduct_of_splitUnipotentSourceProducts
    semigroupRealization ?_ hRays dynamicSemigroupComparison ?_
  · intro k _ U hUs hAff hUc hUnip _ S hS c
    let := hAff
    let := hUs
    let := hUc
    exact hasOrderedSemigroupProducts_of_unipotent c hS hUnip
  · intro k _ G hG S i hi
    let := hG.isAffineHom
    intro a ha
    exact cyclicRootFunctorComparison k G hG.smooth inferInstance S hi.1.1 i a ha.1

end Langlands.GroupScheme.RelativeRoot
