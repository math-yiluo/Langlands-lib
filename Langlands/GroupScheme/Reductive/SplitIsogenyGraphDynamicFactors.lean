import Langlands.GroupScheme.Reductive.SplitIsogenyGraphDensity
import Langlands.GroupScheme.Reductive.SplitLeviGluingGraphDynamicFactors
import Langlands.GroupScheme.Torus.MaximalSelfCentralizing

/-! # Full dynamic factors and maximal source torus of local-isogeny graphs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme.RootDatumIsogenyRealization

open LeviGluing

variable {k : Type u} [Field k]

variable {G G' : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    [IsAffineHom G'.X.hom] [Smooth G'.X.hom]
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'} {t : T ⟶ T'}
    (D : SimpleIsogenyGraph i i' t)

namespace SimpleIsogenyGraph

/-- Actual smooth closed closures of both generated rational root families,
now representing the full intrinsic graph dynamic factors, with the source
torus representing the full middle factor. -/
structure GraphDynamicFactors where
  negative : RationalClosureEnvelope D.envelope.group D.negativeGenerated
  positive : RationalClosureEnvelope D.envelope.group D.positiveGenerated
  negativeRep : (Dynamic.unipotent (CommGroupScheme.groupHom
    (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
      (CommGroupScheme.groupHom D.directions.chamber ≫ D.envelope.torusLift))).IsRepresentedBy negative.inclusion
  torusRep : (Dynamic.centralizer
    (CommGroupScheme.groupHom D.directions.chamber ≫ D.envelope.torusLift)).IsRepresentedBy D.envelope.torusLift
  positiveRep : (Dynamic.unipotent
    (CommGroupScheme.groupHom D.directions.chamber ≫ D.envelope.torusLift)).IsRepresentedBy positive.inclusion

section Construction

variable [ConnectedSpace G.X.left] [IsAlgClosed k]
    (hi : IsClosedSubgroup i)
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom D.directions.chamber ≫ i) =
      SubgroupFunctor.range i)
    {J J' : Type u} [Finite J] [Finite J']
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (P' : RootDatum J' (characterLattice T') (cocharacterLattice T'))
    [Module.Finite ℤ (characterLattice T)] [Module.Finite ℤ (cocharacterLattice T)]
    [Module.Finite ℤ (characterLattice T')] [Module.Finite ℤ (cocharacterLattice T')]
    [P.IsReduced] [P'.IsReduced]
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P')
    (hT' : IsSplitTorus T'.toGrp) {p : ℕ}
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p P' P)
    (hw : ∀ χ : characterLattice T', t ≫ χ = f.weightMap χ)

/-- Construct the graph's entire dynamic factors from its actual rational
root-family closures and the proved dense graph cell. -/
def graphDynamicFactors : D.GraphDynamicFactors := by
  let χ := CommGroupScheme.groupHom D.directions.chamber ≫ D.envelope.torusLift
  let χn := CommGroupScheme.groupHom
    (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
  let : IsAffine D.envelope.group.X.left :=
    isAffine_of_isAffineHom D.envelope.group.X.hom
  let N := rationalClosureEnvelope D.envelope.group D.negativeGenerated
  let U := rationalClosureEnvelope D.envelope.group D.positiveGenerated
  have hneg : Gm.powerHom (Spec (CommRingCat.of k)) (-1) ≫ D.directions.chamber =
      -D.directions.chamber := by
    simp only [Gm.powerHom_apply, neg_one_zsmul, Preadditive.neg_comp, Category.id_comp]
  have hχn : χn = CommGroupScheme.groupHom (-D.directions.chamber) ≫
      D.envelope.torusLift := by
    dsimp only [χn, χ]
    rw [← Category.assoc]
    change CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1) ≫ D.directions.chamber) ≫ _ = _
    rw [hneg]
  have hnle : SubgroupFunctor.range N.inclusion ≤ Dynamic.unipotent χn := by
    apply N.range_le_of_rationalPoints_le
      (Dynamic.Affine.isRepresentedBy_unipotentHom χn)
      (Dynamic.Affine.isClosedSubgroup_unipotentHom χn)
    rw [hχn]
    exact D.negativeGenerated_le_unipotent
  have hule : SubgroupFunctor.range U.inclusion ≤ Dynamic.unipotent χ := by
    exact U.range_le_of_rationalPoints_le
      (Dynamic.Affine.isRepresentedBy_unipotentHom χ)
      (Dynamic.Affine.isClosedSubgroup_unipotentHom χ) D.positiveGenerated_le_unipotent
  have htle : SubgroupFunctor.range D.envelope.torusLift ≤ Dynamic.centralizer χ :=
    (range_le_torusCentralizer D.envelope.torusLift).trans
      (torusCentralizer_le_dynamicCentralizer D.envelope.torusLift
        (CommGroupScheme.groupHom D.directions.chamber))
  have hsub : D.rationalGraphCell ⊆
      rationalTripleProduct N.inclusion D.envelope.torusLift U.inclusion := by
    rintro x ⟨vt, ⟨v, hv, t, ht, rfl⟩, u, hu, rfl⟩
    exact Set.mul_mem_mul (Set.mul_mem_mul (N.rationalPoints_le hv) ht)
      (U.rationalPoints_le hu)
  have hdense : Dense (rationalPointImage D.envelope.group
      (rationalTripleProduct N.inclusion D.envelope.torusLift U.inclusion)) :=
    (D.dense_rationalGraphCell hi hZ P P' hP hP' hT' f hw).mono (Set.image_mono hsub)
  have hreps := isRepresentedBy_dynamicFactors_of_dense_closed_subcell χ
    N.inclusion D.envelope.torusLift U.inclusion N.closed
    (D.envelope.torusLift_closed hi) U.closed hnle htle hule hdense
  exact ⟨N, U, hreps.1, hreps.2.1, hreps.2.2⟩

omit [ConnectedSpace G.X.left] in
/-- Source reductivity and maximality supply the required chamber centralizer. -/
def graphDynamicFactorsOfReductive
    (hG : IsConnectedReductive G) (hmax : IsMaximalTorus i) :
    D.GraphDynamicFactors := by
  let : ConnectedSpace G.X.left := hG.connectedSpace
  exact D.graphDynamicFactors hmax.2.1
    (LocalIsogenyGraphEnvelope.chamber_centralizer_eq_range hG D.split hmax
      D.directions.chamber D.directions.generic) P P' hP hP' hT' f hw

end Construction

namespace GraphDynamicFactors

variable {D} (E : D.GraphDynamicFactors)

instance negative_smooth : Smooth E.negative.group.X.hom := E.negative.smooth
instance positive_smooth : Smooth E.positive.group.X.hom := E.positive.smooth
instance negative_affine : IsAffineHom E.negative.group.X.hom := E.negative.closed.isAffineHom
instance positive_affine : IsAffineHom E.positive.group.X.hom := E.positive.closed.isAffineHom

omit [IsAffineHom G'.X.hom] [Smooth G'.X.hom] in
include E in
/-- The actual source graph torus is its own whole-torus centralizer. -/
theorem torus_selfCentralizing :
    torusCentralizer D.envelope.torusLift = SubgroupFunctor.range D.envelope.torusLift := by
  apply le_antisymm
  · rw [E.torusRep.2]
    exact torusCentralizer_le_dynamicCentralizer D.envelope.torusLift
      (CommGroupScheme.groupHom D.directions.chamber)
  · exact range_le_torusCentralizer D.envelope.torusLift

instance negative_connected : ConnectedSpace E.negative.group.X.left :=
  DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent D.envelope.group
    (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
      (CommGroupScheme.groupHom D.directions.chamber ≫ D.envelope.torusLift)) E.negativeRep

instance positive_connected : ConnectedSpace E.positive.group.X.left :=
  DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent D.envelope.group
    (CommGroupScheme.groupHom D.directions.chamber ≫ D.envelope.torusLift) E.positiveRep


omit [Smooth G'.X.hom] in
include E in
/-- The actual source graph torus is maximal because it is self-centralizing. -/
theorem isMaximalTorus (hi : IsClosedSubgroup i) :
    IsMaximalTorus D.envelope.torusLift :=
  isMaximalTorus_of_torusCentralizer_eq D.split.isTorus
    (D.envelope.torusLift_closed hi) E.torus_selfCentralizing

omit [Smooth G'.X.hom] in
include E in
/-- The same graph torus is maximal after every field extension in the universe. -/
theorem isMaximalTorus_baseChange (hi : IsClosedSubgroup i)
    (K : Type u) [Field K] [Algebra k K] :
    IsMaximalTorus (T := (CommGroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T)
      ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map D.envelope.torusLift) :=
  isMaximalTorus_baseChange_of_torusCentralizer_eq K D.split.isTorus
    (D.envelope.torusLift_closed hi) E.torus_selfCentralizing

end GraphDynamicFactors

end SimpleIsogenyGraph

end Langlands.GroupScheme.RootDatumIsogenyRealization
