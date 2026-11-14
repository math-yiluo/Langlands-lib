import Langlands.GroupScheme.Reductive.SplitIsogenyRootGraphs
import Langlands.GroupScheme.Reductive.SplitIsogenyGraphReductive
import Langlands.GroupScheme.Reductive.SplitLeviGluingSimpleRoots

/-! # Local-isogeny graphs indexed by source simple roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RootDatumIsogenyRealization

variable {k : Type u} [Field k]
    {G G' : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    [IsAffineHom G'.X.hom] [Smooth G'.X.hom]
    (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G') (t : T ⟶ T')

/-- An actual graph using one local isogeny for each source simple-root
direction. Target directions are the pushforwards under the prescribed torus
map; no target simple-system identification is included. -/
structure SimpleIsogenyGraph where
  split : IsSplitTorus T.toGrp
  directions : LeviGluing.SimpleRootDirections i
  targetDirection : simpleRelativeRoots i directions.chamber → cocharacterLattice T'
  targetDirectionComp : ∀ a, directions.direction a ≫ t = targetDirection a
  comparisons : ∀ a : simpleRelativeRoots i directions.chamber,
    LocalIsogeny i i' t (directions.direction a) (targetDirection a)
  envelope : LocalIsogenyGraphEnvelope comparisons

open Langlands.LinearAlgebra in
/-- Construct the simple-root family and its actual graph directly from the
given root-datum isogeny using the rank-at-most-one realization theorem. -/
def simpleIsogenyGraph
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    {J J' : Type u} [Finite J] [Finite J']
    [Module.Finite ℤ (characterLattice T)] [Module.Finite ℤ (cocharacterLattice T)]
    [Module.Finite ℤ (characterLattice T')] [Module.Finite ℤ (cocharacterLattice T')]
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    {P' : RootDatum J' (characterLattice T') (cocharacterLattice T')}
    [P.IsReduced] [P'.IsReduced]
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P')
    (f : RootDatumIsogeny (ringExpChar k) P' P) :
    SimpleIsogenyGraph i i' (torusMap hT' f) := by
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let S := LeviGluing.simpleRootDirections i hT
  let C := fun a : simpleRelativeRoots i S.chamber =>
    localIsogeny hG hG' hT hT' i i' hi hi' hP hP' f (S.direction a) (S.rankOne a)
  exact
    { split := hT
      directions := S
      targetDirection := fun a => f.coweightMap (S.direction a)
      targetDirectionComp := fun a => comp_torusMap hT' hP.1 hP'.1 f (S.direction a)
      comparisons := C
      envelope := localIsogenyGraphEnvelope C hT }

namespace SimpleIsogenyGraph

omit [Smooth G'.X.hom]

variable {i i' t} (D : SimpleIsogenyGraph i i' t)

abbrev SimpleIndex : Type u := simpleRelativeRoots i D.directions.chamber

/-- The positive source root representative in its chosen local centralizer. -/
def positiveRoot (a : D.SimpleIndex) :
    (D.comparisons a).SourceRoot (a : characterLattice T) :=
  (D.comparisons a).sourceRoot a D.split a.2.1.1.1

/-- The negative representative uses the same local isogeny as its positive. -/
def negativeRoot (a : D.SimpleIndex) :
    (D.comparisons a).SourceRoot (-(a : characterLattice T)) :=
  (D.comparisons a).sourceRoot (-a) D.split (neg_ne_zero.mpr a.2.1.1.1)

abbrev positiveGroup (a : D.SimpleIndex) := (D.positiveRoot a).group
abbrev negativeGroup (a : D.SimpleIndex) := (D.negativeRoot a).group

def positiveHom (a : D.SimpleIndex) : D.positiveGroup a ⟶ D.envelope.group :=
  D.envelope.rootLift a (D.positiveRoot a)

def negativeHom (a : D.SimpleIndex) : D.negativeGroup a ⟶ D.envelope.group :=
  D.envelope.rootLift a (D.negativeRoot a)

theorem positiveHom_closed (a : D.SimpleIndex) : IsClosedSubgroup (D.positiveHom a) :=
  D.envelope.rootLift_closed a (D.positiveRoot a)

theorem negativeHom_closed (a : D.SimpleIndex) : IsClosedSubgroup (D.negativeHom a) :=
  D.envelope.rootLift_closed a (D.negativeRoot a)

instance positiveGroup_smooth (a : D.SimpleIndex) : Smooth (D.positiveGroup a).X.hom :=
  (D.positiveRoot a).smooth

instance negativeGroup_smooth (a : D.SimpleIndex) : Smooth (D.negativeGroup a).X.hom :=
  (D.negativeRoot a).smooth

instance positiveGroup_connected (a : D.SimpleIndex) :
    ConnectedSpace (D.positiveGroup a).X.left :=
  (D.positiveRoot a).connected

instance negativeGroup_connected (a : D.SimpleIndex) :
    ConnectedSpace (D.negativeGroup a).X.left :=
  (D.negativeRoot a).connected

instance positiveGroup_affine (a : D.SimpleIndex) :
    IsAffineHom (D.positiveGroup a).X.hom :=
  (D.positiveHom_closed a).isAffineHom

instance negativeGroup_affine (a : D.SimpleIndex) :
    IsAffineHom (D.negativeGroup a).X.hom :=
  (D.negativeHom_closed a).isAffineHom

omit [Smooth G.X.hom] [IsAffineHom G'.X.hom] in
theorem negative_pairing (a : D.SimpleIndex) :
    latticePairing T (-(a : characterLattice T)) (D.directions.direction a) = 0 := by
  simp only [map_neg, LinearMap.neg_apply, D.directions.annihilates a, neg_zero]

omit [IsAffineHom G'.X.hom] in
theorem positive_first_rep (a : D.SimpleIndex) :
    (RelativeRoot.subgroup i (a : characterLattice T)).IsRepresentedBy
      (D.positiveHom a ≫ D.envelope.first) :=
  D.envelope.rootLift_first_rep D.split a (D.positiveRoot a) a.2.1.1.1
    (D.directions.annihilates a)

omit [IsAffineHom G'.X.hom] in
theorem negative_first_rep (a : D.SimpleIndex) :
    (RelativeRoot.subgroup i (-(a : characterLattice T))).IsRepresentedBy
      (D.negativeHom a ≫ D.envelope.first) :=
  D.envelope.rootLift_first_rep D.split a (D.negativeRoot a)
    (neg_ne_zero.mpr a.2.1.1.1) (D.negative_pairing a)

omit [IsAffineHom G'.X.hom] in
theorem positive_normalized (a : D.SimpleIndex) :
    (SubgroupFunctor.range (D.positiveHom a)).IsNormalizedBy
      (SubgroupFunctor.range D.envelope.torusLift) :=
  D.envelope.range_rootLift_isNormalizedBy a (D.positiveRoot a)

omit [IsAffineHom G'.X.hom] in
theorem negative_normalized (a : D.SimpleIndex) :
    (SubgroupFunctor.range (D.negativeHom a)).IsNormalizedBy
      (SubgroupFunctor.range D.envelope.torusLift) :=
  D.envelope.range_rootLift_isNormalizedBy a (D.negativeRoot a)

omit [IsAffineHom G'.X.hom] in
theorem positive_le_unipotent (a : D.SimpleIndex) :
    SubgroupFunctor.range (D.positiveHom a) ≤
      Dynamic.unipotent
        (CommGroupScheme.groupHom D.directions.chamber ≫ D.envelope.torusLift) :=
  (D.envelope.range_rootLift_le a (D.positiveRoot a)).trans
    (RelativeRoot.subgroup_le_dynamicUnipotent D.envelope.torusLift
      D.directions.chamber a.2.1.2)

omit [IsAffineHom G'.X.hom] in
theorem negative_le_unipotent (a : D.SimpleIndex) :
    SubgroupFunctor.range (D.negativeHom a) ≤
      Dynamic.unipotent
        (CommGroupScheme.groupHom (-D.directions.chamber) ≫ D.envelope.torusLift) := by
  apply (D.envelope.range_rootLift_le a (D.negativeRoot a)).trans
  apply RelativeRoot.subgroup_le_dynamicUnipotent
  simpa only [map_neg, LinearMap.neg_apply, neg_neg] using a.2.1.2

omit [Smooth G.X.hom] [IsAffineHom G'.X.hom] in
/-- The source simple-root family automatically covers the source chamber. -/
theorem source_coverage :
    ∀ α ∈ simpleRelativeRoots i D.directions.chamber,
      ∃ a : D.SimpleIndex, latticePairing T α (D.directions.direction a) = 0 :=
  fun α hα => ⟨⟨α, hα⟩, D.directions.annihilates ⟨α, hα⟩⟩

omit [IsAffineHom G'.X.hom] in
/-- The first projection of the source-simple graph is faithfully flat.
This conclusion needs no target simple-system transport. -/
theorem first_geometry (hG : IsConnectedReductive G) (hi : IsMaximalTorus i)
    {J : Type u} (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (hP : IsRootDatumOf i P) :
    Flat D.envelope.first.hom.hom.left ∧ Surjective D.envelope.first.hom.hom.left ∧
      LocallyOfFinitePresentation D.envelope.first.hom.hom.left ∧
        QuasiCompact D.envelope.first.hom.hom.left := by
  let : ConnectedSpace G.X.left := hG.connectedSpace
  exact D.envelope.first_geometry D.split hi.2.1 P hP D.directions.chamber
    D.directions.generic D.source_coverage
    (LocalIsogenyGraphEnvelope.chamber_centralizer_eq_range hG D.split hi
      D.directions.chamber D.directions.generic)

end SimpleIsogenyGraph

end Langlands.GroupScheme.RootDatumIsogenyRealization
