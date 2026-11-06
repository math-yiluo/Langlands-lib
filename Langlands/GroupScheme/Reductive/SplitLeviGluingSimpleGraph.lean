import Langlands.GroupScheme.Reductive.SplitLeviGluingRootGraphs
import Langlands.GroupScheme.Reductive.SplitLeviGluingMixedRoots
import Langlands.GroupScheme.Rational.RootSubgroupPositive

/-! # The actual graph and its paired simple-root families -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LeviGluing

variable {k : Type u} [Field k]
    {G₁ G₂ : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G₁.X.hom] [Smooth G₁.X.hom]
    [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom]
    (i₁ : T.toGrp ⟶ G₁) (i₂ : T.toGrp ⟶ G₂)

/-- The graph built from one local comparison along each intrinsic simple-root
kernel direction, including the distinguished common torus. -/
structure SimpleComparisonGraph where
  split : IsSplitTorus T.toGrp
  directions : SimpleRootDirections i₁
  comparisons : ∀ a : simpleRelativeRoots i₁ directions.chamber,
    LocalComparison i₁ i₂ (directions.direction a)
  envelope : LocalGraphEnvelope comparisons

/-- Construct all local sources and the actual generated graph from the local
gluing premise, without a chosen root family or graph among the inputs. -/
def simpleComparisonGraph [ConnectedSpace G₁.X.left]
    (hT : IsSplitTorus T.toGrp) (hlocal : RankOneLeviHypothesis i₁ i₂) :
    SimpleComparisonGraph i₁ i₂ := by
  let S := simpleRootDirections i₁ hT
  let C := canonicalLocalComparisons i₁ i₂ S.direction hlocal S.rankOne
  exact
    { split := hT
      directions := S
      comparisons := C
      envelope := localGraphEnvelope C hT }

namespace SimpleComparisonGraph

variable {i₁ i₂} (D : SimpleComparisonGraph i₁ i₂)

abbrev SimpleIndex : Type u := simpleRelativeRoots i₁ D.directions.chamber

/-- The positive intrinsic root representatives for a simple root, constructed
inside the same chosen local Levi comparison as its negative. -/
def positiveRoot (a : D.SimpleIndex) :
    (D.comparisons a).RootComparison (a : characterLattice T) :=
  (D.comparisons a).rootComparison a D.split a.2.1.1.1

/-- The negative intrinsic root representatives in the same local comparison. -/
def negativeRoot (a : D.SimpleIndex) :
    (D.comparisons a).RootComparison (-(a : characterLattice T)) :=
  (D.comparisons a).rootComparison (-a) D.split (neg_ne_zero.mpr a.2.1.1.1)

abbrev positiveGroup (a : D.SimpleIndex) := (D.positiveRoot a).left
abbrev negativeGroup (a : D.SimpleIndex) := (D.negativeRoot a).left

/-- The actual positive simple-root map into the generated graph. -/
def positiveHom (a : D.SimpleIndex) : D.positiveGroup a ⟶ D.envelope.group :=
  D.envelope.rootLift a (D.positiveRoot a)

/-- The actual negative simple-root map into the generated graph. -/
def negativeHom (a : D.SimpleIndex) : D.negativeGroup a ⟶ D.envelope.group :=
  D.envelope.rootLift a (D.negativeRoot a)

theorem positiveHom_closed (a : D.SimpleIndex) : IsClosedSubgroup (D.positiveHom a) :=
  D.envelope.rootLift_closed a (D.positiveRoot a)

theorem negativeHom_closed (a : D.SimpleIndex) : IsClosedSubgroup (D.negativeHom a) :=
  D.envelope.rootLift_closed a (D.negativeRoot a)

instance positiveGroup_smooth (a : D.SimpleIndex) : Smooth (D.positiveGroup a).X.hom :=
  (D.positiveRoot a).leftSmooth

instance negativeGroup_smooth (a : D.SimpleIndex) : Smooth (D.negativeGroup a).X.hom :=
  (D.negativeRoot a).leftSmooth

instance positiveGroup_connected (a : D.SimpleIndex) :
    ConnectedSpace (D.positiveGroup a).X.left :=
  (D.positiveRoot a).leftConnected

instance negativeGroup_connected (a : D.SimpleIndex) :
    ConnectedSpace (D.negativeGroup a).X.left :=
  (D.negativeRoot a).leftConnected

instance positiveGroup_affine (a : D.SimpleIndex) :
    IsAffineHom (D.positiveGroup a).X.hom :=
  (D.positiveHom_closed a).isAffineHom

instance negativeGroup_affine (a : D.SimpleIndex) :
    IsAffineHom (D.negativeGroup a).X.hom :=
  (D.negativeHom_closed a).isAffineHom

omit [Smooth G₁.X.hom] [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom] in
theorem negative_pairing (a : D.SimpleIndex) :
    latticePairing T (-(a : characterLattice T)) (D.directions.direction a) = 0 := by
  simp only [map_neg, LinearMap.neg_apply, D.directions.annihilates a, neg_zero]

theorem positive_first_rep (a : D.SimpleIndex) :
    (RelativeRoot.subgroup i₁ (a : characterLattice T)).IsRepresentedBy
      (D.positiveHom a ≫ D.envelope.first) :=
  D.envelope.rootLift_first_rep D.split a (D.positiveRoot a) a.2.1.1.1
    (D.directions.annihilates a)

theorem positive_second_rep (a : D.SimpleIndex) :
    (RelativeRoot.subgroup i₂ (a : characterLattice T)).IsRepresentedBy
      (D.positiveHom a ≫ D.envelope.second) :=
  D.envelope.rootLift_second_rep D.split a (D.positiveRoot a) a.2.1.1.1
    (D.directions.annihilates a)

theorem negative_first_rep (a : D.SimpleIndex) :
    (RelativeRoot.subgroup i₁ (-(a : characterLattice T))).IsRepresentedBy
      (D.negativeHom a ≫ D.envelope.first) :=
  D.envelope.rootLift_first_rep D.split a (D.negativeRoot a)
    (neg_ne_zero.mpr a.2.1.1.1) (D.negative_pairing a)

theorem negative_second_rep (a : D.SimpleIndex) :
    (RelativeRoot.subgroup i₂ (-(a : characterLattice T))).IsRepresentedBy
      (D.negativeHom a ≫ D.envelope.second) :=
  D.envelope.rootLift_second_rep D.split a (D.negativeRoot a)
    (neg_ne_zero.mpr a.2.1.1.1) (D.negative_pairing a)

theorem positive_normalized (a : D.SimpleIndex) :
    (SubgroupFunctor.range (D.positiveHom a)).IsNormalizedBy
      (SubgroupFunctor.range D.envelope.torusLift) :=
  D.envelope.range_rootLift_isNormalizedBy a (D.positiveRoot a)

theorem negative_normalized (a : D.SimpleIndex) :
    (SubgroupFunctor.range (D.negativeHom a)).IsNormalizedBy
      (SubgroupFunctor.range D.envelope.torusLift) :=
  D.envelope.range_rootLift_isNormalizedBy a (D.negativeRoot a)

/-- Each positive simple-root map lands in the intrinsic positive dynamic
unipotent subgroup of the graph for the chosen chamber. -/
theorem positive_le_unipotent (a : D.SimpleIndex) :
    SubgroupFunctor.range (D.positiveHom a) ≤
      Dynamic.unipotent
        (CommGroupScheme.groupHom D.directions.chamber ≫ D.envelope.torusLift) :=
  (D.envelope.range_rootLift_le a (D.positiveRoot a)).trans
    (RelativeRoot.subgroup_le_dynamicUnipotent D.envelope.torusLift
      D.directions.chamber a.2.1.2)

/-- Each negative simple-root map lands in the actual opposite dynamic
unipotent subgroup of the graph. -/
theorem negative_le_unipotent (a : D.SimpleIndex) :
    SubgroupFunctor.range (D.negativeHom a) ≤
      Dynamic.unipotent
        (CommGroupScheme.groupHom (-D.directions.chamber) ≫ D.envelope.torusLift) := by
  apply (D.envelope.range_rootLift_le a (D.negativeRoot a)).trans
  apply RelativeRoot.subgroup_le_dynamicUnipotent
  simpa only [map_neg, LinearMap.neg_apply, neg_neg] using a.2.1.2

private theorem postcomp_mem_of_rep {H K L : GroupScheme (Spec (CommRingCat.of k))}
    {f : H ⟶ K} {p : K ⟶ L} {F : SubgroupFunctor L}
    (hF : F.IsRepresentedBy (f ≫ p))
    {W : Over (Spec (CommRingCat.of k))} {x : W ⟶ K.X}
    (hx : x ∈ (SubgroupFunctor.range f).carrier W) :
    x ≫ p.hom.hom ∈ F.carrier W := by
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  rw [← hF.2]
  exact SubgroupFunctor.mem_range.mpr ⟨y, by rw [Grp.comp_hom_hom, Category.assoc]⟩

/-- Distinct positive and negative simple-root lifts commute in the graph,
by checking both ambient projections on every scheme test. -/
theorem commute_positive_negative
    {J₁ : Type v} {J₂ : Type w}
    (P₁ : RootDatum J₁ (characterLattice T) (cocharacterLattice T))
    (P₂ : RootDatum J₂ (characterLattice T) (cocharacterLattice T))
    (hP₁ : IsRootDatumOf i₁ P₁) (hP₂ : IsRootDatumOf i₂ P₂)
    (hroots : roots i₁ = roots i₂)
    (a b : D.SimpleIndex) (hab : a ≠ b)
    {W : Over (Spec (CommRingCat.of k))} {x y : W ⟶ D.envelope.group.X}
    (hx : x ∈ (SubgroupFunctor.range (D.positiveHom a)).carrier W)
    (hy : y ∈ (SubgroupFunctor.range (D.negativeHom b)).carrier W) :
    Commute x y := by
  have hsimp : simpleRelativeRoots i₁ D.directions.chamber =
      simpleRelativeRoots i₂ D.directions.chamber := by
    have hr : relativeRoots i₁ = relativeRoots i₂ := hroots
    unfold simpleRelativeRoots positiveRelativeRoots
    rw [hr]
  let a₂ : simpleRelativeRoots i₂ D.directions.chamber :=
    ⟨a, by rw [← hsimp]; exact a.2⟩
  let b₂ : simpleRelativeRoots i₂ D.directions.chamber :=
    ⟨b, by rw [← hsimp]; exact b.2⟩
  have hab₂ : a₂ ≠ b₂ := by
    intro h
    apply hab
    apply Subtype.ext
    exact congrArg
      (fun z : simpleRelativeRoots i₂ D.directions.chamber => (z : characterLattice T)) h
  have hgeneric₂ : IsGenericCocharacter i₂ D.directions.chamber := by
    intro z hz
    apply D.directions.generic z
    change z ∈ roots i₁
    rw [hroots]
    exact hz
  have hc₁ := commute_simple_opposite i₁ P₁ hP₁ D.directions.chamber D.split
    D.directions.generic a b hab
    (postcomp_mem_of_rep (D.positive_first_rep a) hx)
    (postcomp_mem_of_rep (D.negative_first_rep b) hy)
  have hc₂ := commute_simple_opposite i₂ P₂ hP₂ D.directions.chamber D.split
    hgeneric₂ a₂ b₂ hab₂
    (postcomp_mem_of_rep (D.positive_second_rep a) hx)
    (postcomp_mem_of_rep (D.negative_second_rep b) hy)
  change x * y = y * x
  apply D.envelope.points_ext
  · simpa only [MonObj.mul_comp] using hc₁.eq
  · simpa only [MonObj.mul_comp] using hc₂.eq

end SimpleComparisonGraph

end Langlands.GroupScheme.LeviGluing
