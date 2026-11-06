import Langlands.GroupScheme.Reductive.SplitLeviGluingRankOneFactors
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.Absolute.AlgClosedMaximalTorusCentralizerAssembly
import Langlands.GroupScheme.Torus.NoTorusUnipotent
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof

/-! # Local root cells and equal-index rational closure in the actual graph -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme.LeviGluing

variable {k : Type u} [Field k]

section RationalClosure

variable {K H M Z A : GroupScheme (Spec (CommRingCat.of k))}

/-- Continuity transports rational-point closure between different actual
group schemes; the morphism need not preserve the group law. -/
theorem postcomp_mem_rationalPointClosure
    {S : Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ K.X)}
    {S' : Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)}
    (φ : K.X ⟶ H.X)
    (hφ : ∀ s ∈ S, s ≫ φ ∈ rationalPointClosure H S')
    {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ K.X}
    (hx : x ∈ rationalPointClosure K S) :
    x ≫ φ ∈ rationalPointClosure H S' := by
  have himage : φ.left '' rationalPointImage K S ⊆ closure (rationalPointImage H S') := by
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact hφ s hs
  have h := image_closure_subset_closure_image φ.left.continuous ⟨_, hx, rfl⟩
  change φ.left (x.left (IsLocalRing.closedPoint k)) ∈ closure (rationalPointImage H S')
  exact closure_minimal himage isClosed_closure h

/-- A homomorphism carries the literal rational three-factor products to the
literal products of the three composite maps. -/
theorem postcomp_mem_rationalTripleProduct
    (m : M ⟶ K) (z : Z ⟶ K) (a : A ⟶ K) (f : K ⟶ H)
    {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ K.X}
    (hx : x ∈ rationalTripleProduct m z a) :
    x ≫ f.hom.hom ∈ rationalTripleProduct (m ≫ f) (z ≫ f) (a ≫ f) := by
  rcases hx with ⟨w, ⟨y, hy, t, ht, rfl⟩, q, hq, rfl⟩
  rw [MonObj.mul_comp, MonObj.mul_comp]
  apply Set.mul_mem_mul
  · apply Set.mul_mem_mul
    · obtain ⟨b, rfl⟩ := SubgroupFunctor.mem_range.mp hy
      exact SubgroupFunctor.mem_range.mpr ⟨b, by rw [Grp.comp_hom_hom, Category.assoc]⟩
    · obtain ⟨b, rfl⟩ := SubgroupFunctor.mem_range.mp ht
      exact SubgroupFunctor.mem_range.mpr ⟨b, by rw [Grp.comp_hom_hom, Category.assoc]⟩
  · obtain ⟨b, rfl⟩ := SubgroupFunctor.mem_range.mp hq
    exact SubgroupFunctor.mem_range.mpr ⟨b, by rw [Grp.comp_hom_hom, Category.assoc]⟩

end RationalClosure

variable {G₁ G₂ : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G₁.X.hom] [Smooth G₁.X.hom]
    [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom]
    {i₁ : T.toGrp ⟶ G₁} {i₂ : T.toGrp ⟶ G₂}
    (D : SimpleComparisonGraph i₁ i₂)

namespace SimpleComparisonGraph

namespace RankOneRootCell

variable [ConnectedSpace G₁.X.left]
    {D} {a : D.SimpleIndex} (E : D.RankOneRootCell a)

/-- Every rational point in the image of the local Levi lies in the graph
closure of its actual three-factor root cell. -/
theorem range_localLift_subset_rationalPointClosure [IsAlgClosed k] :
    ((SubgroupFunctor.range (D.envelope.localLift a)).carrier (Over.mk (𝟙 _)) :
      Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ D.envelope.group.X)) ⊆
      rationalPointClosure D.envelope.group
        (rationalTripleProduct (D.negativeHom a) (E.middleHom ≫ D.envelope.localLift a)
          (D.positiveHom a)) := by
  intro x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have hy : y ∈ rationalPointClosure (D.comparisons a).left
      (rationalTripleProduct (D.negativeRoot a).leftInclusion E.middleHom
        (D.positiveRoot a).leftInclusion) := by
    rw [E.rationalPointClosure_cell_eq_univ]
    exact Set.mem_univ _
  apply postcomp_mem_rationalPointClosure (D.envelope.localLift a).hom.hom _ hy
  intro s hs
  apply subset_rationalPointClosure
  exact postcomp_mem_rationalTripleProduct (D.negativeRoot a).leftInclusion E.middleHom
    (D.positiveRoot a).leftInclusion (D.envelope.localLift a) hs

end RankOneRootCell

variable (hi₁ : IsClosedSubgroup i₁)
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom D.directions.chamber ≫ i₁) =
      SubgroupFunctor.range i₁)

omit [Smooth G₁.X.hom] [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom] in
include hZ hi₁ in
/-- The ambient chamber-centralizer identity identifies the entire local
middle factor with the common torus, on all scheme tests. -/
theorem local_torus_rep (a : D.SimpleIndex) :
    (Dynamic.centralizer (CommGroupScheme.groupHom D.directions.chamber ≫
      (D.comparisons a).leftTorus)).IsRepresentedBy (D.comparisons a).leftTorus := by
  have htclosed := (D.comparisons a).leftTorus_closed hi₁
  let : IsClosedImmersion (D.comparisons a).leftTorus.hom.hom.left := htclosed
  let : Mono (D.comparisons a).leftTorus.hom.hom := Over.mono_of_mono_left _
  let : Mono (D.comparisons a).leftInclusion.hom.hom := (D.comparisons a).leftRep.1
  refine ⟨inferInstance, ?_⟩
  rw [Dynamic.centralizer_eq_comap_of_mono
    (CommGroupScheme.groupHom D.directions.chamber ≫ (D.comparisons a).leftTorus)
      (D.comparisons a).leftInclusion,
    Category.assoc, (D.comparisons a).leftTorusComp, hZ]
  apply SubgroupFunctor.ext
  intro W
  apply Subgroup.ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    apply SubgroupFunctor.mem_comap.mpr
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨y, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, (D.comparisons a).leftTorusComp]
  · intro hx
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp (SubgroupFunctor.mem_comap.mp hx)
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨y, (cancel_mono (D.comparisons a).leftInclusion.hom.hom).mp ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, (D.comparisons a).leftTorusComp]
    exact hy

variable [ConnectedSpace G₁.X.left]
    {J₁ : Type v}
    (P₁ : RootDatum J₁ (characterLattice T) (cocharacterLattice T))
    (hP₁ : IsRootDatumOf i₁ P₁)

/-- Construct the actual local root cell with the common torus as its middle,
assuming the explicitly displayed ambient chamber-centralizer identity. -/
def torusRankOneRootCell (a : D.SimpleIndex) : D.RankOneRootCell a where
  middle := T.toGrp
  middleHom := (D.comparisons a).leftTorus
  middleClosed := (D.comparisons a).leftTorus_closed hi₁
  middleRep := D.local_torus_rep hi₁ hZ a
  negativeRep := D.local_negative_rep P₁ hP₁ a
  positiveRep := D.local_positive_rep P₁ hP₁ a

include hi₁ hZ hP₁ in
/-- The equal-index root-product closure condition in the actual graph. -/
theorem positive_mul_negative_subset_rationalPointClosure [IsAlgClosed k] (a : D.SimpleIndex) :
    (((SubgroupFunctor.range (D.positiveHom a)).carrier (Over.mk (𝟙 _)) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ D.envelope.group.X)) *
      ((SubgroupFunctor.range (D.negativeHom a)).carrier (Over.mk (𝟙 _)) : Set _)) ⊆
      rationalPointClosure D.envelope.group
        (rationalTripleProduct (D.negativeHom a) D.envelope.torusLift (D.positiveHom a)) := by
  have hclosure := (D.torusRankOneRootCell hi₁ hZ P₁ hP₁ a).range_localLift_subset_rationalPointClosure
  change _ ⊆ rationalPointClosure D.envelope.group
    (rationalTripleProduct (D.negativeHom a)
      ((D.comparisons a).leftTorus ≫ D.envelope.localLift a) (D.positiveHom a)) at hclosure
  rw [D.envelope.leftTorus_localLift] at hclosure
  rintro x ⟨y, hy, z, hz, rfl⟩
  apply hclosure
  exact ((SubgroupFunctor.range (D.envelope.localLift a)).carrier _).mul_mem
    (SubgroupFunctor.range_comp_le (D.positiveRoot a).leftInclusion
      (D.envelope.localLift a) _ hy)
    (SubgroupFunctor.range_comp_le (D.negativeRoot a).leftInclusion
      (D.envelope.localLift a) _ hz)

variable (hcent : DynamicCentralizerReductiveStatement.{u})
    (hG₁ : IsConnectedReductive G₁) (hmax₁ : IsMaximalTorus i₁)

omit [ConnectedSpace G₁.X.left] [Smooth G₁.X.hom]
  [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom] in
include hcent hG₁ hmax₁ in
/-- The single remaining structural input suffices for the ambient identity:
no-torus unipotence, solvable torus quotients and generic centralizers are
already published unconditional theorems. -/
theorem chamber_centralizer_eq_range_of_reductiveCentralizers :
    Dynamic.centralizer (CommGroupScheme.groupHom D.directions.chamber ≫ i₁) =
      SubgroupFunctor.range i₁ := by
  have hself := maximalTorusCentralizer_of_structuralInputs hcent noTorusUnipotent
    solvableTorusQuotient k G₁ hG₁ T i₁ hmax₁
  exact (genericCentralizer k G₁ hG₁ T i₁ (hmax₁.isMaximalSplitTorus D.split)
    D.directions.chamber D.directions.generic).trans hself

/-- Construct the torus-middle local root cell from the existing structural
centralizer-reductivity proposition, with all other structural inputs proved. -/
def torusRankOneRootCellOfCentralizerReductivity (a : D.SimpleIndex) : D.RankOneRootCell a :=
  D.torusRankOneRootCell hmax₁.2.1
    (D.chamber_centralizer_eq_range_of_reductiveCentralizers hcent hG₁ hmax₁) P₁ hP₁ a

include hcent hG₁ hmax₁ hP₁ in
/-- The same-index graph closure follows from the explicitly retained
centralizer-reductivity input. -/
theorem positive_mul_negative_subset_closure_of_reductiveCentralizers
    [IsAlgClosed k] (a : D.SimpleIndex) :
    (((SubgroupFunctor.range (D.positiveHom a)).carrier (Over.mk (𝟙 _)) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ D.envelope.group.X)) *
      ((SubgroupFunctor.range (D.negativeHom a)).carrier (Over.mk (𝟙 _)) : Set _)) ⊆
      rationalPointClosure D.envelope.group
        (rationalTripleProduct (D.negativeHom a) D.envelope.torusLift (D.positiveHom a)) :=
  D.positive_mul_negative_subset_rationalPointClosure hmax₁.2.1
    (D.chamber_centralizer_eq_range_of_reductiveCentralizers hcent hG₁ hmax₁) P₁ hP₁ a

end SimpleComparisonGraph

end Langlands.GroupScheme.LeviGluing
