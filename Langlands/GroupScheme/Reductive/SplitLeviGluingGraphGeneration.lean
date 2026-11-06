import Langlands.GroupScheme.Reductive.SplitLeviGluingRankOneGraphClosure
import Langlands.GroupScheme.Reductive.SplitLeviGluingGeneratedDensity
import Langlands.GroupScheme.Cartan.Induction

/-! # Actual simple-root and torus generation of the constructed graph -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LeviGluing

variable {k : Type u} [Field k]

section CellFactorization

variable {K H M Z A Q : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth K.X.hom] [IsAffineHom K.X.hom] [ConnectedSpace K.X.left]

/-- A homomorphism out of a smooth connected affine group factors through an
arbitrary closed subgroup when all three actual dynamic factors do so. -/
theorem factorsThrough_of_contains_tripleCellImages
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ K)
    {m : M ⟶ K} {z : Z ⟶ K} {a : A ⟶ K}
    (hm : (Dynamic.unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ)).IsRepresentedBy m)
    (hz : (Dynamic.centralizer χ).IsRepresentedBy z)
    (ha : (Dynamic.unipotent χ).IsRepresentedBy a)
    (f : K ⟶ H) (q : Q ⟶ H) (hq : IsClosedSubgroup q)
    (hM : SubgroupFunctor.range (m ≫ f) ≤ SubgroupFunctor.range q)
    (hZ : SubgroupFunctor.range (z ≫ f) ≤ SubgroupFunctor.range q)
    (hA : SubgroupFunctor.range (a ≫ f) ≤ SubgroupFunctor.range q) :
    FactorsThrough f.hom.hom q := by
  let : IsReduced K.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k _ K.X.hom
  apply factorsThrough_of_range_subset hq
  let c := Dynamic.tripleCellMultiplication m z a
  have : IsDominant c.left := Dynamic.isDominant_tripleCellMultiplication χ hm hz ha
  have hc := Dynamic.tripleCellMultiplication_mem (m ≫ f) (z ≫ f) (a ≫ f)
    (SubgroupFunctor.range q) hM hZ hA
  obtain ⟨b, hb⟩ := SubgroupFunctor.mem_range.mp hc
  have hcomp : b ≫ q.hom.hom = c ≫ f.hom.hom := by
    rw [Dynamic.tripleCellMultiplication_comp_hom]
    exact hb
  have himage : f.hom.hom.left '' Set.range c.left ⊆ Set.range q.hom.hom.left := by
    rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    refine ⟨b.left w, ?_⟩
    exact congrArg (fun l => l.left w) hcomp
  let : IsClosedImmersion q.hom.hom.left := hq
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ closure (Set.range c.left) := c.left.denseRange x
  exact closure_minimal himage q.hom.hom.left.isClosedEmbedding.isClosed_range
    (image_closure_subset_closure_image f.hom.hom.left.continuous ⟨x, hx, rfl⟩)

end CellFactorization

namespace GraphEnvelope

variable {G₁ G₂ T : GroupScheme (Spec (CommRingCat.of k))}
    {I : Type v} {A : I → GroupScheme (Spec (CommRingCat.of k))}
    {a₁ : ∀ j, A j ⟶ G₁} {a₂ : ∀ j, A j ⟶ G₂}
    {i₁ : T ⟶ G₁} {i₂ : T ⟶ G₂}
    (D : GraphEnvelope A a₁ a₂ i₁ i₂)

/-- The local and torus lifts generate the graph as its own ambient group. -/
theorem isGeneratedByLifts :
    IsGeneratedByFamily (graphSources (T := T) A) D.generatorLift (𝟙 D.group) := by
  refine ⟨?_, ?_, ?_⟩
  · change IsClosedImmersion (𝟙 D.group.X.left)
    infer_instance
  · intro j
    exact ⟨(D.generatorLift j).hom.hom, by simp⟩
  · intro Q q hq hfamily
    have hsub : SubgroupFunctor.range D.inclusion ≤
        SubgroupFunctor.range (q ≫ D.inclusion) := by
      apply D.generated.2.2 Q (q ≫ D.inclusion) (hq.comp D.closed)
      intro j
      obtain ⟨b, hb⟩ := hfamily j
      refine ⟨b, ?_⟩
      rw [Grp.comp_hom_hom, ← Category.assoc, hb, ← Grp.comp_hom_hom,
        D.generatorLift_comp]
    intro W x _
    have hx : x ≫ D.inclusion.hom.hom ∈ (SubgroupFunctor.range D.inclusion).carrier W :=
      SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp (hsub W hx)
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨y, D.represents.1.right_cancellation _ _ ?_⟩
    simpa only [Grp.comp_hom_hom, Category.assoc] using hy

end GraphEnvelope

variable {G₁ G₂ : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G₁.X.hom] [Smooth G₁.X.hom]
    [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom]
    {i₁ : T.toGrp ⟶ G₁} {i₂ : T.toGrp ⟶ G₂}
    (D : SimpleComparisonGraph i₁ i₂)

namespace SimpleComparisonGraph

/-- Actual sources: the common torus and both simple-root families, including
an explicit torus source when the simple-root index is empty. -/
abbrev rootFamilySources : Option (Sum D.SimpleIndex D.SimpleIndex) →
    GroupScheme (Spec (CommRingCat.of k))
  | none => T.toGrp
  | some (.inl a) => D.positiveGroup a
  | some (.inr a) => D.negativeGroup a

/-- The actual torus and positive/negative simple-root maps into the graph. -/
def rootFamilyMaps : ∀ j, D.rootFamilySources j ⟶ D.envelope.group
  | none => D.envelope.torusLift
  | some (.inl a) => D.positiveHom a
  | some (.inr a) => D.negativeHom a

theorem rootFamily_geometry (j : Option (Sum D.SimpleIndex D.SimpleIndex)) :
    Smooth (D.rootFamilySources j).X.hom ∧ IsAffineHom (D.rootFamilySources j).X.hom ∧
      ConnectedSpace (D.rootFamilySources j).X.left := by
  rcases j with _ | (a | a)
  · exact ⟨D.split.smooth, D.split.isAffineHom, D.split.connectedSpace⟩
  · exact ⟨inferInstance, inferInstance, inferInstance⟩
  · exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The actual rational subgroup generated by the two simple-root families
and the common torus in the graph. -/
def rootFamilyRationalPoints :
    Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ D.envelope.group.X) :=
  generatedRationalPoints D.envelope.group D.rootFamilySources D.rootFamilyMaps

variable [ConnectedSpace G₁.X.left]
    (hi₁ : IsClosedSubgroup i₁)
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom D.directions.chamber ≫ i₁) =
      SubgroupFunctor.range i₁)
    {J₁ : Type v}
    (P₁ : RootDatum J₁ (characterLattice T) (cocharacterLattice T))
    (hP₁ : IsRootDatumOf i₁ P₁)

include hi₁ hZ hP₁ in
/-- The actual simple-root groups and the torus generate the graph as an
algebraic closed subgroup, even over a nonclosed or imperfect field. -/
theorem isGeneratedByRootFamily :
    IsGeneratedByFamily D.rootFamilySources D.rootFamilyMaps (𝟙 D.envelope.group) := by
  refine ⟨?_, ?_, ?_⟩
  · change IsClosedImmersion (𝟙 D.envelope.group.X.left)
    infer_instance
  · intro j
    exact ⟨(D.rootFamilyMaps j).hom.hom, by simp⟩
  · intro Q q hq hfamily
    apply D.envelope.isGeneratedByLifts.2.2 Q q hq
    rintro (_ | a)
    · exact hfamily none
    · change FactorsThrough (D.envelope.localLift a).hom.hom q
      let E := D.torusRankOneRootCell hi₁ hZ P₁ hP₁ a
      apply factorsThrough_of_contains_tripleCellImages
        (CommGroupScheme.groupHom D.directions.chamber ≫ (D.comparisons a).leftTorus)
        E.negativeRep E.middleRep E.positiveRep (D.envelope.localLift a) q hq
      · exact (factorsThrough_hom_iff_range_le _ _).1 (hfamily (some (.inr a)))
      · change SubgroupFunctor.range
          ((D.comparisons a).leftTorus ≫ D.envelope.localLift a) ≤ SubgroupFunctor.range q
        rw [D.envelope.leftTorus_localLift]
        exact (factorsThrough_hom_iff_range_le _ _).1 (hfamily none)
      · exact (factorsThrough_hom_iff_range_le _ _).1 (hfamily (some (.inl a)))

include hi₁ hZ hP₁ in
/-- Over an algebraically closed field, the actual generated simple-root and
torus rational subgroup has dense locations in the graph. -/
theorem dense_rootFamilyRationalPoints [IsAlgClosed k] :
    Dense (rationalPointImage D.envelope.group (D.rootFamilyRationalPoints : Set _)) :=
  dense_rationalPointImage_closure_of_isGeneratedByFamily D.rootFamily_geometry
    (D.isGeneratedByRootFamily hi₁ hZ P₁ hP₁)

variable (hcent : DynamicCentralizerReductiveStatement.{u})
    (hG₁ : IsConnectedReductive G₁) (hmax₁ : IsMaximalTorus i₁)

include hcent hG₁ hmax₁ hP₁ in
/-- The generation theorem with only the explicitly retained structural
centralizer-reductivity proposition in place of the chamber identity. -/
theorem isGeneratedByRootFamily_of_reductiveCentralizers :
    IsGeneratedByFamily D.rootFamilySources D.rootFamilyMaps (𝟙 D.envelope.group) :=
  D.isGeneratedByRootFamily hmax₁.2.1
    (D.chamber_centralizer_eq_range_of_reductiveCentralizers hcent hG₁ hmax₁) P₁ hP₁

include hcent hG₁ hmax₁ hP₁ in
/-- The dense generated rational subgroup with that same explicit structural
input; no additional generation premise is assumed. -/
theorem dense_rootFamilyRationalPoints_of_reductiveCentralizers [IsAlgClosed k] :
    Dense (rationalPointImage D.envelope.group (D.rootFamilyRationalPoints : Set _)) :=
  D.dense_rootFamilyRationalPoints hmax₁.2.1
    (D.chamber_centralizer_eq_range_of_reductiveCentralizers hcent hG₁ hmax₁) P₁ hP₁

end SimpleComparisonGraph

end Langlands.GroupScheme.LeviGluing
