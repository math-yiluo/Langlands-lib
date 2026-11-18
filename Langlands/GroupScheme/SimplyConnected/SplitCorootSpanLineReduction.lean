import Langlands.GroupScheme.SimplyConnected.SplitNecessityAssembly
import Langlands.GroupScheme.Reductive.SplitExistence
import Langlands.GroupScheme.Reductive.SplitSemisimplicity
import Langlands.GroupScheme.Reductive.SplitCentralIsogenyReduction
import Langlands.GroupScheme.Reductive.CentralTorusQuotientProof
import Langlands.GroupScheme.CentralIsogeny.SplitRootDatumProof
import Langlands.GroupScheme.Reductive.SplitRankOneRootCellReduction
import Langlands.GroupScheme.Reductive.SplitIsomorphismCentralizerRootData
import Langlands.GroupScheme.Reductive.SplitLeviGluingFactorInjectivity
import Langlands.GroupScheme.Reductive.SplitRootLieLineStatement

/-! # Integral coroot generation from explicit root-cell and root-line inputs

The necessity half of Milne's coroot criterion (Proposition 23.59) for split groups, assuming
three explicit statements: existence of root data (`RootDatumExistenceStatement`), the rank-one
root cell (`SplitRankOneRootCellStatement`) and one-dimensionality of root spaces
(`SplitRootLieLineStatement`). The Lie-line input replaces the projective-Borel root-tangent
argument in the Levi-gluing step of the common-torus Isomorphism Theorem. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace LeviGluing

variable {k : Type u} [Field k]

section Graph

variable {G₁ G₂ : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G₁.X.hom] [Smooth G₁.X.hom] [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom]
    {i₁ : T.toGrp ⟶ G₁} {i₂ : T.toGrp ⟶ G₂}

namespace SimpleComparisonGraph

variable (D : SimpleComparisonGraph i₁ i₂)

omit [Smooth G₁.X.hom] [Smooth G₂.X.hom] in
/-- Along a simple root `a`, a nonzero weight orthogonal to the direction of `a` has a
weight space in the reductive graph which is a line, by the explicit input `hLine`, and which
contains the nonzero image of the corresponding weight space of the local Levi. A projection
restricting to a monomorphism on that Levi therefore kills no nonzero vector of this weight
space. -/
theorem weightKernelTrivial_of_orthogonal_of_rootLieLine
    (hLine : SplitRootLieLineStatement.{u})
    (hG₁ : IsConnectedReductive G₁) (hmax₁ : IsMaximalTorus i₁)
    (hroots : roots i₁ = roots i₂)
    (hH : IsConnectedReductive D.envelope.group)
    (htmax : IsMaximalTorus D.envelope.torusLift)
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : D.envelope.group ⟶ G) (a : D.SimpleIndex)
    [Mono (D.envelope.localLift a ≫ p).hom.hom]
    {χ : characterLattice T} (hχ0 : χ ≠ 0)
    (hχa : latticePairing T χ (D.directions.direction a) = 0) :
    WeightKernelTrivial p D.envelope.torusLift χ := by
  by_cases hχ : χ ∈ roots D.envelope.torusLift
  swap
  · exact weightKernelTrivial_of_not_mem_roots p _ hχ0 hχ
  have hZ := dynamicCentralizerReductive k G₁ hG₁ _ (D.comparisons a).left
    (D.comparisons a).leftInclusion (D.comparisons a).leftClosed (D.comparisons a).leftRep
  let : IsAffineHom (D.comparisons a).left.X.hom := hZ.isAffineHom
  have hB := dynamicCentralizerRoots k G₁ hG₁ T D.split i₁ hmax₁ (D.directions.direction a)
    (D.comparisons a).left (D.comparisons a).leftInclusion (D.comparisons a).leftClosed
    (D.comparisons a).leftRep hZ (D.comparisons a).leftTorus (D.comparisons a).leftTorusComp
  have hχs : χ ∈ roots (D.comparisons a).leftTorus := by
    rw [hB]
    exact ⟨D.roots_subset_first hroots hχ, hχa⟩
  obtain ⟨Y, hY, hY0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (mem_roots.mp hχs).2
  have hX₀ := lieKernelHomLinear_mem_weightSpace (D.envelope.localLift a)
    (D.comparisons a).leftTorus χ hY
  rw [D.envelope.leftTorus_localLift] at hX₀
  obtain ⟨e⟩ := hLine k D.envelope.group hH T D.split D.envelope.torusLift htmax χ hχ
  have hdim : Module.finrank k (weightSpace D.envelope.torusLift χ) = 1 :=
    e.finrank_eq.symm.trans (Module.finrank_self k)
  apply weightKernelTrivial_of_finrank_eq_one p _ hdim hX₀
  rw [← LinearMap.comp_apply, ← Lie.targetMapLinear_comp]
  intro h
  apply hY0
  apply Lie.targetMapLinear_injective (D.envelope.localLift a ≫ p) (CommRingCat.of k)
  rw [h, map_zero]

/-- Every weight space of the graph torus meets the kernel of the differential of a
projection trivially, when the projection restricts to monomorphisms on the local Levis
and on the torus, given the explicit root-line input `hLine`. Induction over the positive
roots starts at the simple roots and their doubles, which are orthogonal to the directions of
their local Levis, and uses the simple reflections. -/
theorem weightKernelTrivial_of_rootLieLine (hLine : SplitRootLieLineStatement.{u})
    (E : D.GraphDynamicFactors)
    (hG₁ : IsConnectedReductive G₁) (hmax₁ : IsMaximalTorus i₁) {J₁ : Type*}
    {P₁ : RootDatum J₁ (characterLattice T) (cocharacterLattice T)}
    (hP₁ : IsRootDatumOf i₁ P₁) (hroots : roots i₁ = roots i₂)
    (hH : IsConnectedReductive D.envelope.group)
    (htmax : IsMaximalTorus D.envelope.torusLift)
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : D.envelope.group ⟶ G) {i : T.toGrp ⟶ G} (ht : D.envelope.torusLift ≫ p = i)
    [Mono i.hom.hom] (hmono : ∀ a : D.SimpleIndex, Mono (D.envelope.localLift a ≫ p).hom.hom)
    (χ : characterLattice T) : WeightKernelTrivial p D.envelope.torusLift χ := by
  let : IsAffineHom T.toGrp.X.hom := D.split.isAffineHom
  have hQ : ∀ a (ha : a ∈ simpleRelativeRoots i₁ D.directions.chamber)
      (ψ : characterLattice T), latticePairing T ψ D.directions.chamber ≠ 0 →
      latticePairing T ψ (D.directions.direction ⟨a, ha⟩) = 0 →
      WeightKernelTrivial p D.envelope.torusLift ψ := by
    intro a ha ψ hψc hψa
    have : Mono (D.envelope.localLift ⟨a, ha⟩ ≫ p).hom.hom := hmono ⟨a, ha⟩
    refine D.weightKernelTrivial_of_orthogonal_of_rootLieLine hLine hG₁ hmax₁ hroots hH htmax
      p ⟨a, ha⟩ ?_ hψa
    rintro rfl
    exact hψc (by rw [map_zero, LinearMap.zero_apply])
  have hpos := positive_induction hP₁ D.split D.directions.generic
    (fun ψ => WeightKernelTrivial p D.envelope.torusLift ψ ∧
      WeightKernelTrivial p D.envelope.torusLift (-ψ))
    (fun a ha => by
      have hann := D.directions.annihilates ⟨a, ha⟩
      have hc := ha.1.2
      refine ⟨hQ a ha a hc.ne' hann, hQ a ha (-a) ?_ ?_⟩
      · rw [map_neg, LinearMap.neg_apply]
        omega
      · rw [map_neg, LinearMap.neg_apply, hann, neg_zero])
    (fun a ha _ => by
      have hann : latticePairing T a (D.directions.direction ⟨a, ha⟩) = 0 :=
        D.directions.annihilates ⟨a, ha⟩
      have hc := ha.1.2
      refine ⟨hQ a ha (2 • a) ?_ ?_, hQ a ha (-(2 • a)) ?_ ?_⟩
      · rw [two_nsmul, map_add, LinearMap.add_apply]
        omega
      · rw [two_nsmul, map_add, LinearMap.add_apply, hann, add_zero]
      · rw [two_nsmul, map_neg, LinearMap.neg_apply, map_add, LinearMap.add_apply]
        omega
      · rw [two_nsmul, map_neg, LinearMap.neg_apply, map_add, LinearMap.add_apply, hann,
          add_zero, neg_zero])
    (fun j hj ψ hψ => ⟨D.weightKernelTrivial_reflection hP₁ p hj hψ.1, by
      rw [← map_neg]
      exact D.weightKernelTrivial_reflection hP₁ p hj hψ.2⟩)
  by_cases h0 : χ = 0
  · subst h0
    exact weightKernelTrivial_zero p _ ht E.torus_selfCentralizing
  by_cases hχ : χ ∈ roots D.envelope.torusLift
  · have hχ₁ := D.roots_subset_first hroots hχ
    rcases lt_trichotomy 0 (latticePairing T χ D.directions.chamber) with h | h | h
    · exact (hpos χ ⟨hχ₁, h⟩).1
    · exact absurd h.symm (D.directions.generic χ hχ₁)
    · have h' := (hpos (-χ) ⟨neg_mem_roots hP₁ hχ₁, by
        rw [map_neg, LinearMap.neg_apply]
        omega⟩).2
      rwa [neg_neg] at h'
  · exact weightKernelTrivial_of_not_mem_roots p _ h0 hχ

end SimpleComparisonGraph

end Graph

/-- **The graph projections are isomorphisms over an algebraically closed field, from the
root-line input.** The four unipotent factor maps of the graph are faithfully flat; each is an
isomorphism because the corresponding projection is injective on the Lie algebra of the
reductive graph, which is checked one torus weight space at a time using `hLine`. -/
theorem algClosedGraphProjectionIsomorphisms_of_rootLieLine
    (hLine : SplitRootLieLineStatement.{u}) : AlgClosedGraphProjectionIsomorphisms.{u} := by
  intro k _ _ G₁ G₂ hG₁ hG₂ T i₁ i₂ hmax₁ hmax₂
  let := hG₁.isAffineHom
  let := hG₁.smooth
  let := hG₂.isAffineHom
  let := hG₂.smooth
  intro J₁ J₂ P₁ P₂ hP₁ hP₂ hroots D
  let E := D.graphDynamicFactorsOfReductive P₁ P₂ hP₁ hP₂ hroots hG₁ hmax₁
  let F := D.graphFactorProjectionsOfReductive E P₁ P₂ hP₁ hP₂ hroots hG₁ hG₂ hmax₁ hmax₂
  have hH := D.isConnectedReductive P₁ P₂ hP₁ hP₂ hroots hG₁ hG₂ hmax₁ hmax₂
  have htmax := E.isMaximalTorus hmax₁.2.1
  let : IsClosedImmersion i₁.hom.hom.left := hmax₁.2.1
  let : IsClosedImmersion i₂.hom.hom.left := hmax₂.2.1
  let : Mono i₁.hom.hom := Over.mono_of_mono_left _
  let : Mono i₂.hom.hom := Over.mono_of_mono_left _
  have hfirst := D.weightKernelTrivial_of_rootLieLine hLine E hG₁ hmax₁ hP₁ hroots hH htmax
    D.envelope.first D.envelope.torusLift_first (fun a => by
      rw [D.envelope.localLift_first]
      exact (D.comparisons a).leftRep.1)
  have hsecond := D.weightKernelTrivial_of_rootLieLine hLine E hG₁ hmax₁ hP₁ hroots hH htmax
    D.envelope.second D.envelope.torusLift_second (fun a => by
      rw [D.envelope.localLift_second]
      have : IsIso (D.comparisons a).iso.hom.hom.hom :=
        (inferInstance : IsIso ((Grp.forget _).mapIso (D.comparisons a).iso).hom)
      have : Mono (D.comparisons a).rightInclusion.hom.hom := (D.comparisons a).rightRep.1
      change Mono ((D.comparisons a).iso.hom.hom.hom ≫ (D.comparisons a).rightInclusion.hom.hom)
      infer_instance)
  have hinj₁ := eq_one_of_targetMap_eq_one D.envelope.first
    (targetMapLinear_injective_of_weightKernelTrivial D.envelope.first D.envelope.torusLift
      D.split hfirst)
  have hinj₂ := eq_one_of_targetMap_eq_one D.envelope.second
    (targetMapLinear_injective_of_weightKernelTrivial D.envelope.second D.envelope.torusLift
      D.split hsecond)
  have hneg : (Dynamic.unipotent (CommGroupScheme.groupHom (-D.directions.chamber) ≫
      D.envelope.torusLift)).IsRepresentedBy E.negative.inclusion := by
    rw [groupHom_neg_comp_eq_oppositeCocharacter]
    exact E.negativeRep
  have : IsIso F.positiveFirst.hom := UnipotentProjectionData.isIso_of_lieKernel
    D.envelope.torusLift D.envelope.torusLift_first D.directions.chamber hmax₁.2.1
    E.positiveRep F.positiveFirst hinj₁
  have : IsIso F.negativeFirst.hom := UnipotentProjectionData.isIso_of_lieKernel
    D.envelope.torusLift D.envelope.torusLift_first (-D.directions.chamber) hmax₁.2.1
    hneg F.negativeFirst hinj₁
  have : IsIso F.positiveSecond.hom := UnipotentProjectionData.isIso_of_lieKernel
    D.envelope.torusLift D.envelope.torusLift_second D.directions.chamber hmax₂.2.1
    E.positiveRep F.positiveSecond hinj₂
  have : IsIso F.negativeSecond.hom := UnipotentProjectionData.isIso_of_lieKernel
    D.envelope.torusLift D.envelope.torusLift_second (-D.directions.chamber) hmax₂.2.1
    hneg F.negativeSecond hinj₂
  exact ⟨E.isIso_first_of_factorIsomorphisms F hG₁ hmax₁,
    E.isIso_second_of_factorIsomorphisms F hG₂ hmax₂ hroots⟩

end LeviGluing

/-- The three explicit inputs of the integral coroot criterion in this module, at universe
`u`: existence of root data (Milne Theorem 21.11 in the split case), the rank-one root cell
(Conrad, *Reductive group schemes*, Theorem 4.1.4 and Remark 4.2.4) and one-dimensionality of
root spaces (Milne Theorem 21.11(a)). -/
def SplitCorootSpanLineInputs : Prop :=
  RootDatumExistenceStatement.{u} ∧ SplitRankOneRootCellStatement.{u} ∧
    SplitRootLieLineStatement.{u}

/-- **Isomorphism Theorem for a common split maximal torus, from explicit inputs.** The
rank-one case comes from the root cell and the gluing step from the root-line input. -/
theorem splitCommonTorusIsomorphism_of_rootCell_of_rootLieLine
    (hCell : SplitRankOneRootCellStatement.{u}) (hLine : SplitRootLieLineStatement.{u}) :
    SplitCommonTorusIsomorphismStatement.{u} :=
  splitCommonTorusIsomorphism_of_rankOne_of_leviGluing
    (splitRankOneCommonTorusIsomorphism_of_rootCell hCell)
    (LeviGluing.splitCommonTorusLeviGluing_of_algClosedGraphs
      (LeviGluing.algClosedGraphProjectionIsomorphisms_of_rootLieLine hLine))

/-- **Central Isogeny Theorem from explicit inputs** (Milne Theorem 23.9, existence half,
central case). -/
theorem splitCentralIsogenyExistence_of_corootSpanLineInputs
    (h : SplitCorootSpanLineInputs.{u}) : SplitCentralIsogenyExistenceStatement.{u} :=
  splitCentralIsogenyExistence_of_commonTorusIsomorphism h.1 centralIsogenyRootDatumHom
    splitCentralTorusQuotient (splitCommonTorusIsomorphism_of_rootCell_of_rootLieLine h.2.1 h.2.2)

/-- **Simple connectedness forces integral coroot generation, from explicit inputs** (Milne,
*Algebraic Groups*, Proposition 23.59, necessity, split case). -/
theorem splitSimplyConnectedCorootSpan_of_corootSpanLineInputs
    (h : SplitCorootSpanLineInputs.{u}) : SplitSimplyConnectedCorootSpanStatement.{u} :=
  splitSimplyConnectedCorootSpan_of_inputs
    ⟨splitReductiveExistence, splitCentralIsogenyExistence_of_corootSpanLineInputs h,
      splitSemisimpleRootDatum⟩

end Langlands.GroupScheme
