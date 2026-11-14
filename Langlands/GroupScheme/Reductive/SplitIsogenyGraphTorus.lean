import Langlands.GroupScheme.Reductive.SplitIsogenyGraphDynamicFactors
import Langlands.GroupScheme.Reductive.SplitLeviGluingSimpleGeneration
import Langlands.GroupScheme.Dynamic.CentralizerRootsProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Rational.RootFactorPairTransport
import Langlands.GroupScheme.Reductive.RootReducednessProof
import Langlands.GroupScheme.Lie.Functoriality
import Langlands.GroupScheme.Torus.WeightRestriction

/-! # The source torus and roots of a local-isogeny graph -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RootDatumIsogenyRealization

open LeviGluing

variable {k : Type u} [Field k]
    {G G' : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    [IsAffineHom G'.X.hom] [Smooth G'.X.hom]
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'} {t : T ⟶ T'}
    (D : SimpleIsogenyGraph i i' t)

namespace SimpleIsogenyGraph

omit [Smooth G.X.hom] [Smooth G'.X.hom] in
/-- Every nonzero graph adjoint weight occurs in at least one ambient group.
The two actual projections jointly detect tangent vectors on the dual-number test. -/
theorem roots_subset_union : roots D.envelope.torusLift ⊆ roots i ∪ roots (CommGroupScheme.groupHom t ≫ i') := by
  intro α hα
  by_contra h
  have hnot : α ∉ roots i ∧ α ∉ roots (CommGroupScheme.groupHom t ≫ i') := not_or.mp h
  have hb₁ : weightSpace i α = ⊥ := by
    by_contra hb
    exact hnot.1 ⟨hα.1, hb⟩
  have hb₂ : weightSpace (CommGroupScheme.groupHom t ≫ i') α = ⊥ := by
    by_contra hb
    exact hnot.2 ⟨hα.1, hb⟩
  apply hα.2
  apply eq_bot_iff.mpr
  intro X hX
  rw [Submodule.mem_bot]
  have h₁ := lieKernelHomLinear_mem_weightSpace D.envelope.first D.envelope.torusLift α hX
  have h₂ := lieKernelHomLinear_mem_weightSpace D.envelope.second D.envelope.torusLift α hX
  rw [D.envelope.torusLift_first, hb₁, Submodule.mem_bot] at h₁
  rw [D.envelope.torusLift_second, hb₂, Submodule.mem_bot] at h₂
  apply Additive.toMul.injective
  apply Subtype.ext
  change X.toMul.val = (1 : _ ⟶ D.envelope.group.X)
  apply D.envelope.points_ext
  · rw [MonObj.one_comp]
    exact congrArg (fun Z : Additive (lieKernel G (CommRingCat.of k)) => Z.toMul.val) h₁
  · rw [MonObj.one_comp]
    exact congrArg (fun Z : Additive (lieKernel G' (CommRingCat.of k)) => Z.toMul.val) h₂

section SourceRoots

variable (hG : IsConnectedReductive G) (hmax : IsMaximalTorus i)

omit [Smooth G.X.hom] [Smooth G'.X.hom] in
include hG hmax in
/-- A source root orthogonal to a local direction is an actual graph root. -/
theorem mem_roots_of_orthogonal (a : D.SimpleIndex)
    {χ : characterLattice T} (hχ : χ ∈ roots i)
    (hχa : latticePairing T χ (D.directions.direction a) = 0) :
    χ ∈ roots D.envelope.torusLift := by
  have hZ := dynamicCentralizerReductive k G hG _ (D.comparisons a).left
    (D.comparisons a).leftInclusion (D.comparisons a).leftClosed (D.comparisons a).leftRep
  have hB := dynamicCentralizerRoots k G hG T D.split i hmax (D.directions.direction a)
    (D.comparisons a).left (D.comparisons a).leftInclusion (D.comparisons a).leftClosed
    (D.comparisons a).leftRep hZ (D.comparisons a).leftTorus (D.comparisons a).leftTorusComp
  have hlocal : χ ∈ roots (D.comparisons a).leftTorus := by
    rw [hB]
    exact ⟨hχ, hχa⟩
  let : IsClosedImmersion (D.envelope.localLift a).hom.hom.left :=
    D.envelope.localLift_closed a (D.comparisons a).leftClosed
  let : Mono (D.envelope.localLift a).hom.hom := Over.mono_of_mono_left _
  have h := roots_subset_comp (D.envelope.localLift a) (D.comparisons a).leftTorus hlocal
  rwa [D.envelope.leftTorus_localLift] at h

variable {J : Type u} {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf i P)

omit [Smooth G.X.hom] [IsAffineHom G'.X.hom] [Smooth G'.X.hom] in
include hP in
/-- Source simple reflections are realized in the graph and preserve its roots. -/
theorem reflection_mem_graph_roots {j : J}
    (hj : P.root j ∈ simpleRelativeRoots i D.directions.chamber)
    {χ : characterLattice T} (hχ : χ ∈ roots D.envelope.torusLift) :
    P.reflection j χ ∈ roots D.envelope.torusLift := by
  let a : D.SimpleIndex := ⟨P.root j, hj⟩
  obtain ⟨n, σ, hn, hσ⟩ := hP.2.2 j
  have hfix := cocharacter_comp_eq_of_reflection hP hσ (D.directions.annihilates a)
  have hmem := constantPoint_mem_centralizer hn hfix (Over.mk (𝟙 (Spec (CommRingCat.of k))))
  rw [constantPoint_self, ← (D.comparisons a).leftRep.2] at hmem
  obtain ⟨m, hm⟩ := SubgroupFunctor.mem_range.1 hmem
  have : Mono (D.comparisons a).leftInclusion.hom.hom := (D.comparisons a).leftRep.1
  have hm' : IsNormalizingPoint (D.comparisons a).leftTorus m σ := by
    apply IsNormalizingPoint.of_comp (D.comparisons a).leftInclusion
    rw [(D.comparisons a).leftTorusComp, hm]
    exact hn
  have hn' := hm'.comp (D.envelope.localLift a)
  rw [D.envelope.leftTorus_localLift] at hn'
  have heq : σ.inv ≫ χ = P.reflection j χ := by
    rw [← characterAut_apply, hσ]
  rw [← heq]
  refine ⟨?_, ?_⟩
  · rw [heq]
    intro hz
    have hz' := congrArg (P.reflection j) hz
    rw [P.reflection_same, map_zero] at hz'
    exact hχ.1 hz'
  · exact fun hbot => hχ.2 ((weightSpace_eq_bot_iff_of_isNormalizingPoint hn' χ).mp hbot)

omit [Smooth G'.X.hom] in
include hG hmax hP in
/-- Every source root occurs in the graph: lift simple roots from the local
centralizers and use their actual normalizer reflections. -/
theorem source_roots_subset [P.IsReduced] : roots i ⊆ roots D.envelope.torusLift := by
  let : IsAddTorsionFree (characterLattice T) := isAddTorsionFree_of_rootDatum P
  have hpos := positive_induction hP D.split D.directions.generic
    (fun ψ => (ψ ∈ roots i → ψ ∈ roots D.envelope.torusLift) ∧
      (-ψ ∈ roots i → -ψ ∈ roots D.envelope.torusLift))
    (fun a ha => by
      refine ⟨fun h => D.mem_roots_of_orthogonal hG hmax ⟨a, ha⟩ h
        (D.directions.annihilates ⟨a, ha⟩), fun h => ?_⟩
      exact D.mem_roots_of_orthogonal hG hmax ⟨a, ha⟩ h (D.negative_pairing ⟨a, ha⟩))
    (fun a ha _ => by
      have hnot : 2 • a ∉ roots i := by
        obtain ⟨j, rfl⟩ := exists_root_eq hP ha.1.1
        rw [← hP.2.1]
        exact P.nsmul_notMem_range_root
      exact ⟨fun h => (hnot h).elim, fun h => (hnot (by
        simpa only [neg_neg] using neg_mem_roots hP h)).elim⟩)
    (fun j hj ψ hψ => by
      refine ⟨fun h => D.reflection_mem_graph_roots hP hj (hψ.1 ?_), fun h => ?_⟩
      · simpa only [P.reflection_same] using reflection_mem_roots hP j h
      · rw [← map_neg]
        apply D.reflection_mem_graph_roots hP hj
        apply hψ.2
        have h' := reflection_mem_roots hP j h
        simpa only [map_neg, P.reflection_same] using h')
  intro χ hχ
  rcases lt_trichotomy 0 (latticePairing T χ D.directions.chamber) with h | h | h
  · exact (hpos χ ⟨hχ, h⟩).1 hχ
  · exact (D.directions.generic χ hχ h.symm).elim
  · have hneg := neg_mem_roots hP hχ
    have h' := (hpos (-χ) ⟨hneg, by rw [map_neg, LinearMap.neg_apply]; omega⟩).2
    simpa only [neg_neg] using h' (by simpa only [neg_neg] using hχ)

end SourceRoots

section IsogenyRoots

variable {J J' : Type u} [Finite J] [Finite J']
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (P' : RootDatum J' (characterLattice T') (cocharacterLattice T'))
    [Module.Finite ℤ (characterLattice T)] [Module.Finite ℤ (cocharacterLattice T)]
    [Module.Finite ℤ (characterLattice T')] [Module.Finite ℤ (cocharacterLattice T')]
    [P.IsReduced] [P'.IsReduced]
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P')
    (hT' : IsSplitTorus T'.toGrp) {p : ℕ}
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p P' P)
    (hw : ∀ χ : characterLattice T', t ≫ χ = f.weightMap χ)

omit [Smooth G.X.hom] in
include D hP' hT' hw in
/-- Restricted target roots are prescribed positive integral multiples of source roots. -/
theorem restricted_root_multiple {χ : characterLattice T}
    (hχ : χ ∈ roots (CommGroupScheme.groupHom t ≫ i')) :
    ∃ j : J', χ = f.rootFactor j • P.root (f.indexEquiv j) := by
  obtain ⟨_, ψ, hψ, hψχ⟩ := (mem_roots_comp_iff hT' D.split t i' χ).mp hχ
  rw [← hP'.2.1] at hψ
  obtain ⟨j, rfl⟩ := hψ
  exact ⟨j, by simpa only [hw, f.root_weightMap, natCast_zsmul] using hψχ.symm⟩

include hP hP' hT' hw in
/-- Reductivity excludes extra roots along the source-root rays. -/
theorem roots_eq_source (hG : IsConnectedReductive G) (hmax : IsMaximalTorus i)
    (hH : IsConnectedReductive D.envelope.group)
    (htmax : IsMaximalTorus D.envelope.torusLift) :
    roots D.envelope.torusLift = roots i := by
  have hle := D.source_roots_subset hG hmax hP
  apply Set.Subset.antisymm _ hle
  intro χ hχ
  rcases D.roots_subset_union hχ with h | h
  · exact h
  · obtain ⟨j, hj⟩ := D.restricted_root_multiple P P' hP' hT' f hw h
    have hβ : P.root (f.indexEquiv j) ∈ roots i := by
      rw [← hP.2.1]
      exact ⟨f.indexEquiv j, rfl⟩
    have hdep : ¬ LinearIndependent ℤ ![χ, P.root (f.indexEquiv j)] := by
      rw [hj]
      intro hind
      have hzero := (LinearIndependent.pair_iff.mp hind 1 (-(f.rootFactor j : ℤ))
        (by simp only [one_smul, neg_smul, natCast_zsmul, add_neg_cancel])).1
      exact one_ne_zero hzero
    rcases rootReducedness k D.envelope.group hH T D.split D.envelope.torusLift
        htmax χ hχ _ (hle hβ) hdep with heq | heq
    · exact heq ▸ hβ
    · exact heq ▸ neg_mem_roots hP hβ

/-- Full factors together with maximality, chamber genericity and the exact
source-root set for the graph torus. -/
structure GraphTorusGeometry where
  factors : D.GraphDynamicFactors
  maximal : IsMaximalTorus D.envelope.torusLift
  generic : IsGenericCocharacter D.envelope.torusLift D.directions.chamber
  roots_eq : roots D.envelope.torusLift = roots i

/-- Construct graph torus geometry, retaining graph reductivity as an explicit
input until target coverage is supplied. -/
def graphTorusGeometryOfReductive [IsAlgClosed k]
    (hG : IsConnectedReductive G) (hmax : IsMaximalTorus i)
    (hH : IsConnectedReductive D.envelope.group) : D.GraphTorusGeometry := by
  let E := D.graphDynamicFactorsOfReductive P P' hP hP' hT' f hw hG hmax
  have htmax := E.isMaximalTorus hmax.2.1
  have hroots := D.roots_eq_source P P' hP hP' hT' f hw hG hmax hH htmax
  exact ⟨E, htmax, fun χ hχ => D.directions.generic χ (by change χ ∈ roots i; rw [← hroots]; exact hχ), hroots⟩

end IsogenyRoots

end SimpleIsogenyGraph

end Langlands.GroupScheme.RootDatumIsogenyRealization
