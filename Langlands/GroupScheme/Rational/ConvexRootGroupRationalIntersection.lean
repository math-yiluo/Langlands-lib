import Langlands.GroupScheme.Rational.ConvexRootNormalizerWeyl
import Langlands.GroupScheme.Rational.OvergroupNormalizerFactorization
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.Torus.SplitReflection
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof

/-! # Rational-point intersection from normalization and convex Weyl groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section RationalIntersection

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  {S X : Set (characterLattice T)}
  (hS : IsConvexRootSubset (relativeRoots i) S)
  (hX : IsConvexRootSubset (relativeRoots i) X)
  {H₁ H₂ H₃ : GroupScheme (Spec (CommRingCat.of k))}
  {h₁ : H₁ ⟶ G} {h₂ : H₂ ⟶ G} {h₃ : H₃ ⟶ G}
  (hH₁ : IsRootSubsetGroup i S h₁) (hH₂ : IsRootSubsetGroup i X h₂)
  (hH₃ : IsRootSubsetGroup i (S ∩ X) h₃)

include hG hi hS hX hH₁ hH₂ hH₃

/-- Maximal-torus conjugacy and all-test normalization turn the convex Weyl
intersection formula into equality on rational points. -/
theorem convexRootGroups_rationalPoints_inter_of_normalizing
    (hmax : IsMaximalTorus i) (hconj : MaximalToriAreConjugate H₃)
    (hnorm : SubgroupFunctor.range h₁ ⊓ SubgroupFunctor.range h₂ ≤
      (SubgroupFunctor.range h₃).normalizer) :
    (SubgroupFunctor.range h₁).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ⊓
        (SubgroupFunctor.range h₂).carrier (Over.mk (𝟙 _)) =
      (SubgroupFunctor.range h₃).carrier (Over.mk (𝟙 _)) := by
  let : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : IsClosedImmersion h₃.hom.hom.left := hH₃.1
  let : Mono h₃.hom.hom := Over.mono_of_mono_left _
  have hle₁ : SubgroupFunctor.range h₃ ≤ SubgroupFunctor.range h₁ :=
    hH₃.2.2.2 H₁ h₁ hH₁.1 hH₁.2.1 (fun α hα => hH₁.2.2.1 α hα.1)
  have hle₂ : SubgroupFunctor.range h₃ ≤ SubgroupFunctor.range h₂ :=
    hH₃.2.2.2 H₂ h₂ hH₂.1 hH₂.2.1 (fun α hα => hH₂.2.2.1 α hα.2)
  obtain ⟨f, hf⟩ := SubgroupFunctor.exists_factor_of_range_le
    ((range_le_torusCentralizer i).trans hH₃.2.1)
  have hfmax : IsMaximalTorus f := IsMaximalTorus.of_comp hH₃.1 (hf.symm ▸ hmax)
  apply le_antisymm
  · apply pointSubgroup_le_range_of_normalizer_inter_le h₃ f hfmax hconj
    · exact le_inf (hle₁ _) (hle₂ _)
    · exact hnorm _
    · intro n hn
      have hnT : n ∈ normalizerPoints i := by
        have h := hn.2
        rwa [hf] at h
      exact (normalizer_mem_convexRootGroups_inter_iff i hG hi hS hX
        hH₁ hH₂ hH₃ ⟨n, hnT⟩).mp hn.1
  · exact le_inf (hle₁ _) (hle₂ _)

/-- Over an algebraically closed field, the common-root group's smoothness,
affineness and connectedness provide the required rational torus conjugacy. -/
theorem convexRootGroups_rationalPoints_inter_of_isAlgClosed_of_normalizing
    [IsAlgClosed k] [Smooth H₃.X.hom] [IsAffineHom H₃.X.hom]
    [ConnectedSpace H₃.X.left]
    (hnorm : SubgroupFunctor.range h₁ ⊓ SubgroupFunctor.range h₂ ≤
      (SubgroupFunctor.range h₃).normalizer) :
    (SubgroupFunctor.range h₁).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ⊓
        (SubgroupFunctor.range h₂).carrier (Over.mk (𝟙 _)) =
      (SubgroupFunctor.range h₃).carrier (Over.mk (𝟙 _)) := by
  have hsplit : ToriAreSplit k := fun A hA =>
    hA.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  apply convexRootGroups_rationalPoints_inter_of_normalizing i hG hi hS hX
    hH₁ hH₂ hH₃ (hi.isMaximalTorus hsplit) _ hnorm
  intro T₁ T₂ f₁ f₂ hf₁ hf₂
  exact (subgroupConjugate_iff_exists_commGroupSchemeIso f₁ f₂).mpr
    (maximalTorusConjugacy k H₃ T₁ T₂ f₁ f₂ hf₁ hf₂)

end RationalIntersection

/-- Uniform rational-point intersection, retaining absolute maximality,
rational conjugacy and normalization on every test scheme. -/
def ConvexRootGroupRationalIntersectionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (_hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    ∀ (S X : Set (characterLattice T)),
      IsConvexRootSubset (relativeRoots i) S →
      IsConvexRootSubset (relativeRoots i) X →
      ∀ (H₁ H₂ H₃ : GroupScheme (Spec (CommRingCat.of k)))
        (h₁ : H₁ ⟶ G) (h₂ : H₂ ⟶ G) (h₃ : H₃ ⟶ G),
        IsRootSubsetGroup i S h₁ → IsRootSubsetGroup i X h₂ →
        IsRootSubsetGroup i (S ∩ X) h₃ → IsMaximalTorus i →
        MaximalToriAreConjugate H₃ →
        SubgroupFunctor.range h₁ ⊓ SubgroupFunctor.range h₂ ≤
          (SubgroupFunctor.range h₃).normalizer →
        (SubgroupFunctor.range h₁).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ⊓
            (SubgroupFunctor.range h₂).carrier (Over.mk (𝟙 _)) =
          (SubgroupFunctor.range h₃).carrier (Over.mk (𝟙 _))

/-- Minimality, normalizer factorization and the convex Weyl formula prove
the uniform rational-point intersection statement. -/
theorem convexRootGroupRationalIntersection :
    ConvexRootGroupRationalIntersectionStatement.{u} := by
  intro k _ G hG T i hi
  let := hG.isAffineHom
  intro S X hS hX H₁ H₂ H₃ h₁ h₂ h₃ hH₁ hH₂ hH₃ hmax hconj hnorm
  exact convexRootGroups_rationalPoints_inter_of_normalizing i hG hi hS hX
    hH₁ hH₂ hH₃ hmax hconj hnorm

end Langlands.GroupScheme
