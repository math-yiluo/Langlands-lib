import Langlands.GroupScheme.Dynamic.CentralizerWeightSpace
import Langlands.GroupScheme.Reductive.SplitRootLieLineStatement

/-! # Reduction of split root lines to proportional-root centralizers -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RootReducedness in
/-- Split root Lie spaces are lines once this is known for groups whose roots
are pairwise dependent. Connected reductivity of cocharacter centralizers
and the rank-one line assertion remain explicit inputs. -/
theorem splitRootLieLine_of_rankOne
    (hcent : DynamicCentralizerReductiveStatement.{u})
    (hrank : ∀ (k : Type u) [Field k]
      (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
      (T : CommGroupScheme (Spec (CommRingCat.of k))),
      IsSplitTorus T.toGrp → ∀ i : T.toGrp ⟶ G, IsMaximalTorus i →
        haveI := hG.isAffineHom
        (∀ β ∈ roots i, ∀ γ ∈ roots i, ¬ LinearIndependent ℤ ![β, γ]) →
          ∀ χ ∈ roots i, Nonempty (k ≃ₗ[k] weightSpace i χ)) :
    SplitRootLieLineStatement.{u} := by
  intro k _ G hG T hT i hi χ hχ
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth G.X.hom := hG.smooth
  have hχζ := latticePairing_kernelCocharacter hT hχ.1 (hT.finite_relativeRoots i)
  have hζ := fun γ (hγ : γ ∈ roots i) =>
    not_linearIndependent_of_latticePairing_kernelCocharacter hT hχ.1
      (hT.finite_relativeRoots i) hγ
  generalize kernelCocharacter hT hχ.1 (hT.finite_relativeRoots i) = ζ at hχζ hζ
  have hj := Dynamic.Affine.isRepresentedBy_centralizerHom (CommGroupScheme.groupHom ζ ≫ i)
  have hjc := Dynamic.Affine.isClosedSubgroup_centralizerHom (CommGroupScheme.groupHom ζ ≫ i)
  have hL := hcent k G hG _ _ _ hjc hj
  have : IsAffineHom (Dynamic.Affine.centralizerScheme
    (CommGroupScheme.groupHom ζ ≫ i)).X.hom := hL.isAffineHom
  have hiL : IsMaximalTorus (Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj) :=
    IsMaximalTorus.of_comp hjc (by rwa [Dynamic.torusFactor_comp])
  have hdep : ∀ β ∈ roots (Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj),
      ∀ γ ∈ roots (Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj),
      ¬ LinearIndependent ℤ ![β, γ] := by
    intro β hβ γ hγ
    obtain ⟨hβ', hβζ⟩ := mem_roots_of_mem_roots_torusFactor i ζ hj hβ
    obtain ⟨hγ', hγζ⟩ := mem_roots_of_mem_roots_torusFactor i ζ hj hγ
    exact not_linearIndependent_of_not_linearIndependent hT hχ.1 hγ'.1
      (hζ β hβ' hβζ) (hζ γ hγ' hγζ)
  have hline := hrank k _ hL T hT _ hiL hdep χ (mem_roots_torusFactor i ζ hj hχ hχζ)
  exact (Dynamic.nonempty_line_torusFactor_iff i ζ hj χ hχζ).mp hline

end Langlands.GroupScheme
