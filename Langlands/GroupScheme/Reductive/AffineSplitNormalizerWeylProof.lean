import Langlands.GroupScheme.Reductive.AffineSplitNormalizerWeylStatement
import Langlands.GroupScheme.Reductive.AffineSplitNormalizerWeylFinite
import Langlands.GroupScheme.Reductive.AffineSplitNormalizedRepresentatives

/-! # Proof: normalizer points of a split maximal torus map onto the Weyl group -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Normalizer points of a split maximal torus and the Weyl group** (Conrad, *Reductive group
schemes*, Example 6.4.3). Over a ring with connected spectrum, for a split reductive group with
split maximal torus `T`, the sequence `1 → T(S) → N_G(T)(S) → W(Φ) → 1` is exact. Over a domain,
some finite subgroup of the normalizer points maps onto `W(Φ)`. -/
theorem affineSplitNormalizerWeyl : AffineSplitNormalizerWeylStatement.{u} := by
  intro R _ _ G hG I _ i J P hi hmax hP hfree Induces
  have := hG.isAffineHom
  classical
  refine ⟨AffineSplitReflection.weylGroup_induced R G hG I i J P hi hmax hP hfree,
    fun n hn => AffineSplitNormalizerWeyl.exists_weylGroup_of_mem_normalizerPoints hG i hi hmax hP hn,
    fun n hn => AffineSplitNormalizerWeyl.exists_eq_of_mem_centralizerPoints hG i hi hmax hn,
    fun _ => ?_⟩
  obtain ⟨n, hn, hsq⟩ :=
    AffineSplitReflection.exists_reflection_representatives hG i hi hmax hP hfree
  have : Finite J := hP.1
  have : P.IsReduced := hP.2.1
  exact AffineSplitNormalizerWeyl.exists_finite_subgroup_of_representatives hG hi hmax n hn hsq

end Langlands.GroupScheme
