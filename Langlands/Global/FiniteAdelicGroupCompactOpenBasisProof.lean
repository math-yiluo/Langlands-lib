import Langlands.Global.FiniteAdelicGroupCompactOpenBasisStatement
import Langlands.Topology.LocallyProfiniteProof
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Filter
open scoped CategoryTheory.MonObj Topology RestrictedProduct

namespace Langlands.Global

variable (F : Type u) [Field F] [NumberField F]

/-- Continuous injection into the product transfers total disconnectedness
without asserting that the restricted-product map is an embedding. -/
theorem finiteAdeles_totallyDisconnectedSpace :
    TotallyDisconnectedSpace (FiniteAdeleRing (𝓞 F) F) := by
  let : ∀ v : FinitePlace F, TotallyDisconnectedSpace (FiniteCompletion F v) :=
    fun _ => inferInstance
  constructor
  exact isTotallyDisconnected_of_image
    (RestrictedProduct.continuous_coe.continuousOn :
      ContinuousOn
        ((↑) : (Πʳ v : FinitePlace F,
          [FiniteCompletion F v, v.adicCompletionIntegers F]) →
            ∀ v : FinitePlace F, FiniteCompletion F v) Set.univ)
    DFunLike.coe_injective (isTotallyDisconnected_of_totallyDisconnectedSpace _)

variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

/-- The original affine evaluation embedding has a totally disconnected target. -/
theorem finiteAdelicGroupPoints_totallyDisconnectedSpace :
    TotallyDisconnectedSpace (FiniteAdelicGroupPoints F G) := by
  let : TotallyDisconnectedSpace (FiniteAdeleRing (𝓞 F) F) :=
    finiteAdeles_totallyDisconnectedSpace F
  exact (G.isEmbedding_affinePointEvaluation
    (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F))).isTotallyDisconnected_range.mp
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)

/-- Specialize public Van Dantzig to the original locally compact finite points. -/
theorem finiteAdelicGroupCompactOpenBasis :
    FiniteAdelicGroupCompactOpenBasisStatement.{u} := by
  intro F _ _ G _
  have htd := finiteAdelicGroupPoints_totallyDisconnectedSpace F G
  refine ⟨htd, ?_⟩
  intro _
  let : TotallyDisconnectedSpace (FiniteAdelicGroupPoints F G) := htd
  have hb := ((Langlands.Topology.LocallyProfiniteProof.vanDantzig
    (FiniteAdelicGroupPoints F G)).mp
      Langlands.Topology.isLocallyProfinite_of_mathlib).2
  constructor
  intro U
  constructor
  · exact hb U
  · rintro ⟨K, _, hKU⟩
    exact mem_of_superset K.mem_nhds_one hKU

end Langlands.Global
