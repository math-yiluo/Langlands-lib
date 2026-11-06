import Langlands.GroupScheme.HomScheme.TorusSubgroupChartStatements
import Langlands.GroupScheme.HomScheme.ChartCoverBaseChange
import Langlands.GroupScheme.HomScheme.ChartCoverOpenExtension
import Langlands.GroupScheme.HomScheme.SmoothAffineGroupFiniteTypeModel

/-! # Reduction of chart covers to bases of finite type over `ℤ` -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

/-- Chart covers over affine bases of finite type over `ℤ` give chart covers of every
smooth affine group scheme over an affine base. -/
theorem hasChartCover_affine (hfin : FiniteTypeChartCoverStatement.{u}) (R : CommRingCat.{u})
    (G : GroupScheme (Spec R)) [Smooth G.X.hom] [IsAffineHom G.X.hom] : HasChartCover G := by
  obtain ⟨R₀, _, _, φ, G₀, hs, ha, ⟨e⟩⟩ := exists_finiteType_model R G
  have : Smooth G₀.X.hom := hs
  have : IsAffineHom G₀.X.hom := ha
  exact hasChartCover_iso e.symm (hasChartCover_baseChange _ (hfin R₀ G₀))

/-- Chart covers over affine bases of finite type over `ℤ` give chart covers of every
smooth affine group scheme over every base scheme. -/
theorem chartCoverReduction : ChartCoverReductionStatement.{u} := by
  intro hfin S G _ _
  have key : HasChartCover G := by
    refine hasChartCover_of_openCover (J := S.affineOpens) (fun V => V.2.fromSpec) ?_ ?_
    · intro s
      obtain ⟨_, ⟨V, hV, rfl⟩, hsV, -⟩ :=
        S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
      refine ⟨⟨V, hV⟩, ?_⟩
      change s ∈ Set.range (hV.fromSpec : Spec Γ(S, V) → S)
      rw [IsAffineOpen.range_fromSpec]
      exact hsV
    · intro V
      have : Smooth ((baseChange V.2.fromSpec).obj G).X.hom := by
        change Smooth (pullback.snd G.X.hom V.2.fromSpec)
        infer_instance
      have : IsAffineHom ((baseChange V.2.fromSpec).obj G).X.hom := by
        change IsAffineHom (pullback.snd G.X.hom V.2.fromSpec)
        infer_instance
      exact hasChartCover_affine hfin _ _
  exact key

end Langlands.GroupScheme.TorusSubgroupModuli
