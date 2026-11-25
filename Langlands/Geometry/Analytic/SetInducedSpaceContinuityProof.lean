import Langlands.Geometry.Analytic.SetInducedSpaceContinuityStatement
import Langlands.Geometry.Analytic.LocalizedSigmaNearness

/-! # Proof: the spaces `X_Σ` of discrete `G`-sets are `G`-spaces -/

noncomputable section

universe u v z

open CategoryTheory CategoryTheory.Limits Topology

namespace Langlands.Analytic.SaturatedAtlasPresentation.SetInducedSpace

/-- **Berkovich's space `X_Σ` of a `G`-space `X` and a `G`-set `Σ` with open stabilizers is a
`G`-space** (Berkovich 1996, §1.2). -/
theorem continuityStatement : ContinuityStatement.{u, v, z} := by
  intro K _ _ _ G _ _ _ X S _ hS hX
  refine ⟨?_, fun τ => ?_⟩
  · have : T2Space ((presentationOf X.V).presentation.space) := hX.1
    exact (inferInstance : T2Space ((_ : S) × (presentationOf X.V).presentation.space))
  · obtain ⟨s₀, hτ⟩ :=
      TestTriple.exists_locus_subset_range_localizedSigmaCofan (fun _ : S => X.V) τ
    obtain ⟨E, -, hE⟩ := exists_isNear_postcomp (copy X S s₀) τ
      (isCompact_preimage_localizedSigmaCofan_inj (fun _ : S => X.V) s₀ τ)
    have hV : (⋂ τ' ∈ E, X.ρAut ⁻¹' nearIdentity τ') ∈ 𝓝 (1 : G) :=
      (Filter.biInter_finset_mem E).2 fun τ' _ => hX.2 τ'
    have hW : (MulAction.stabilizer G s₀ : Set G) ∩ ⋂ τ' ∈ E, X.ρAut ⁻¹' nearIdentity τ' ∈
        𝓝 (1 : G) :=
      Filter.inter_mem ((hS s₀).mem_nhds (MulAction.stabilizer G s₀).one_mem) hV
    refine Filter.mem_of_superset hW fun g hg => ?_
    obtain ⟨hgs₀, hgV⟩ := hg
    have hgs₀' : g • s₀ = s₀ := MulAction.mem_stabilizer_iff.mp hgs₀
    change IsNear τ (actionMap X S g) (𝟙 _)
    refine isNear_of_localizedSigmaCofan (fun _ : S => X.V) τ _ _ fun s => ?_
    change IsNear τ (copy X S s ≫ actionMap X S g) (copy X S s ≫ 𝟙 _)
    rw [copy_actionMap, Category.comp_id]
    by_cases hs : s = s₀
    · rw [hs, hgs₀']
      have := hE X.V (X.ρ g).asHom (𝟙 X.V) fun τ' hτ' => Set.mem_iInter₂.mp hgV τ' hτ'
      rwa [Category.id_comp] at this
    · have hgs : g • s ≠ s₀ := fun h' => hs (MulAction.injective g (h'.trans hgs₀'.symm))
      refine isNear_of_preimage_eq_empty ?_ ?_
      · exact preimage_locus_comp_localizedSigmaCofan_inj_eq_empty (fun _ : S => X.V) hgs _
          τ hτ
      · have := preimage_locus_comp_localizedSigmaCofan_inj_eq_empty (fun _ : S => X.V) hs
          (𝟙 X.V) τ hτ
        rwa [Category.id_comp] at this

end Langlands.Analytic.SaturatedAtlasPresentation.SetInducedSpace
