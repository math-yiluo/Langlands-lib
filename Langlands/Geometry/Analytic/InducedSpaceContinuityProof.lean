import Langlands.Geometry.Analytic.InducedSpaceContinuityStatement
import Langlands.Geometry.Analytic.LocalizedSigmaNearness

/-! # Proof: induced spaces of `H`-spaces are `G`-spaces -/

noncomputable section

universe u v z

open CategoryTheory CategoryTheory.Limits Topology

namespace Langlands.Analytic.SaturatedAtlasPresentation

/-! ## The induced space is a `G`-space -/

namespace InducedSpace

open PresentedAffinoidAlgebra.InducedAction (correction correction_coe)

/-- **Berkovich's induced space `X_{G/H}` of an `H`-space is a `G`-space** (Berkovich 1996,
1.1.2). -/
theorem continuityStatement : ContinuityStatement.{u, v, z} := by
  intro K _ _ _ G _ _ _ H hH X hX
  refine ⟨?_, fun τ => ?_⟩
  · have : T2Space ((presentationOf X.V).presentation.space) := hX.1
    exact (inferInstance : T2Space ((_ : G ⧸ H) × (presentationOf X.V).presentation.space))
  · obtain ⟨c₀, hτ⟩ :=
      TestTriple.exists_locus_subset_range_localizedSigmaCofan (fun _ : G ⧸ H => X.V) τ
    obtain ⟨E, -, hE⟩ := exists_isNear_postcomp (copy H X c₀) τ
      (isCompact_preimage_localizedSigmaCofan_inj (fun _ : G ⧸ H => X.V) c₀ τ)
    have hV : (⋂ τ' ∈ E, X.ρAut ⁻¹' nearIdentity τ') ∈ 𝓝 (1 : H) :=
      (Filter.biInter_finset_mem E).2 fun τ' _ => hX.2 τ'
    have hW : (fun g : G => c₀.out⁻¹ * g * c₀.out) ⁻¹'
        (Subtype.val '' ⋂ τ' ∈ E, X.ρAut ⁻¹' nearIdentity τ') ∈ 𝓝 (1 : G) := by
      have h1 := hH.isOpenMap_subtype_val.image_mem_nhds hV
      have hc : Continuous fun g : G => c₀.out⁻¹ * g * c₀.out := by fun_prop
      refine hc.continuousAt.preimage_mem_nhds ?_
      have e1 : c₀.out⁻¹ * 1 * c₀.out = ((1 : H) : G) := by simp
      rw [e1]
      exact h1
    refine Filter.mem_of_superset hW fun g hg => ?_
    obtain ⟨h, hhV, hh'⟩ := hg
    have hh : (h : G) = c₀.out⁻¹ * g * c₀.out := hh'
    have hgc₀ : g • c₀ = c₀ := by
      rw [← MulAction.Quotient.coe_smul_out H g c₀, smul_eq_mul]
      conv_rhs => rw [← QuotientGroup.out_eq' c₀]
      rw [QuotientGroup.eq]
      have h2 : (g * c₀.out)⁻¹ * c₀.out = (h : G)⁻¹ := by
        rw [hh]
        group
      rw [h2]
      exact H.inv_mem h.2
    have hcorr : correction H g c₀ = h := by
      apply Subtype.ext
      rw [correction_coe, hgc₀, hh, mul_assoc]
    change IsNear τ (actionMap H X g) (𝟙 _)
    refine isNear_of_localizedSigmaCofan (fun _ : G ⧸ H => X.V) τ _ _ fun c => ?_
    change IsNear τ (copy H X c ≫ actionMap H X g) (copy H X c ≫ 𝟙 _)
    rw [copy_actionMap, Category.comp_id]
    by_cases hc : c = c₀
    · rw [hc, hcorr, hgc₀]
      have := hE X.V (X.ρ h).asHom (𝟙 X.V) fun τ' hτ' => Set.mem_iInter₂.mp hhV τ' hτ'
      rwa [Category.id_comp] at this
    · have hgc : g • c ≠ c₀ := fun h' => hc (MulAction.injective g (h'.trans hgc₀.symm))
      refine isNear_of_preimage_eq_empty ?_ ?_
      · exact preimage_locus_comp_localizedSigmaCofan_inj_eq_empty (fun _ : G ⧸ H => X.V) hgc _
          τ hτ
      · have := preimage_locus_comp_localizedSigmaCofan_inj_eq_empty (fun _ : G ⧸ H => X.V) hc
          (𝟙 X.V) τ hτ
        rwa [Category.id_comp] at this

end InducedSpace

end Langlands.Analytic.SaturatedAtlasPresentation
