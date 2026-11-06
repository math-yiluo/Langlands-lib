import Langlands.GroupScheme.Dynamic.CentralizerRootsStatement
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Rational.StandardLeviLieWeights
import Langlands.GroupScheme.Absolute.RegularCocharacterWeights

/-! # The roots of the centralizer of a cocharacter of a split maximal torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Roots of the centralizer of a cocharacter.** The roots of `T` in a closed representative
`Z` of the centralizer of `ν ≫ i` are the roots `α` of `T` in `G` with `⟨α, ν⟩ = 0`. A root
vector of `Z` maps to a root vector of `G` under the injective differential of `z`, and lies in
the weight-zero space of `ν` by `dynamicLie`; conversely a root vector of `G` of weight zero for
`ν` is a tangent vector of the centralizer, hence comes from `Z`. -/
theorem dynamicCentralizerRoots : DynamicCentralizerRootsStatement.{u} := by
  intro k _ G hG T hT i hi ν Z z hz hrep hZ t ht
  have := hG.isAffineHom
  have := hZ.isAffineHom
  have := hG.smooth
  have : Mono z.hom.hom := hrep.1
  ext α
  constructor
  · rintro ⟨hα0, hαne⟩
    obtain ⟨Y, hY, hY0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hαne
    have hX : Lie.targetMapLinear z _ Y ∈ weightSpace i α := by
      have h := lieKernelHomLinear_mem_weightSpace z t α hY
      rwa [ht] at h
    have hX0 : Lie.targetMapLinear z _ Y ≠ 0 := by
      intro h
      apply hY0
      apply Lie.targetMapLinear_injective z _
      rw [h, map_zero]
    refine ⟨⟨hα0, fun hbot => hX0 ?_⟩, ?_⟩
    · rw [hbot] at hX
      exact (Submodule.mem_bot _).mp hX
    · have hcent := (hrep.mem_range_lieKernelHomLinear (Lie.targetMapLinear z _ Y)).mp ⟨Y, rfl⟩
      have h0 := (dynamicLie k G (CommGroupScheme.groupHom ν ≫ i)
        (Lie.targetMapLinear z _ Y).toMul).1.mp hcent
      have hn := weightSpace_le_weightSpace_cocharacter ν i α hX
      by_contra hne
      have hdis := weightSpace_disjoint isSplitTorus_gm (CommGroupScheme.groupHom ν ≫ i)
        (χ := Gm.powerHom _ (latticePairing T α ν)) (χ' := Gm.powerHom _ 0)
        (fun h => hne (Gm.powerHom_injective k h))
      exact hX0 ((Submodule.disjoint_def.mp hdis) _ hn h0)
  · rintro ⟨⟨hα0, hαne⟩, hpair⟩
    obtain ⟨X, hX, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hαne
    have hn := weightSpace_le_weightSpace_cocharacter ν i α hX
    rw [hpair] at hn
    have hcent := (dynamicLie k G (CommGroupScheme.groupHom ν ≫ i) X.toMul).1.mpr hn
    obtain ⟨Y, hY⟩ := (hrep.mem_range_lieKernelHomLinear X).mpr hcent
    refine ⟨hα0, fun hbot => hX0 ?_⟩
    have hYw : Y ∈ weightSpace t α := by
      apply (lieKernelHomLinear_mem_weightSpace_iff z t α Y).mp
      rw [ht, hY]
      exact hX
    rw [hbot] at hYw
    rw [← hY, (Submodule.mem_bot _).mp hYw, map_zero]

end Langlands.GroupScheme
