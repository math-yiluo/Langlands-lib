/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper

/-!
# The curve estimate on an arbitrary affine curve

Let `C` be an affine `k₀`-scheme of finite type of dimension at most one, not necessarily
geometrically connected, and `F` a Weil sheaf on `C`, punctually `ι`-pure of weight `w`. Then
`H_c^r(C, F)` has weights at most `w + r`.

## Implementation notes

Rather than passing to a finite constant extension over which the geometric components of `C`
are defined, a finite morphism `f : C ⟶ 𝔸¹_{k₀}` (Noether normalization) identifies `H_c^r(C, F)`
with `H_c^r(𝔸¹, f₀*F)`; the finite direct image `f₀*F` is punctually pure of weight `w` and lisse
on a dense open `V ⊆ 𝔸¹`, which is a smooth geometrically connected curve, where the estimate on
dense opens of the line
(`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.hasWeightsAtMostOver_compactlySupportedCohomology`)
applies; the finite complement contributes only in degree zero, with weights at most `w`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

/- Through `Mathlib.AlgebraicGeometry.Group.Affine`, `Spec k₀` is also an object over itself via
`specOverSpec`; prefer the identity structure `CategoryTheory.instOverClass`. -/
attribute [local instance 1100] CategoryTheory.instOverClass

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (ι : PadicAlgCl l →+* ℂ)

section AffineLine

/-- **The curve estimate on the affine line, without lissity.** Let `G` be a Weil sheaf on
`𝔸¹_{k₀}`, punctually `ι`-pure of weight `w`. Then `H_c^r(𝔸¹, G)` has weights at most `w + r`:
`G` is lisse on a dense open `U` with finite complement `Z`, the curve estimate applies on `U`,
the finite `Z` only contributes in degree zero with weights at most `w`, and the open–closed exact
sequence `Rʳ(a_U)₀! G|_U ⟶ Rʳa₀! G ⟶ Rʳ(a_Z)₀! G|_Z` bounds the weights of the middle term. -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_affineLine
    (G : WeilSheaf k₀ l 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀))) {w : ℝ}
    (hG : G.IsPunctuallyPureOfWeight ι w) (r : ℕ) :
    (G.compactlySupportedCohomology r).HasWeightsAtMostOver k₀ ι (w + r) := by
  -- the lisse locus `U` of `G`, a dense open with finite complement
  obtain ⟨U, hUd, hUl⟩ := WeilSheaf.exists_dense_isLisse_upperStar G
  obtain ⟨b, ⟨s, hs⟩, hb⟩ :=
    AffineSpace.exists_basicOpen_forall_exists_mem_and_finite U hUd.nonempty
  have hfin : ((U : Set 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀)))ᶜ).Finite :=
    (hb s hs).2.subset fun x hx ↦ ⟨hx, Subsingleton.elim _ _⟩
  -- the reduced closed complement `Z` of `U`, quasi-finite over `k₀`
  let C : TopologicalSpace.Closeds 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀)) :=
    ⟨(U : Set 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀)))ᶜ, U.isOpen.isClosed_compl⟩
  let i := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  let : (Scheme.IdealSheafData.vanishingIdeal C).subscheme.Over (Spec (CommRingCat.of k₀)) :=
    ⟨i ≫ 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀)⟩
  have : i.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have hrange : Set.range i = C := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have : LocallyOfFiniteType
      ((Scheme.IdealSheafData.vanishingIdeal C).subscheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over i]
    infer_instance
  have : LocallyQuasiFinite (i ≫ 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀)) ↘
      Spec (CommRingCat.of k₀)) := by
    refine .of_finite_preimage_singleton _ fun _ ↦
      (hfin.preimage i.isClosedEmbedding.injective.injOn).subset fun z _ ↦ ?_
    exact (hrange ▸ ⟨z, rfl⟩ : i z ∈ (C : Set _))
  have := isNoetherian_of_locallyOfFiniteType
    (𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))
  -- the open–closed exact sequence on `Spec k₀`
  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := WeilSheaf.exists_exact_higherLowerShriek_of_openClosed
    (j := U.ι) (i := i) (f := 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀)) ↘
      Spec (CommRingCat.of k₀))
    (by rw [Scheme.Opens.range_ι, hrange]; exact isCompl_compl) G r
  -- the open part: the curve estimate on `U`
  have h₁ : S.X₁.HasWeightsAtMost ι (w + r) := by
    have hc := comp_over U.ι (Spec (CommRingCat.of k₀))
    have : Nonempty U := hUd.nonempty.to_subtype
    have : SmoothOfRelativeDimension 1 (U.toScheme ↘ Spec (CommRingCat.of k₀)) := by
      rw [← hc]
      exact AffineSpace.smoothOfRelativeDimension_one_of_isOpenImmersion U.ι
    have : GeometricallyConnected (U.toScheme ↘ Spec (CommRingCat.of k₀)) := by
      rw [← hc]
      exact AffineSpace.geometricallyConnected_of_isOpenImmersion U.ι
    have : IsSeparated (U.toScheme ↘ Spec (CommRingCat.of k₀)) := by
      rw [← hc]
      infer_instance
    have : QuasiCompact (U.toScheme ↘ Spec (CommRingCat.of k₀)) := by
      rw [← hc]
      infer_instance
    have : QuasiCompact U.ι := inferInstance
    have : IsDominant U.ι := ⟨by rwa [DenseRange, Scheme.Opens.range_ι]⟩
    have hU := WeilSheaf.LisseOnDenseOpen.hasWeightsAtMostOver_compactlySupportedCohomology
      ⟨U, U.ι, _, hUl⟩ (hG.upperStar U.ι) r
    obtain ⟨E⟩ := WeilSheaf.nonempty_equiv_compactlySupportedCohomology_zero_higherLowerShriek
      (U.ι ≫ 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))
      ((WeilSheaf.upperStar U.ι).obj G) r
    exact (WeilSheaf.hasWeightsAtMost_of_compactlySupportedCohomology_zero
      (FrobeniusModule.HasWeightsAtMost.of_equiv E hU)).of_epi e₁.inv
  -- the closed part: `Z` is quasi-finite over `k₀`
  have h₃ : S.X₃.HasWeightsAtMost ι (w + r) := by
    refine WeilSheaf.HasWeightsAtMost.of_epi e₃.inv ?_
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · refine (WeilSheaf.HasWeightsAtMost.higherLowerShriek_zero_of_quasiFinite _
        (hG.upperStar i).hasWeightsAtMost).mono ?_
      simp
    · exact (WeilSheaf.isPunctuallyPureOfWeight_of_isZero
        (isZero_higherLowerShriek_of_quasiFinite _ r hr _) _).hasWeightsAtMost
  obtain ⟨E⟩ := WeilSheaf.nonempty_equiv_compactlySupportedCohomology_zero_higherLowerShriek
    (𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀)) G r
  exact FrobeniusModule.HasWeightsAtMost.of_equiv E.symm
    (((WeilSheaf.HasWeightsAtMost.of_exact hS h₁ h₃).of_epi
      e₂.hom).compactlySupportedCohomology_zero)

end AffineLine

/-- **The curve estimate on an affine curve.** Let `C` be an affine `k₀`-scheme of finite type of
dimension at most one and `F` a Weil sheaf on `C`, punctually `ι`-pure of weight `w`. Then
`H_c^r(C, F)` has weights at most `w + r`: this is the curve estimate on the geometric components
of an affine fibre. -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_of_isAffine {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    (hC : ringKrullDim Γ(C, ⊤) ≤ 1) (F : WeilSheaf k₀ l C) {w : ℝ}
    (hw : F.IsPunctuallyPureOfWeight ι w) (r : ℤ) :
    (F.compactlySupportedCohomology r).HasWeightsAtMostOver k₀ ι (w + r) := by
  rcases lt_or_ge r 0 with hr | hr
  · -- `H_c^r` vanishes in negative degrees
    intro β hβ
    have : Subsingleton (F.compactlySupportedCohomology r).carrier :=
      WeilSheaf.subsingleton_globalSections_of_isZero
        (WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg
          (f := C ↘ Spec (CommRingCat.of k₀)) F hr)
    obtain ⟨x, hx⟩ := hβ.exists_hasEigenvector
    exact (hx.2 (Subsingleton.elim _ _)).elim
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, r = n := ⟨r.toNat, (Int.toNat_of_nonneg hr).symm⟩
  -- a finite morphism `f : C ⟶ 𝔸¹_{k₀}` identifies `H_c^n(C, F)` with `H_c^n(𝔸¹, f₀!F)`
  obtain ⟨f, hf, hfo⟩ := AffineSpace.exists_isFinite_of_ringKrullDim_le_one (k := k₀) C hC
  have : f.IsOver (Spec (CommRingCat.of k₀)) := ⟨hfo⟩
  obtain ⟨E⟩ := WeilSheaf.nonempty_equiv_compactlySupportedCohomology_higherLowerShriek_zero f F n
  exact FrobeniusModule.HasWeightsAtMost.of_equiv E
    (hasWeightsAtMostOver_compactlySupportedCohomology_affineLine ι _
      (hw.higherLowerShriek_zero_of_quasiFinite f) n)

/-- **Purity of the top affine-curve factor.** Let `C` be a smooth affine curve over `k₀`, not
necessarily geometrically connected, and let `E` be a lisse Weil sheaf on `C`, punctually `ι`-pure
of weight `0`. Then `H_c^2(C, E)` is `ι`-pure of weight `2`. For a finite morphism
`f : C ⟶ 𝔸¹_{k₀}`,
`H_c^2(C, E) ≅ H_c^2(𝔸¹, f₀*E) ≅ H_c^2(V, f₀*E)` for a dense open `V ⊆ 𝔸¹` on which `f₀*E` is
lisse, and the degree-two endpoint estimate applies on the geometrically connected `V`. -/
theorem isPureOfWeightOver_compactlySupportedCohomology_two_of_isAffine {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))] (E : WeilSheaf k₀ l C)
    (hE : E.IsLisse) (hpure : E.IsPunctuallyPureOfWeight ι 0) :
    -- `C ↘ Spec k₀` is locally of finite type, being smooth
    haveI := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
    (E.compactlySupportedCohomology 2).IsPureOfWeightOver k₀ ι 2 := by
  have := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  obtain ⟨f, hf, hfo⟩ := AffineSpace.exists_isFinite_of_ringKrullDim_le_one (k := k₀) C
    (ringKrullDim_le_of_smoothOfRelativeDimension (C ↘ Spec (CommRingCat.of k₀)) 1)
  have : f.IsOver (Spec (CommRingCat.of k₀)) := ⟨hfo⟩
  obtain ⟨e⟩ := WeilSheaf.nonempty_equiv_compactlySupportedCohomology_higherLowerShriek_zero f E 2
  exact FrobeniusModule.IsPureOfWeight.of_equiv e
    (WeilSheaf.isPureOfWeightOver_compactlySupportedCohomology_two_of_isFinite ι f E hE hpure)

/-- **Vanishing of `H_c^0` on a smooth affine curve.** Let `C` be a smooth affine curve over `k₀`,
not necessarily geometrically connected, and let `E` be a lisse Weil sheaf on `C`. Then
`H_c^0(C, E) = 0`, the vanishing of the degree-zero group of an affine fibre. For a finite
morphism `f : C ⟶ 𝔸¹_{k₀}`, the direct image `f₀*E` is the middle extension of its restriction to a
dense open `V ⊆ 𝔸¹` on which it is lisse, and `H_c^0` of a middle extension on the geometrically
connected `𝔸¹` vanishes
(`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_higherLowerShriek_zero`). -/
theorem WeilSheaf.subsingleton_compactlySupportedCohomology_zero_of_isAffine {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))] (E : WeilSheaf k₀ l C)
    (hE : E.IsLisse) :
    -- `C ↘ Spec k₀` is locally of finite type, being smooth
    haveI := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
    Subsingleton (E.compactlySupportedCohomology 0).carrier := by
  have := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  obtain ⟨f, hf, hfo⟩ := AffineSpace.exists_isFinite_of_ringKrullDim_le_one (k := k₀) C
    (ringKrullDim_le_of_smoothOfRelativeDimension (C ↘ Spec (CommRingCat.of k₀)) 1)
  have : f.IsOver (Spec (CommRingCat.of k₀)) := ⟨hfo⟩
  obtain ⟨e⟩ := WeilSheaf.nonempty_equiv_compactlySupportedCohomology_higherLowerShriek_zero f E 0
  have := WeilSheaf.subsingleton_compactlySupportedCohomology_higherLowerShriek_zero f E hE
  exact e.toLinearEquiv.toEquiv.subsingleton

/-- **Affine compact-support upper bound.** Let `C` be a smooth geometrically connected affine
curve over `k₀` and `F` a lisse Weil sheaf on `C`, punctually `ι`-pure of weight `w`. Then every
`H_c^r(C, F)` has weights at most `w + r`. More precisely, `H_c^0(C, F) = 0`, `H_c^2(C, F)` is
`ι`-pure of weight `w + 2`, and `H_c^r(C, F) = 0` for `r ∉ {0, 1, 2}`. The degree-one bound
comes from a finite morphism `C ⟶ 𝔸¹` and the estimate on dense opens of the line
(`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.hasWeightsAtMostOver_compactlySupportedCohomology`),
see `AlgebraicGeometry.hasWeightsAtMostOver_compactlySupportedCohomology_of_isAffine`. -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_of_isAffine_of_isLisse
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l C)
    (hF : F.IsLisse) {w : ℝ} (hw : F.IsPunctuallyPureOfWeight ι w) :
    haveI := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
    (∀ r : ℤ, (F.compactlySupportedCohomology r).HasWeightsAtMostOver k₀ ι (w + r)) ∧
      Subsingleton (F.compactlySupportedCohomology 0).carrier ∧
      (F.compactlySupportedCohomology 2).IsPureOfWeightOver k₀ ι (w + 2) ∧
      ∀ r : ℤ, r < 0 ∨ 2 < r → Subsingleton (F.compactlySupportedCohomology r).carrier := by
  have := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  exact ⟨hasWeightsAtMostOver_compactlySupportedCohomology_of_isAffine ι
      (ringKrullDim_le_of_smoothOfRelativeDimension (C ↘ Spec (CommRingCat.of k₀)) 1) F hw,
    WeilSheaf.subsingleton_compactlySupportedCohomology_of_isLisse_of_isAffine hF (Or.inl le_rfl),
    hw.isPureOfWeightOver_compactlySupportedCohomology_two hF,
    fun r hr ↦ WeilSheaf.subsingleton_compactlySupportedCohomology_of_isLisse_of_isAffine hF
      (hr.imp_left le_of_lt)⟩

end AlgebraicGeometry
