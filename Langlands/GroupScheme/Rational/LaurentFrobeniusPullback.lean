import Langlands.GroupScheme.Rational.LaurentFrobeniusClosure

/-! # Finite Frobenius generators through an injective Laurent pullback -/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.LaurentAugmentation

variable {K : Type u} [Field K] {B : Type w} [CommRing B] [Algebra K B]
  {I : Type v} (σ : B →ₐ[K] AddMonoidAlgebra K (I → ℤ)) (N : Submodule K B)
  (hσ : ∀ f ∈ N, augmentation K (I → ℤ) (σ f) = 0)

/-- Restriction of a Laurent pullback to functions whose pullbacks vanish at the identity. -/
def pointedPullback : N →ₗ[K] space K (I → ℤ) :=
  (σ.toLinearMap.comp N.subtype).codRestrict _ (fun f => hσ f f.property)

@[simp] theorem pointedPullback_val (f : N) :
    (pointedPullback σ N hσ f).val = σ f := rfl

/-- The pointed generated algebra is the image of the original generated algebra. -/
theorem pointedAdjoin_pointedPullback (S : Set N) :
    pointedAdjoin K I (pointedPullback σ N hσ '' S) =
      (Algebra.adjoin K (Subtype.val '' S)).map σ := by
  rw [pointedAdjoin, ← Algebra.adjoin_image]
  congr 1
  rw [Set.image_image, Set.image_image]
  rfl

variable {p : ℕ} [Fact p.Prime] [CharP K p]

/-- A p-power-stable coordinate subspace has a Frobenius-stable pointed image. -/
theorem frobeniusMap_mem_range_pointedPullback
    (hN : ∀ f ∈ N, f ^ p ∈ N)
    {f : space K (I → ℤ)} (hf : f ∈ LinearMap.range (pointedPullback σ N hσ)) :
    frobeniusMap (k := K) (p := p) (I := I) f ∈
      LinearMap.range (pointedPullback σ N hσ) := by
  obtain ⟨g, rfl⟩ := hf
  refine ⟨⟨g.val ^ p, hN g.val g.property⟩, ?_⟩
  apply Subtype.ext
  simp

open Classical in
/-- A finite family in a p-power-stable coordinate subspace can be replaced
inside that subspace, preserving its generated algebra and giving independent
finite Laurent encodings. -/
theorem exists_finiteFrobGenerators_pullback
    (hinj : Function.Injective σ) (hN : ∀ f ∈ N, f ^ p ∈ N) (F : Finset N) :
    ∃ (s : Finset {m : I → ℤ // IsPrimitive p m}) (G : Finset N),
      frobSpan K p I (pointedPullback σ N hσ '' (F : Set N)) ≤
        finiteOrbitSpace K p I s ∧
      (pointedPullback σ N hσ '' (G : Set N)) ⊆
        frobSpan K p I (pointedPullback σ N hσ '' (F : Set N)) ∧
      frobSpan K p I (pointedPullback σ N hσ '' (F : Set N)) =
        frobSpan K p I (pointedPullback σ N hσ '' (G : Set N)) ∧
      Algebra.adjoin K (Subtype.val '' (F : Set N)) =
        Algebra.adjoin K (Subtype.val '' (G : Set N)) ∧
      TorusLinearization.FrobIndep
        (G.image (finiteEncoding K p I s ∘ pointedPullback σ N hσ)) := by
  classical
  let φ := pointedPullback σ N hσ
  obtain ⟨s, G', hs, hG', hspan, halg, hind⟩ :=
    exists_finiteFrobGenerators (p := p) (F.image φ)
  have hle : frobSpan K p I ((F.image φ : Finset _) : Set _) ≤ LinearMap.range φ := by
    apply frobSpan_le (fun _ hf => frobeniusMap_mem_range_pointedPullback σ N hσ hN hf)
    rw [Finset.coe_image]
    rintro _ ⟨f, _, rfl⟩
    exact LinearMap.mem_range_self φ f
  obtain ⟨G, _, hGG'⟩ : ∃ G : Finset N, (G : Set N) ⊆ Set.univ ∧ G.image φ = G' := by
    apply Finset.subset_set_image_iff.mp
    intro f hf
    obtain ⟨g, hg⟩ := hle (hG' hf)
    exact ⟨g, Set.mem_univ _, hg⟩
  refine ⟨s, G, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Finset.coe_image] using hs
  · rw [← Finset.coe_image, hGG']
    simpa only [Finset.coe_image] using hG'
  · rw [← Finset.coe_image, ← Finset.coe_image, hGG']
    exact hspan
  · apply Subalgebra.map_injective hinj
    rw [← pointedAdjoin_pointedPullback σ N hσ, ← pointedAdjoin_pointedPullback σ N hσ]
    change pointedAdjoin K I (φ '' (F : Set N)) = pointedAdjoin K I (φ '' (G : Set N))
    rw [← Finset.coe_image, ← Finset.coe_image, hGG']
    exact halg
  · rw [← Finset.image_image, hGG']
    exact hind

end Langlands.GroupScheme.LaurentAugmentation
