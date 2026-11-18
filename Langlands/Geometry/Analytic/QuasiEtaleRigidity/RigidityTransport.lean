import Langlands.Geometry.Analytic.QuasiEtaleRigidity.StrongNearPostcomposition

/-! # Rigidity of morphisms over a compact set and its transport -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Rigidity of `p : U ⟶ X` over a set `L` of points of `U` (uniqueness in Berkovich's Key
Lemma 7.2 for morphisms into `L`): there is a finite set `E` of test triples on `U`, with
domains in `L`, such that two morphisms `ψ₁ ψ₂` with `ψ₁ ≫ p = ψ₂ ≫ p` which are both `E`-near
a common morphism `ψ` are equal, provided the three morphisms take values in `L`. -/
def IsRigidOn {U X : LocalizedCategory.{u, v, w} (K := K)} (p : U ⟶ X)
    (L : Set (localizedSpaceFunctor.obj U)) : Prop :=
  ∃ E : Finset (TestTriple (presentationOf U)), (∀ τ ∈ E, τ.locus ⊆ L) ∧
    ∀ (V : LocalizedCategory.{u, v, w} (K := K)) (ψ ψ₁ ψ₂ : V ⟶ U),
      Set.range (localizedSpaceFunctor.map ψ) ⊆ L →
      Set.range (localizedSpaceFunctor.map ψ₁) ⊆ L →
      Set.range (localizedSpaceFunctor.map ψ₂) ⊆ L → ψ₁ ≫ p = ψ₂ ≫ p →
        (∀ τ ∈ E, IsNear τ ψ ψ₁ ∧ IsNear τ ψ ψ₂) → ψ₁ = ψ₂

variable {U V₀ W X Y : LocalizedCategory.{u, v, w} (K := K)}

theorem TestTriple.isCompact_locus {B : SaturatedAtlasPresentation.{u, v, w} K}
    (τ : TestTriple B) : IsCompact τ.locus :=
  isCompact_range (B.presentation.atlas.isEmbedding_chart τ.domain).continuous

theorem range_map_comp_subset {Z : LocalizedCategory.{u, v, w} (K := K)} (ψ : Z ⟶ W)
    (j : W ⟶ Y) {L : Set (localizedSpaceFunctor.obj Y)}
    (h : Set.range (localizedSpaceFunctor.map ψ) ⊆ (localizedSpaceFunctor.map j) ⁻¹' L) :
    Set.range (localizedSpaceFunctor.map (ψ ≫ j)) ⊆ L := by
  rintro _ ⟨x, rfl⟩
  rw [Functor.map_comp, TopCat.comp_app]
  exact h ⟨x, rfl⟩

/-- Rigidity is inherited by `p` from `p ≫ h`. -/
theorem IsRigidOn.of_comp {p : U ⟶ X} {h : X ⟶ Y} {L : Set (localizedSpaceFunctor.obj U)}
    (hr : IsRigidOn (p ≫ h) L) : IsRigidOn p L := by
  obtain ⟨E, hEL, hE⟩ := hr
  exact ⟨E, hEL, fun V ψ ψ₁ ψ₂ h0 h1 h2 heq hn =>
    hE V ψ ψ₁ ψ₂ h0 h1 h2 (by rw [← Category.assoc, heq, Category.assoc]) hn⟩

/-- **Transport of rigidity along a monomorphism.** If `w` is rigid over `L` and preimages
under `j` of compact subsets of `L` are compact, then `j ≫ w` is rigid over `j⁻¹(L)`. -/
theorem IsRigidOn.precomp {j : V₀ ⟶ W} [Mono j] {w : W ⟶ Y}
    {L : Set (localizedSpaceFunctor.obj W)} (h : IsRigidOn w L)
    (hK : ∀ K' ⊆ L, IsCompact K' → IsCompact ((localizedSpaceFunctor.map j) ⁻¹' K')) :
    IsRigidOn (j ≫ w) ((localizedSpaceFunctor.map j) ⁻¹' L) := by
  classical
  obtain ⟨E, hEL, hE⟩ := h
  choose F hFloc hF using fun τ' : E =>
    exists_isNear_postcomp j τ'.1 (hK _ (hEL _ τ'.2) τ'.1.isCompact_locus)
  refine ⟨Finset.univ.biUnion F, ?_, ?_⟩
  · intro τ hτ
    obtain ⟨τ', -, hτ'⟩ := Finset.mem_biUnion.mp hτ
    exact (hFloc τ' τ hτ').trans (Set.preimage_mono (hEL _ τ'.2))
  · intro V ψ ψ₁ ψ₂ h0 h1 h2 heq hnear
    apply (cancel_mono j).1
    refine hE V (ψ ≫ j) (ψ₁ ≫ j) (ψ₂ ≫ j) (range_map_comp_subset ψ j h0)
      (range_map_comp_subset ψ₁ j h1) (range_map_comp_subset ψ₂ j h2)
      (by simp only [Category.assoc, heq]) fun τ' hτ' => ⟨?_, ?_⟩
    · exact hF ⟨τ', hτ'⟩ V ψ ψ₁ fun τ hτ =>
        (hnear τ (Finset.mem_biUnion.mpr ⟨⟨τ', hτ'⟩, Finset.mem_univ _, hτ⟩)).1
    · exact hF ⟨τ', hτ'⟩ V ψ ψ₂ fun τ hτ =>
        (hnear τ (Finset.mem_biUnion.mpr ⟨⟨τ', hτ'⟩, Finset.mem_univ _, hτ⟩)).2

/-- Rigidity transports along an isomorphism of the source. -/
theorem IsRigidOn.iso_comp {w : W ⟶ Y} {L : Set (localizedSpaceFunctor.obj W)}
    (h : IsRigidOn w L) (e : V₀ ≅ W) :
    IsRigidOn (e.hom ≫ w) ((localizedSpaceFunctor.map e.hom) ⁻¹' L) := by
  refine h.precomp fun K' _ hK' => ?_
  let h' : localizedSpaceFunctor.obj V₀ ≃ₜ localizedSpaceFunctor.obj W :=
    TopCat.homeoOfIso (localizedSpaceFunctor.mapIso e)
  exact h'.isCompact_preimage.mpr hK'

end Langlands.Analytic.SaturatedAtlasPresentation
