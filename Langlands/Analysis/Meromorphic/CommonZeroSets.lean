import Langlands.Analysis.Meromorphic.AnalyticSystems
import Langlands.Analysis.SeveralComplex.PointwiseSpan
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! # Common zero sets of holomorphic families on complex manifolds are analytic

Let `M` be a complex manifold modelled on a finite-dimensional complex normed space `E`. A set
`Z ⊆ M` is *locally a common zero set* (`IsLocallyCommonZeroSet`) when every point has an open
neighbourhood `W` and a family of functions holomorphic on `W`, indexed by an arbitrary type,
whose common zeros in `W` are exactly `Z ∩ W`. We show that such a set is analytic
(`IsLocallyCommonZeroSet.isAnalyticSubset`): finitely many members of the family suffice near
each point. This transfers `exists_finset_zero_iff` through charts. -/

noncomputable section
set_option autoImplicit false

universe w

namespace Langlands.Analysis.Meromorphic

open Set
open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- `Z ⊆ M` is locally the common zero set of a family of holomorphic functions: every point
has an open neighbourhood `W` and a family `f : Λ → M → ℂ` (with `Λ : Type w` arbitrary) of
functions holomorphic on `W` such that `Z ∩ W` is the set of common zeros of the `f l` in `W`. -/
def IsLocallyCommonZeroSet (Z : Set M) : Prop :=
  ∀ s₀ : M, ∃ W : Set M, IsOpen W ∧ s₀ ∈ W ∧ ∃ (Λ : Type w) (f : Λ → M → ℂ),
    (∀ l, MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (f l) W) ∧ Z ∩ W = {s ∈ W | ∀ l, f l s = 0}

variable [IsManifold 𝓘(ℂ, E) 1 M]

/-- **Finitely many members of a holomorphic family define its common zeros locally, on a
manifold.** For a family of functions holomorphic on an open set `W ⊆ M`, every `s₀ ∈ W` has an
open neighbourhood `V ⊆ W` and a finite set `t` of indices such that on `V` the common zeros of
the whole family are the common zeros of the members with indices in `t`. -/
theorem exists_finset_zero_iff_of_mdifferentiableOn {Λ : Type*} {W : Set M} (hW : IsOpen W)
    {f : Λ → M → ℂ} (hf : ∀ l, MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (f l) W) {s₀ : M}
    (hs₀ : s₀ ∈ W) :
    ∃ V ⊆ W, IsOpen V ∧ s₀ ∈ V ∧ ∃ t : Finset Λ,
      ∀ s ∈ V, (∀ l, f l s = 0) ↔ ∀ μ ∈ t, f μ s = 0 := by
  set φ := extChartAt 𝓘(ℂ, E) s₀ with hφdef
  set S := W ∩ φ.source with hSdef
  have hSsrc : S ⊆ φ.source := inter_subset_right
  have hS : IsOpen S := hW.inter (isOpen_extChartAt_source s₀)
  -- the chart image of `S` is open
  set T := φ.target ∩ φ.symm ⁻¹' S with hTdef
  have hT : IsOpen T :=
    (continuousOn_extChartAt_symm s₀).isOpen_inter_preimage (isOpen_extChartAt_target s₀) hS
  have hTimg : φ '' S = T := φ.image_eq_target_inter_inv_preimage hSsrc
  -- the family in coordinates
  have hfT : ∀ l, DifferentiableOn ℂ (f l ∘ φ.symm) T := by
    intro l
    have h := (mdifferentiableOn_iff_of_subset_source' (I := 𝓘(ℂ, E)) (I' := 𝓘(ℂ, ℂ))
      (x := s₀) (y := f l s₀) hSsrc (by
        intro s _
        rw [extChartAt_model_space_eq_id]
        exact mem_univ _)).1 ((hf l).mono inter_subset_left)
    rw [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp, hTimg] at h
    exact h
  have hs₀T : φ s₀ ∈ T := by
    rw [← hTimg]
    exact mem_image_of_mem _ ⟨hs₀, mem_extChartAt_source s₀⟩
  obtain ⟨V', hV'T, hV', hs₀V', t, ht⟩ :=
    Langlands.Analysis.SeveralComplex.exists_finset_zero_iff hT hfT hs₀T
  refine ⟨S ∩ φ ⁻¹' V', inter_subset_left.trans inter_subset_left,
    ((continuousOn_extChartAt s₀).mono hSsrc).isOpen_inter_preimage hS hV',
    ⟨⟨hs₀, mem_extChartAt_source s₀⟩, hs₀V'⟩, t, ?_⟩
  rintro s ⟨hsS, hsV'⟩
  have hinv : φ.symm (φ s) = s := φ.left_inv (hSsrc hsS)
  have := ht (φ s) hsV'
  simp only [Function.comp_apply, hinv] at this
  exact this

/-- **A locally common zero set of holomorphic families is analytic.** -/
theorem IsLocallyCommonZeroSet.isAnalyticSubset {Z : Set M}
    (hZ : IsLocallyCommonZeroSet.{w} (E := E) Z) : IsAnalyticSubset 𝓘(ℂ, E) Z := by
  intro s₀
  obtain ⟨W, hW, hs₀W, Λ, f, hf, hZW⟩ := hZ s₀
  obtain ⟨V, hVW, hV, hs₀V, t, ht⟩ := exists_finset_zero_iff_of_mdifferentiableOn hW hf hs₀W
  refine ⟨V, hV, hs₀V, t.card, fun j => f (t.equivFin.symm j), fun j => (hf _).mono hVW, ?_⟩
  ext s
  simp only [mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨hsZ, hsV⟩
    have : s ∈ Z ∩ W := ⟨hsZ, hVW hsV⟩
    rw [hZW] at this
    exact ⟨hsV, fun j => this.2 _⟩
  · rintro ⟨hsV, hs⟩
    refine ⟨?_, hsV⟩
    have hall : ∀ l, f l s = 0 := by
      refine (ht s hsV).2 fun μ hμ => ?_
      have := hs (t.equivFin ⟨μ, hμ⟩)
      simpa using this
    have : s ∈ Z ∩ W := by
      rw [hZW]
      exact ⟨hVW hsV, hall⟩
    exact this.1

end Langlands.Analysis.Meromorphic
