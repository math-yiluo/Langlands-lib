import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationInvariantQuotientCoverDescent

/-! # Finite invariant affine covers from an étale scheme quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

/-- A finite invariant affine open cover with affine quotients on its charts. -/
structure InvariantAffineQuotientCover (E : EtaleEquivalenceRelation.{u}) where
  Index : Type u
  finite : Finite Index
  opens : Index → E.U.Opens
  isCover : IsOpenCover opens
  isAffine : ∀ k, IsAffineOpen (opens k)
  isInvariant : ∀ k, E.IsInvariantOpen (opens k)
  hasAffineQuotient : ∀ k, (E.chart (opens k).ι).HasAffineQuotient

variable (E : EtaleEquivalenceRelation.{u}) {M : Scheme.{u}} (f : E.U ⟶ M)
  (h : IsPullback E.t E.s f f)

include h in
/-- Inverse images of opens in a kernel-pair quotient are invariant. -/
lemma isInvariantOpen_preimage_of_kernelPair (V : M.Opens) :
    E.IsInvariantOpen (f ⁻¹ᵁ V) := by
  change E.s ⁻¹ᵁ (f ⁻¹ᵁ V) = E.t ⁻¹ᵁ (f ⁻¹ᵁ V)
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h.w]

include h in
/-- Restricting a kernel-pair quotient to an open gives the kernel pair of
the induced open-chart relation. -/
lemma isPullback_chart_morphismRestrict (V : M.Opens) :
    IsPullback (Chart.t E (f ⁻¹ᵁ V).ι) (Chart.s E (f ⁻¹ᵁ V).ι)
      (f ∣_ V) (f ∣_ V) := by
  refine IsPullback.mk' ?_ ?_ ?_
  · apply (cancel_mono V.ι).mp
    simp only [Category.assoc, morphismRestrict_ι]
    rw [← Chart.map_t_assoc, ← Chart.map_s_assoc, h.w]
  · intro T a b ht hs
    exact Chart.hom_ext E (f ⁻¹ᵁ V).ι ht hs
  · intro T a b hab
    have hab' : (a ≫ (f ⁻¹ᵁ V).ι) ≫ f = (b ≫ (f ⁻¹ᵁ V).ι) ≫ f := by
      simpa only [Category.assoc, morphismRestrict_ι] using
        congrArg (· ≫ V.ι) hab
    exact ⟨Chart.lift E (f ⁻¹ᵁ V).ι a b
      (h.lift (a ≫ (f ⁻¹ᵁ V).ι) (b ≫ (f ⁻¹ᵁ V).ι) hab')
      (h.lift_fst _ _ _) (h.lift_snd _ _ _), by simp, by simp⟩

/-- A morphism restricted to an open in its image is surjective onto that open. -/
lemma surjective_morphismRestrict_of_subset_range (V : M.Opens)
    (hV : (V : Set M) ⊆ Set.range f) : Surjective (f ∣_ V) := by
  constructor
  intro x
  obtain ⟨y, hy⟩ := hV x.property
  have hyV : y ∈ f ⁻¹ᵁ V := by
    change f y ∈ V
    rw [hy]
    exact x.property
  let z : (f ⁻¹ᵁ V).toScheme := ⟨y, hyV⟩
  refine ⟨z, ?_⟩
  apply V.ι.isEmbedding.injective
  change (f ∣_ V ≫ V.ι) z = x.val
  rw [morphismRestrict_ι]
  exact hy

include h in
/-- An affine open in the image of an étale kernel-pair quotient is an actual
affine quotient of the corresponding chart relation. -/
lemma hasAffineQuotient_chart_morphismRestrict [Etale f] (V : M.Opens)
    (hV : IsAffineOpen V) (hrange : (V : Set M) ⊆ Set.range f) :
    (E.chart (f ⁻¹ᵁ V).ι).HasAffineQuotient := by
  let : Etale (f ∣_ V) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f V).flip
      (inferInstanceAs (Etale f))
  have hflat : Flat (f ∣_ V) := inferInstance
  have hlfp : LocallyOfFinitePresentation (f ∣_ V) := inferInstance
  exact ⟨V.toScheme, f ∣_ V, hV, E.isPullback_chart_morphismRestrict f h V,
    hflat, hlfp, E.surjective_morphismRestrict_of_subset_range f V hrange⟩

/-- Choose a finite invariant affine cover by pulling back an affine cover of
a compact open image of an étale kernel-pair quotient. -/
def invariantAffineQuotientCoverOfCompactImage [IsAffine E.U] [IsAffine M] [Etale f]
    (W : M.Opens) (hW : IsCompact (W : Set M))
    (hrange : Set.range f = (W : Set M)) : E.InvariantAffineQuotientCover :=
  Classical.choice (by
    classical
    obtain ⟨Vs, hVs, hfinite, hsup⟩ := M.isBasis_affineOpens.exists_finite_of_isCompact hW
    let := hfinite.fintype
    have hcover : IsOpenCover (fun k : Vs => f ⁻¹ᵁ k.val) := by
      apply le_antisymm le_top
      intro x _
      have hxW : f x ∈ W := by
        change f x ∈ (W : Set M)
        rw [← hrange]
        exact ⟨x, rfl⟩
      rw [hsup] at hxW
      obtain ⟨V, hV, hxV⟩ := Opens.mem_sSup.mp hxW
      exact Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hxV⟩
    refine ⟨⟨Vs, inferInstance, (fun k => f ⁻¹ᵁ k.val), hcover,
      (fun k => (hVs k.property).preimage f),
      (fun k => E.isInvariantOpen_preimage_of_kernelPair f h k.val), ?_⟩⟩
    intro k
    apply E.hasAffineQuotient_chart_morphismRestrict f h k.val (hVs k.property)
    rw [hrange]
    change k.val ≤ W
    rw [hsup]
    exact le_sSup k.property)

namespace InvariantAffineQuotientCover

/-- Descend a supplied finite invariant affine quotient cover to one common
level of a cofiltered cartesian diagram. -/
def descend {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ EtaleEquivalenceRelation.{u}) (c : Cone D)
    [∀ i, IsAffine (D.obj i).U] [∀ i, IsAffine (D.obj i).R]
    (hc : IsLimit (objectFunctor.mapCone c)) (C : c.pt.InvariantAffineQuotientCover) :
    CartesianDiagram.InvariantAffineQuotientCoverModel D c C.opens := by
  letI := C.finite
  exact CartesianDiagram.invariantAffineQuotientCoverModel D c hc C.opens C.isCover
    C.isAffine C.isInvariant C.hasAffineQuotient

end InvariantAffineQuotientCover

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
