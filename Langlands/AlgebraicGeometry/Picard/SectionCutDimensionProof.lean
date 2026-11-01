import Langlands.AlgebraicGeometry.Picard.SectionCutDimensionStatement
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Dimension bounds for actual principal vanishing loci -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Order Opposite

namespace Langlands.AlgebraicGeometry.Picard

/-- A proper closed subset of an irreducible space has dimension at
most one less than the ambient dimension. -/
theorem topologicalKrullDim_add_one_le_of_isClosed
    {T : Type u} [TopologicalSpace T] [IrreducibleSpace T]
    (Z : Set T) (hZ : IsClosed Z) (hne : Z ≠ Set.univ) :
    topologicalKrullDim Z + 1 ≤ topologicalKrullDim T := by
  classical
  rcases isEmpty_or_nonempty (IrreducibleCloseds Z) with h | h
  · simp [topologicalKrullDim, Order.krullDim_eq_bot]
  · let F := IrreducibleCloseds.map (Subtype.val : Z → T) continuous_subtype_val
    let W : IrreducibleCloseds T :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ T, isClosed_univ⟩
    have hF : StrictMono F :=
      IrreducibleCloseds.map_strictMono_of_isInducing IsInducing.subtypeVal
    have hFW (A : IrreducibleCloseds Z) : F A < W := by
      have hsub : (F A : Set T) ⊆ Z :=
        closure_minimal (by rintro _ ⟨z, _, rfl⟩; exact z.2) hZ
      refine lt_of_le_of_ne (Set.subset_univ _) ?_
      intro he
      apply hne
      apply Set.Subset.antisymm (Set.subset_univ _)
      rw [← show (W : Set T) = Set.univ from rfl, ← he]
      exact hsub
    have hsm : StrictMono (WithTop.recTopCoe W F) :=
      WithTop.strictMono_iff.mpr ⟨hF, hFW⟩
    simpa only [topologicalKrullDim, Order.krullDim_WithTop] using
      (Order.krullDim_le_of_strictMono _ hsm)

/-- Pullback to a local spectrum computes the basic open of the germ. -/
theorem fromSpecStalk_preimage_basicOpen
    (X : Scheme.{u}) (x : X) (c : Γ(X, ⊤)) :
    (X.fromSpecStalk x) ⁻¹ᵁ X.basicOpen c =
      PrimeSpectrum.basicOpen (X.presheaf.germ ⊤ x trivial c) := by
  rw [Scheme.preimage_basicOpen_top, Scheme.fromSpecStalk_appTop]
  simp only [CommRingCat.comp_apply, Scheme.basicOpen_res,
    basicOpen_eq_of_affine]
  exact top_inf_eq _

/-- The spectrum of a principal local quotient embeds into the actual
vanishing locus, so its dimension is bounded by that locus. -/
theorem ringKrullDim_quotient_germ_le_vanishing
    (X : Scheme.{u}) (x : X) (c : Γ(X, ⊤)) :
    ringKrullDim (X.presheaf.stalk x ⧸
      Ideal.span {X.presheaf.germ ⊤ x trivial c}) ≤
        topologicalKrullDim {y : X // y ∉ X.basicOpen c} := by
  let I : Ideal (X.presheaf.stalk x) :=
    Ideal.span {X.presheaf.germ ⊤ x trivial c}
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let f := q ≫ X.fromSpecStalk x
  have hz : f ⁻¹ᵁ X.basicOpen c = ⊥ := by
    change q ⁻¹ᵁ ((X.fromSpecStalk x) ⁻¹ᵁ X.basicOpen c) = ⊥
    rw [fromSpecStalk_preimage_basicOpen, SpecMap_preimage_basicOpen]
    have hzero : Ideal.Quotient.mk I (X.presheaf.germ ⊤ x trivial c) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    change PrimeSpectrum.basicOpen
      (Ideal.Quotient.mk I (X.presheaf.germ ⊤ x trivial c)) = ⊥
    rw [hzero]
    exact PrimeSpectrum.basicOpen_zero
  have hr (y : Spec (CommRingCat.of (X.presheaf.stalk x ⧸ I))) :
      f y ∈ (X.basicOpen c : Set X)ᶜ := by
    intro hy
    have : y ∈ f ⁻¹ᵁ X.basicOpen c := hy
    rw [hz] at this
    exact this
  have hdim := (f.isEmbedding.isInducing.codRestrict hr).topologicalKrullDim_le
  change topologicalKrullDim (PrimeSpectrum (X.presheaf.stalk x ⧸ I)) ≤
    topologicalKrullDim {y : X // y ∉ X.basicOpen c} at hdim
  simpa only [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] using hdim

/-- The two dimension bounds for principal section cuts. -/
theorem sectionCutDimension : SectionCutDimensionStatement.{u} := by
  exact ⟨fun _ _ _ Z hZ hne => topologicalKrullDim_add_one_le_of_isClosed Z hZ hne,
    ringKrullDim_quotient_germ_le_vanishing⟩

end Langlands.AlgebraicGeometry.Picard
