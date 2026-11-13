import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalRepresentationProperties
import Langlands.AlgebraicGeometry.PointTopology.FiniteAffineNeighborhoodsOpenShrinking
import Langlands.AlgebraicGeometry.FiniteAffineNeighborhoodsPushoutCharts

/-! # AF representations over a finite disjoint open cover of the base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace LocalRepresentation

variable {B U : Scheme.{u}} {F : Presheaf B}

/-- A base-change-stable property of the base chart `j` holds relatively for
the global chart of a representation after restriction along `j`. -/
theorem chart_relative (j : U ⟶ B) (H : Over U)
    (e : (schemeYoneda U).obj H ≅ (Over.map j).op ⋙ F)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] (hj : P j) :
    (P.inverseImage (Over.forget B)).relative (schemeYoneda B) (chart j H e) := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [← chartProductIso_hom_fst]
  exact (MorphismProperty.cancel_left_of_respectsIso
    ((P.inverseImage (Over.forget B)).relative (schemeYoneda B)) _ _).mpr
    (extProd.relative_fst P (Λ := Over.mk j) hj)

/-- A scheme covered by finitely many pairwise disjoint open subschemes, each
with the finite-set affine-neighborhood property, has that property. -/
theorem hasFiniteAffineNeighborhoods_of_disjoint_cover {X : Scheme.{u}} {ι : Type*} [Finite ι]
    {Y : ι → Scheme.{u}} (f : ∀ k, Y k ⟶ X) [∀ k, _root_.AlgebraicGeometry.IsOpenImmersion (f k)]
    (hcov : ∀ x, ∃ k, x ∈ Set.range (f k))
    (hdisj : Pairwise fun k l ↦ Disjoint (Set.range (f k)) (Set.range (f l)))
    (hY : ∀ k, PointTopology.HasFiniteAffineNeighborhoods (Y k)) :
    PointTopology.HasFiniteAffineNeighborhoods X := by
  intro s hs
  choose W hW using fun k ↦
    hY k ((f k) ⁻¹' s) (hs.preimage (f k).isOpenEmbedding.injective.injOn)
  let O : ι → X.Opens := fun k ↦ f k ''ᵁ (W k).1
  have hO : ∀ k, IsAffineOpen (O k) := fun k ↦
    (W k).2.image_of_isOpenImmersion (f k)
  have hOd : Pairwise (Function.onFun Disjoint O) := by
    intro k l hkl
    change Disjoint (O k) (O l)
    rw [← TopologicalSpace.Opens.coe_disjoint]
    refine (hdisj hkl).mono ?_ ?_
    · rintro _ ⟨y, -, rfl⟩
      exact ⟨y, rfl⟩
    · rintro _ ⟨y, -, rfl⟩
      exact ⟨y, rfl⟩
  refine ⟨⟨iSup O, IsAffineOpen.iSup_of_disjoint hO hOd⟩, ?_⟩
  intro x hx
  obtain ⟨k, y, rfl⟩ := hcov x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, ⟨y, hW k hx, rfl⟩⟩

/-- Over a finite base open cover with pairwise disjoint members, local
representatives with the finite-set affine-neighborhood property glue to a
global representative with that property. -/
theorem exists_representation_of_disjoint_cover
    (hF : Presheaf.IsSheaf (fppfTopology B) F)
    (𝒰 : Scheme.OpenCover.{u} B) [Finite 𝒰.I₀]
    (hdisj : Pairwise fun k l ↦ Disjoint (Set.range (𝒰.f k)) (Set.range (𝒰.f l)))
    (H : ∀ i, Over (𝒰.X i))
    (hH : ∀ i, PointTopology.HasFiniteAffineNeighborhoods (H i).left)
    (e : ∀ i, (schemeYoneda (𝒰.X i)).obj (H i) ≅ (Over.map (𝒰.f i)).op ⋙ F) :
    ∃ V : Over B, PointTopology.HasFiniteAffineNeighborhoods V.left ∧
      Nonempty ((schemeYoneda B).obj V ≅ F) := by
  obtain ⟨V, ⟨eV⟩⟩ := exists_representation hF 𝒰 H e
  refine ⟨V, ?_, ⟨eV⟩⟩
  refine hasFiniteAffineNeighborhoods_of_disjoint_cover
    (fun i ↦ Limits.pullback.fst V.hom (𝒰.f i)) ?_ ?_ ?_
  · intro x
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (V.hom x)
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    exact ⟨i, z, hz⟩
  · intro i k hik
    rw [Set.disjoint_iff_forall_ne]
    rintro _ ⟨z, rfl⟩ _ ⟨z', rfl⟩ h
    refine Set.disjoint_iff_forall_ne.mp (hdisj hik)
      ⟨Limits.pullback.snd V.hom (𝒰.f i) z, rfl⟩
      ⟨Limits.pullback.snd V.hom (𝒰.f k) z', rfl⟩ ?_
    rw [← Scheme.Hom.comp_apply, ← Limits.pullback.condition, Scheme.Hom.comp_apply, h,
      ← Scheme.Hom.comp_apply, Limits.pullback.condition, Scheme.Hom.comp_apply]
  · intro i
    exact FinitePinching.hasFiniteAffineNeighborhoods_of_iso
      ((Over.forget _).mapIso (localRepresentativeIso (𝒰.f i) V eV (H i) (e i))).symm (hH i)

end LocalRepresentation

end Langlands.AlgebraicGeometry.AlgebraicSpace
