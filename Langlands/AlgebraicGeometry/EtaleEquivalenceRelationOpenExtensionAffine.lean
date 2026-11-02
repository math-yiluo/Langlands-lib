import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationOpenExtension

/-! # Affineness of the extension of a relation from an open -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.OpenExtension

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]

/-- The open complement of the identity arrows. -/
noncomputable def offDiagonalOpen : E.R.Opens :=
  ⟨(Set.range E.unit)ᶜ, E.unit.isClosedEmbedding.isClosed_range.isOpen_compl⟩

lemma offDiagonalOpen_isClosed : IsClosed ((offDiagonalOpen E) : Set E.R) :=
  E.unit.isOpenEmbedding.isOpen_range.isClosed_compl

instance offDiagonalOpen_isClosedImmersion : IsClosedImmersion (offDiagonalOpen E).ι :=
  IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact offDiagonalOpen_isClosed E)

instance offDiagonalOpen_isAffine [IsAffine E.R] : IsAffine (offDiagonalOpen E).toScheme :=
  isAffine_of_isAffineHom (offDiagonalOpen E).ι

lemma isCompl_unit_offDiagonal :
    IsCompl E.unit.opensRange (offDiagonalOpen E).ι.opensRange := by
  rw [Scheme.Opens.opensRange_ι]
  rw [isCompl_iff, disjoint_iff, codisjoint_iff]
  constructor <;> ext x <;> simp [offDiagonalOpen, Scheme.Hom.opensRange]

/-- The original arrow scheme is the coproduct of the identities and their complement. -/
noncomputable def offDiagonalCofanIsColimit :
    IsColimit (BinaryCofan.mk E.unit (offDiagonalOpen E).ι) :=
  (nonempty_isColimit_binaryCofanMk_of_isCompl E.unit (offDiagonalOpen E).ι
    (isCompl_unit_offDiagonal E)).some

variable {V : Scheme.{u}} (ι : E.U ⟶ V)

/-- Map the two old components to the enlarged identity component and the same complement. -/
noncomputable def toCoprod :
    E.R ⟶ V ⨿ (offDiagonalOpen E).toScheme :=
  (offDiagonalCofanIsColimit E).desc
    (BinaryCofan.mk (ι ≫ coprod.inl) coprod.inr)

@[reassoc (attr := simp)]
lemma unit_toCoprod : E.unit ≫ toCoprod E ι = ι ≫ coprod.inl :=
  (offDiagonalCofanIsColimit E).fac _ ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
lemma offDiagonal_toCoprod :
    (offDiagonalOpen E).ι ≫ toCoprod E ι = coprod.inr :=
  (offDiagonalCofanIsColimit E).fac _ ⟨WalkingPair.right⟩

variable [IsOpenImmersion ι]

/-- The extension replaces only the identity component of the old arrow scheme. -/
noncomputable def arrowsCoprodIso :
    arrows E ι ≅ V ⨿ (offDiagonalOpen E).toScheme where
  hom := pushout.desc coprod.inl (toCoprod E ι) (unit_toCoprod E ι).symm
  inv := coprod.desc (unit E ι) ((offDiagonalOpen E).ι ≫ inclusion E ι)
  hom_inv_id := by
    apply pushout.hom_ext
    · simp [pushout.inl_desc_assoc]
    · apply (offDiagonalCofanIsColimit E).hom_ext
      rintro ⟨j⟩
      cases j <;>
        simp [pushout.inr_desc_assoc, unit_inclusion]
  inv_hom_id := by
    apply coprod.hom_ext <;>
      simp [unit, inclusion, pushout.inl_desc, pushout.inr_desc]

instance arrows_isAffine [IsAffine V] [IsAffine E.R] : IsAffine (arrows E ι) :=
  IsAffine.of_isIso (arrowsCoprodIso E ι).hom

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.OpenExtension
