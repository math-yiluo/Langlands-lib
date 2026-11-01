import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Langlands.AlgebraicGeometry.Picard.GenericRationalSection
import Langlands.AlgebraicGeometry.Picard.GenericSectionSchematicClosureStatement
import Langlands.AlgebraicGeometry.Picard.UnramifiedGenericSectionExtensionStatement
import Langlands.AlgebraicGeometry.Picard.UnramifiedSections

/-! # Schematic closure of a generic section -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry

theorem toImage_schemeTheoreticallyDominant {Y X : Scheme.{u}} (f : Y ⟶ X)
    [QuasiCompact f] : IsSchemeTheoreticallyDominant f.toImage := by
  refine ⟨Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : X.affineOpens ↦ ⟨f.imageι ⁻¹ᵁ U.1, U.2.preimage f.imageι⟩) ?_
    (fun U ↦ ?_)⟩
  · rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top]
    simp
  · simp only [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (f.toImage_app_injective U)

theorem isIntegral_schematicImage {Y X : Scheme.{u}} (f : Y ⟶ X)
    [QuasiCompact f] [IsIntegral Y] : IsIntegral f.image := by
  let := toImage_schemeTheoreticallyDominant f
  let := IsSchemeTheoreticallyDominant.isReduced f.toImage
  have h : IsIrreducible (f.ker.support : Set X) := by
    rw [Scheme.Hom.support_ker, ← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ Y).image f f.continuous.continuousOn).closure
  let : IrreducibleSpace f.image := Subtype.irreducibleSpace h
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem birationalOver_of_genericSection {S X : Scheme.{u}}
    [IsIntegral S] [IsIntegral X] (p : X ⟶ S)
    [LocallyOfFiniteType p] [FormallyUnramified p]
    (a : Spec S.functionField ⟶ X)
    (ha : a ≫ p = S.fromSpecStalk (genericPoint S)) :
    Scheme.BirationalOver p (𝟙 S) := by
  let r := Scheme.PartialMap.ofFromSpecStalk (𝟙 S) p a (by simpa using ha)
  have hr : r.hom ≫ p = r.domain.ι := by
    simpa [r] using Scheme.PartialMap.ofFromSpecStalk_comp (𝟙 S) p a (by simpa using ha)
  have : IsOpenImmersion (r.hom ≫ p) := by rw [hr]; infer_instance
  have := isOpenImmersion_of_comp_of_unramified r.hom p
  have : IsDominant r.hom := ⟨by
    rw [DenseRange]
    apply r.hom.isOpenEmbedding.isOpen_range.dense
    obtain ⟨x, hx⟩ := r.dense_domain.nonempty
    exact ⟨_, ⟨⟨x, hx⟩, rfl⟩⟩⟩
  have : IsDominant r.domain.ι := Opens.isDominant_ι r.dense_domain
  exact (r.hom.birationalOver p r.domain.ι hr).symm.trans
    (r.domain.ι.birationalOver (𝟙 S) r.domain.ι (by simp))

theorem genericSection_image_birationalOver {S X : Scheme.{u}} [IsIntegral S]
    (p : X ⟶ S) [LocallyOfFiniteType p] [FormallyUnramified p]
    (a : Spec S.functionField ⟶ X)
    (ha : a ≫ p = S.fromSpecStalk (genericPoint S)) :
    IsIntegral a.image ∧ Scheme.BirationalOver (a.imageι ≫ p) (𝟙 S) := by
  have : QuasiCompact a := ⟨fun U _ _ ↦ (Set.toFinite _).isCompact⟩
  have := isIntegral_schematicImage a
  have : FormallyUnramified (a.imageι ≫ p) :=
    MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance inferInstance
  refine ⟨inferInstance, birationalOver_of_genericSection (a.imageι ≫ p) a.toImage ?_⟩
  simpa using ha

theorem genericSectionSchematicClosure : GenericSectionSchematicClosureStatement.{u} := by
  intro S X _ p _ _ a ha
  exact genericSection_image_birationalOver p a ha

end Langlands.AlgebraicGeometry
