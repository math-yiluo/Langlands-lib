import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Langlands.AlgebraicGeometry.Picard.GenericSectionSchematicClosure
import Langlands.AlgebraicGeometry.Picard.BirationalUnramifiedOpenImmersionProof

/-! # Assembly of generic-section extension from the birational criterion -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry

theorem genericSectionImage_isIso_of_birationalOpenImmersion
    (hopen : BirationalUnramifiedOpenImmersionStatement.{u})
    {S X : Scheme.{u}} [IsIntegral S]
    (hS : GeometricallyUnibranchIntegralScheme S)
    (p : X ⟶ S) [IsSeparated p] [LocallyOfFiniteType p] [FormallyUnramified p]
    (hp : ClosedIrreducibleImages p)
    (a : Spec S.functionField ⟶ X)
    (ha : a ≫ p = S.fromSpecStalk (genericPoint S)) :
    IsIso (a.imageι ≫ p) := by
  have hcl := genericSection_image_birationalOver p a ha
  have : IsIntegral a.image := hcl.1
  let f := a.imageι ≫ p
  have : FormallyUnramified f :=
    MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance inferInstance
  have : IsOpenImmersion f := hopen S a.image hS f hcl.2
  have hclosed : IsClosed (Set.range f) := by
    change IsClosed (Set.range (a.imageι ≫ p))
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    apply hp _ a.imageι.isClosedEmbedding.isClosed_range
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ a.image).image _
      a.imageι.continuous.continuousOn
  have hη : genericPoint S ∈ Set.range f := by
    refine ⟨a.toImage (IsLocalRing.closedPoint S.functionField), ?_⟩
    change (a.toImage ≫ f) (IsLocalRing.closedPoint S.functionField) = _
    have heq : a.toImage ≫ f = S.fromSpecStalk (genericPoint S) := by
      simpa [f] using ha
    exact (congrArg (fun g : Spec S.functionField ⟶ S =>
      g (IsLocalRing.closedPoint S.functionField)) heq).trans
        (S.fromSpecStalk_closedPoint (x := genericPoint S))
  have hrange : Set.range f = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← genericPoint_closure S]
    exact closure_minimal (Set.singleton_subset_iff.mpr hη) hclosed
  have : Surjective f := ⟨Set.range_eq_univ.mp hrange⟩
  exact (isIso_iff_isOpenImmersion_and_surjective f).mpr ⟨inferInstance, inferInstance⟩

theorem unramifiedGenericSectionExtension_of_birationalOpenImmersion
    (hopen : BirationalUnramifiedOpenImmersionStatement.{u}) :
    UnramifiedGenericSectionExtensionStatement.{u} := by
  intro S X _ hS p _ _ _ hp sη
  let a := genericResidueFunctionFieldEquiv p sη
  have ha : a.val ≫ p = S.fromSpecStalk (genericPoint S) := by
    simpa using a.property
  let f := a.val.imageι ≫ p
  have : IsIso f :=
    genericSectionImage_isIso_of_birationalOpenImmersion hopen hS p hp a.val ha
  let s : S ⟶ X := inv f ≫ a.val.imageι
  have hs : s ≫ p = 𝟙 S := by
    change inv f ≫ a.val.imageι ≫ p = 𝟙 S
    exact IsIso.inv_hom_id f
  refine ⟨⟨s, hs⟩, ?_⟩
  apply (genericResidueFunctionFieldEquiv p).injective
  apply Subtype.ext
  have hgen : S.fromSpecStalk (genericPoint S) ≫ s = a.val := by
    calc
      _ = (a.val ≫ p) ≫ s := congrArg (fun k => k ≫ s) ha.symm
      _ = a.val.toImage ≫ (f ≫ inv f) ≫ a.val.imageι := by
        simp only [s, f, ← Category.assoc, Scheme.Hom.toImage_imageι]
      _ = a.val := by simp
  have := isIso_genericPoint_residue S
  change inv (Spec.map (S.residue (genericPoint S))) ≫
    (S.fromSpecResidueField (genericPoint S) ≫ s) = a.val
  rw [Scheme.fromSpecResidueField, ← Category.assoc, IsIso.inv_hom_id_assoc]
  exact hgen

theorem unramifiedGenericSectionExtension :
    UnramifiedGenericSectionExtensionStatement.{u} :=
  unramifiedGenericSectionExtension_of_birationalOpenImmersion
    birationalUnramifiedOpenImmersion

end Langlands.AlgebraicGeometry
